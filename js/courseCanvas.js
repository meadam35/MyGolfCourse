// SimGolf course canvas. Draws the isometric map and forwards pointer input to C#.
// JS owns the camera (pan and zoom), the projection, and picking the tile and corner
// under the pointer. C# owns the rules: what a click means, what it costs, and what changes.
(function () {
    const TILE_W = 64;       // diamond width in world pixels
    const TILE_H = 32;       // diamond height: 2:1 isometric
    const LEVEL_H = 6;       // screen pixels per height step: a quarter of a metre
    const WALL_LIGHT = 0.62; // cliff face that faces right, as a share of the tile colour
    const WALL_DARK = 0.42;  // cliff face that faces left
    const SLOPE_SHADE = 0.25;         // how steeply a height change tilts a tile's surface
    const SLOPE_LIGHT_STRENGTH = 1.5; // how strongly a tilt changes the light on it
    const PATH_WIDTH = 5;            // width of a cart path, in world pixels
    const MIN_ZOOM = 0.2;
    const START_ZOOM = 0.5;  // a whole course rarely fits the panel at 100%
    const MAX_ZOOM = 3;

    const sprites = new Map();   // sprite path -> Image

    let canvas = null;
    let ctx = null;
    let dotNet = null;
    let terrains = {};           // terrain id -> { id, name, cost, color, sprite }
    let map = null;              // { width, height, tiles, heights, holes }
    let maxAbsHeight = 0;
    let camera = { x: 0, y: 0, zoom: 1 };
    let cameraCentred = false;
    let hover = null;            // { tile: {x, y}, corner: {x, y} } or null
    let pointer = null;          // { button, lastX, lastY, last }
    let buildingDefs = {};       // building id -> { id, name, color, pieces: { "1": path, "2": path } }
    let pendingSet = new Set();  // "x,y" keys of tiles marked for a footprint
    let golfers = [];            // { id, x, y } in tile coordinates, from the course simulation
    let balls = [];              // { x, y, inFlight, progress, flightTiles } for each golfer's ball
    let popupTile = null;        // tile the hole details popup hangs from, or null
    let rotation = 0;            // quarter turns of the view, 0 to 3, clockwise
    const GOLFER_SCALE = 1.0;    // size of a golfer figure, in world pixels per drawing unit
    // Which way a golfer's facing (grid +x) points on screen, for each quarter turn of the view.
    const FACING_SIGN = [1, -1, -1, 1];

    // ---- heights and corners ---------------------------------------------

    // Height in steps of tile corner (gx, gy). Corners run 0..width and 0..height.
    function heightOf(gx, gy) {
        return map.heights[gy * (map.width + 1) + gx];
    }

    // A grid point turned by the view rotation, around the centre of the map.
    function rotatePoint(gx, gy) {
        const cx = map.width / 2;
        const cy = map.height / 2;
        let dx = gx - cx;
        let dy = gy - cy;
        for (let i = 0; i < rotation; i++) {
            const t = dx;
            dx = -dy;
            dy = t;
        }
        return { x: cx + dx, y: cy + dy };
    }

    // How near a grid point is to the viewer in this view. Larger is nearer.
    function depthOf(gx, gy) {
        const p = rotatePoint(gx, gy);
        return p.x + p.y;
    }

    // The same corner with no height applied. Used for the ground line under walls.
    function flatPoint(gx, gy) {
        const p = rotatePoint(gx, gy);
        return { x: (p.x - p.y) * TILE_W / 2, y: (p.x + p.y) * TILE_H / 2 };
    }

    // Screen-world position of a corner, lifted by its height.
    function cornerPoint(gx, gy) {
        const p = flatPoint(gx, gy);
        return { x: p.x, y: p.y - heightOf(gx, gy) * LEVEL_H };
    }

    // Corners of tile (x, y) in order: top, right, bottom, left.
    function tileCorners(x, y) {
        return [
            { gx: x, gy: y },
            { gx: x + 1, gy: y },
            { gx: x + 1, gy: y + 1 },
            { gx: x, gy: y + 1 },
        ].map((c) => {
            const p = cornerPoint(c.gx, c.gy);
            return { gx: c.gx, gy: c.gy, x: p.x, y: p.y };
        });
    }

    function averageHeight(x, y) {
        return (heightOf(x, y) + heightOf(x + 1, y) + heightOf(x + 1, y + 1) + heightOf(x, y + 1)) / 4;
    }

    // Centre of a tile on screen-world space. Used for markers and sprites.
    function tileCentre(x, y) {
        const p = flatPoint(x + 0.5, y + 0.5);
        return { x: p.x, y: p.y - averageHeight(x, y) * LEVEL_H };
    }

    // Order a tile is drawn in, and picked in: its farthest corner's depth. Tiles behind come first.
    function tileKey(x, y) {
        return Math.min(depthOf(x, y), depthOf(x + 1, y), depthOf(x + 1, y + 1), depthOf(x, y + 1));
    }

    // ---- picking ----------------------------------------------------------

    function screenToWorld(sx, sy) {
        const rect = canvas.getBoundingClientRect();
        return {
            x: (sx - rect.width / 2) / camera.zoom + camera.x,
            y: (sy - rect.height / 2) / camera.zoom + camera.y,
        };
    }

    // Tile under a world point ignoring heights. A starting guess for the real search.
    function flatTile(wx, wy) {
        const a = wx / (TILE_W / 2);  // rotated x - y
        const b = wy / (TILE_H / 2);  // rotated x + y
        // Undo the view rotation about the map centre, one quarter turn at a time.
        const cx = map.width / 2;
        const cy = map.height / 2;
        let dx = (a + b) / 2 - cx;
        let dy = (b - a) / 2 - cy;
        for (let i = 0; i < rotation; i++) {
            const t = dx;
            dx = dy;
            dy = -t;
        }
        return { x: Math.floor(cx + dx), y: Math.floor(cy + dy) };
    }

    // True when the point lies inside the convex quad given by its four corners.
    function containsPoint(pts, px, py) {
        let pos = false;
        let neg = false;
        for (let i = 0; i < 4; i++) {
            const a = pts[i];
            const b = pts[(i + 1) % 4];
            const cross = (b.x - a.x) * (py - a.y) - (b.y - a.y) * (px - a.x);
            if (cross > 0) pos = true;
            else if (cross < 0) neg = true;
            if (pos && neg) return false;
        }
        return true;
    }

    // The tile drawn on top at this world point, using the raised corners.
    function pickTile(wx, wy) {
        const approx = flatTile(wx, wy);
        const r = maxAbsHeight + 2;
        let best = null;
        for (let dy = -r; dy <= r; dy++) {
            for (let dx = -r; dx <= r; dx++) {
                const x = approx.x + dx;
                const y = approx.y + dy;
                if (x < 0 || y < 0 || x >= map.width || y >= map.height) continue;
                if (best && tileKey(x, y) <= tileKey(best.x, best.y)) continue;
                if (containsPoint(tileCorners(x, y), wx, wy)) best = { x, y };
            }
        }
        return best;
    }

    // The corner of this tile closest to the world point.
    function nearestCorner(tile, wx, wy) {
        let best = null;
        let bestDistance = Infinity;
        for (const c of tileCorners(tile.x, tile.y)) {
            const d = (c.x - wx) * (c.x - wx) + (c.y - wy) * (c.y - wy);
            if (d < bestDistance) {
                bestDistance = d;
                best = { x: c.gx, y: c.gy };
            }
        }
        return best;
    }

    // Tile and nearest corner under a canvas point, or null when off the course.
    function locate(sx, sy) {
        if (!map) return null;
        const w = screenToWorld(sx, sy);
        const tile = pickTile(w.x, w.y);
        if (!tile) return null;
        return { tile, corner: nearestCorner(tile, w.x, w.y) };
    }

    function sameLocation(a, b) {
        if (a === b) return true;
        if (!a || !b) return false;
        return a.tile.x === b.tile.x && a.tile.y === b.tile.y
            && a.corner.x === b.corner.x && a.corner.y === b.corner.y;
    }

    function insideCanvas(sx, sy) {
        const rect = canvas.getBoundingClientRect();
        return sx >= 0 && sy >= 0 && sx <= rect.width && sy <= rect.height;
    }

    // ---- drawing ----------------------------------------------------------

    function tracePath(pts) {
        ctx.beginPath();
        ctx.moveTo(pts[0].x, pts[0].y);
        for (let i = 1; i < pts.length; i++) ctx.lineTo(pts[i].x, pts[i].y);
        ctx.closePath();
    }

    // Darkens a #rrggbb colour by a factor from 0 to 1.
    function shade(hex, factor) {
        const n = parseInt(hex.slice(1), 16);
        const r = Math.round(((n >> 16) & 255) * factor);
        const g = Math.round(((n >> 8) & 255) * factor);
        const b = Math.round((n & 255) * factor);
        return `rgb(${r}, ${g}, ${b})`;
    }

    // A cliff face from corner a to corner b, dropping to ground level.
    function drawWall(a, b, color) {
        if (heightOf(a.gx, a.gy) <= 0 && heightOf(b.gx, b.gy) <= 0) return;
        const fa = flatPoint(a.gx, a.gy);
        const fb = flatPoint(b.gx, b.gy);
        tracePath([a, b, fb, fa]);
        ctx.fillStyle = color;
        ctx.fill();

        // A light lip along the top of the cliff, so each step reads as an edge.
        ctx.beginPath();
        ctx.moveTo(a.x, a.y);
        ctx.lineTo(b.x, b.y);
        ctx.strokeStyle = "rgba(255, 255, 255, 0.35)";
        ctx.lineWidth = 1;
        ctx.stroke();
    }

    // Cliff faces on the two edges that face the viewer: the ones that meet the corner nearest the viewer.
    // The edge going right on screen is lit, and the one going left is in shadow.
    function drawTileWalls(corners, color) {
        let near = 0;
        for (let i = 1; i < 4; i++) {
            const c = corners[i];
            const n = corners[near];
            if (depthOf(c.gx, c.gy) > depthOf(n.gx, n.gy)) near = i;
        }
        const pivot = corners[near];
        for (const [a, b] of [[corners[(near + 3) % 4], pivot], [pivot, corners[(near + 1) % 4]]]) {
            const midX = (a.x + b.x) / 2;
            drawWall(a, b, shade(color, midX > pivot.x ? WALL_LIGHT : WALL_DARK));
        }
    }

    // Mixes a #rrggbb colour toward white by a fraction from 0 to 1.
    function mix(hex, t) {
        const n = parseInt(hex.slice(1), 16);
        const lift = (v) => Math.round(v + (255 - v) * t);
        return `rgb(${lift((n >> 16) & 255)}, ${lift((n >> 8) & 255)}, ${lift(n & 255)})`;
    }

    // Brightens or darkens a colour by a factor: below 1 is darker, above 1 is lighter.
    function adjust(hex, factor) {
        return factor < 1 ? shade(hex, factor) : mix(hex, Math.min(1, factor - 1));
    }

    // Light comes from the upper left of the screen, in view coordinates, so it stays put as the view turns.
    const LIGHT = (() => {
        const v = [-1, -0.4, 1];
        const len = Math.hypot(v[0], v[1], v[2]);
        return v.map((c) => c / len);
    })();

    // Slopes facing the light are lit and slopes facing away are shaded, so terrain changes read at a glance.
    function slopeFactor(x, y) {
        let gx = ((heightOf(x + 1, y) + heightOf(x + 1, y + 1)) - (heightOf(x, y) + heightOf(x, y + 1))) / 2;
        let gy = ((heightOf(x, y + 1) + heightOf(x + 1, y + 1)) - (heightOf(x, y) + heightOf(x + 1, y))) / 2;
        for (let i = 0; i < rotation; i++) {
            const t = gx;
            gx = -gy;
            gy = t;
        }
        const nx = -gx * SLOPE_SHADE;
        const ny = -gy * SLOPE_SHADE;
        const len = Math.hypot(nx, ny, 1);
        const lit = (nx * LIGHT[0] + ny * LIGHT[1] + LIGHT[2]) / len;
        const flat = LIGHT[2];
        return 1 + Math.max(-0.4, Math.min(0.3, (lit - flat) * SLOPE_LIGHT_STRENGTH));
    }

    // The colour of a tile's top: its terrain colour, lifted when the tile is high, and lit or shaded by its slope.
    function surfaceColour(hex, x, y, height) {
        const heightFactor = 1 + Math.max(-0.3, Math.min(0.3, height * 0.06));
        return adjust(hex, heightFactor * slopeFactor(x, y));
    }

    function spriteFor(terrain) {
        if (!terrain || !terrain.sprite) return null;
        let img = sprites.get(terrain.sprite);
        if (!img) {
            img = new Image();
            img.onload = () => draw();
            img.src = new URL(terrain.sprite, document.baseURI).href;
            sprites.set(terrain.sprite, img);
        }
        return img;
    }

    function drawTile(x, y, terrainId, groundId) {
        const terrain = terrains[terrainId];
        // A cart path sits on the ground beneath it, so the ground's colour, texture, and sprite still show.
        const isPath = !!(terrain && terrain.isPath);
        const surface = isPath ? (terrains[groundId] || terrain) : terrain;
        const color = surface ? surface.color : "#ff00ff";
        const corners = tileCorners(x, y);

        // Cliff faces on the two front edges. Tiles drawn later cover them where they should.
        drawTileWalls(corners, color);

        const img = spriteFor(surface);
        if (img && img.complete && img.naturalWidth > 0) {
            // Sprite art is as wide as the diamond. Its bottom edge sits on the bottom of the tile,
            // so tall art such as trees rises above its tile.
            const centre = tileCentre(x, y);
            const h = img.naturalHeight * TILE_W / img.naturalWidth;
            ctx.drawImage(img, centre.x - TILE_W / 2, centre.y + TILE_H / 2 - h, TILE_W, h);
            return;
        }

        tracePath(corners);
        ctx.fillStyle = surfaceColour(color, x, y, averageHeight(x, y));
        ctx.fill();
        if (surface && surface.texture && surface.texture !== "none") drawTileTexture(surface.texture, corners, x, y);
        if (surface && GRASS_TEXTURES.has(surface.texture)) drawWindSheen(corners, x, y);
        ctx.strokeStyle = "rgba(0, 0, 0, 0.18)";
        ctx.lineWidth = 0.5;
        ctx.stroke();

        // The path itself is drawn over the ground, in its own colour.
        if (isPath) drawPathShape(x, y, terrain.color);
        if (terrainId === map.teeTerrain) drawTeeBalls(x, y);
    }

    // Marks a tile that is part of the footprint being planned.
    function overlayTile(x, y) {
        tracePath(tileCorners(x, y));
        ctx.fillStyle = "rgba(255, 230, 120, 0.35)";
        ctx.fill();
    }

    // Buildings sorted by the depth of their front tile, so tiles in front cover them.
    // Placed buildings are solid, and the pending footprint preview is faint.
    function pieceItems() {
        const items = [];
        const add = (piece, alpha) => {
            let key = -Infinity;
            for (let j = 0; j < piece.size; j++) {
                for (let i = 0; i < piece.size; i++) key = Math.max(key, tileKey(piece.x + i, piece.y + j));
            }
            items.push({ key, rank: 1, piece, alpha });
        };
        for (const p of map.buildings || []) add(p, 1);
        for (const p of map.pendingPieces || []) add(p, 0.6);
        return items;
    }

    // One building square: its art spans the square's width and sits on its bottom corner.
    function drawPiece(piece, alpha) {
        const def = buildingDefs[piece.buildingId];
        const s = piece.size;
        const bottom = cornerPoint(piece.x + s, piece.y + s);
        const width = s * TILE_W;
        const img = def && def.pieces ? spriteFor({ sprite: def.pieces[String(s)] }) : null;

        ctx.globalAlpha = alpha;
        if (img && img.complete && img.naturalWidth > 0) {
            const h = img.naturalHeight * width / img.naturalWidth;
            ctx.drawImage(img, bottom.x - width / 2, bottom.y - h, width, h);
        } else {
            // Placeholder until the art exists: a flat square in the building's colour.
            tracePath([
                cornerPoint(piece.x, piece.y),
                cornerPoint(piece.x + s, piece.y),
                cornerPoint(piece.x + s, piece.y + s),
                cornerPoint(piece.x, piece.y + s),
            ]);
            ctx.fillStyle = def ? def.color : "#ff00ff";
            ctx.fill();
            ctx.strokeStyle = "rgba(0, 0, 0, 0.4)";
            ctx.lineWidth = 1;
            ctx.stroke();
        }
        ctx.globalAlpha = 1;
    }

    // Golfers sorted by the depth of their tile, so nearer tiles and buildings cover them correctly.
    // A small speckled grain, drawn once and repeated over every tile that uses it, so it stays cheap to draw.
    let sandPattern = null;
    function getSandPattern() {
        if (sandPattern) return sandPattern;
        const grain = document.createElement("canvas");
        grain.width = 64;
        grain.height = 64;
        const g = grain.getContext("2d");
        for (let i = 0; i < 300; i++) {
            g.fillStyle = i % 2 === 0 ? "rgba(0, 30, 8, 0.4)" : "rgba(200, 245, 130, 0.3)";
            g.fillRect((i * 37) % 64, (i * 53 + (i >> 3)) % 64, 1, 1);
        }
        sandPattern = ctx.createPattern(grain, "repeat");
        return sandPattern;
    }

    // A point on a tile at (u, v), from 0 to 1 across each of its two sides. Corners are top, right, bottom, left.
    function tilePoint(corners, u, v) {
        const [top, right, , left] = corners;
        return { x: top.x + u * (right.x - top.x) + v * (left.x - top.x), y: top.y + u * (right.y - top.y) + v * (left.y - top.y) };
    }

    // Draws a surface pattern over a tile, clipped to its diamond. Sandpaper is a fine speckled grain, and mowing stripes
    // are light bands across the tile. Each name in terrain.json's textures list needs a case here.
    // A deterministic pseudo-random number from 0 to 1 for a tile and a slot, so a tile's ripples keep their places.
    function tileHash(x, y, k) {
        let h = Math.imul(x, 73856093) ^ Math.imul(y, 19349663) ^ Math.imul(k + 1, 83492791);
        h = Math.imul(h ^ (h >>> 13), 1274126177);
        return ((h ^ (h >>> 16)) >>> 0) / 4294967295;
    }

    function drawTileTexture(texture, corners, x, y) {
        if (texture === "waves") {
            // Short ripples that brighten and fade on their own timing. They follow the game clock, so they stop when paused.
            ctx.lineWidth = 1.3;
            ctx.lineCap = "round";
            drawWaterSwell(corners, x, y);
            drawShoreFoam(corners, x, y);
            drawWaterGlints(corners, x, y);

            // In wind, ripples come quicker, stand taller, and sway downwind.
            const wind = windOnScreen();
            const choppy = 1 + wind.strength * 1.5;
            for (let k = 0; k < 3; k++) {
                const p = tilePoint(corners, 0.2 + 0.6 * tileHash(x, y, k * 2), 0.2 + 0.6 * tileHash(x, y, k * 2 + 1));
                const phase = (animClock / 1000) * 1.2 * choppy + tileHash(x, y, k + 10) * Math.PI * 2;
                const alpha = 0.25 + 0.4 * (0.5 + 0.5 * Math.sin(phase));
                const drift = Math.sin(phase * 0.5) * 2 * wind.strength;
                const px = p.x + wind.x * drift;
                const py = p.y + wind.y * drift;
                ctx.strokeStyle = `rgba(235, 248, 255, ${alpha.toFixed(3)})`;
                ctx.beginPath();
                ctx.moveTo(px - 6, py);
                ctx.quadraticCurveTo(px, py - 2.5 * choppy, px + 6, py);
                ctx.stroke();
            }
            if (shown.rain > 0.02) drawRainRings(corners, x, y);
            return;
        }

        ctx.save();
        tracePath(corners);
        ctx.clip();
        if (texture === "sandpaper") {
            ctx.fillStyle = getSandPattern();
            tracePath(corners);
            ctx.fill();
        } else if (texture === "mowStripes") {
            ctx.fillStyle = "rgba(255, 255, 255, 0.07)";
            for (let s = 0; s < 4; s++) {
                const u0 = s / 4;
                const u1 = u0 + 0.125;
                const pts = [tilePoint(corners, u0, 0), tilePoint(corners, u1, 0), tilePoint(corners, u1, 1), tilePoint(corners, u0, 1)];
                ctx.beginPath();
                ctx.moveTo(pts[0].x, pts[0].y);
                for (let i = 1; i < 4; i++) ctx.lineTo(pts[i].x, pts[i].y);
                ctx.closePath();
                ctx.fill();
            }
        }
        ctx.restore();
    }

    // A tree standing on its tile: its art is drawn from the tile's centre, growing up from the ground.
    // Until the art loads, a plain trunk and canopy stand in for it.
    function drawTree(t) {
        const centre = tileCentre(t.x, t.y);
        const img = spriteFor({ sprite: t.sprite });
        const width = TILE_W * t.scale;
        const baseY = centre.y + TILE_H / 2;

        // Trees lean downwind and sway about their base. The top moves most, and the trunk stays planted.
        const wind = windOnScreen();
        const phase = (animClock / 1000) * (1.2 + wind.strength * 1.6) + tileHash(t.x, t.y, 7) * Math.PI * 2;
        const lean = wind.x * wind.strength * 0.08;
        const sway = Math.sin(phase) * (0.015 + wind.strength * 0.05);
        ctx.save();
        ctx.translate(centre.x, baseY);
        ctx.transform(1, 0, -(lean + sway), 1, 0, 0);
        if (img && img.complete && img.naturalWidth > 0) {
            const h = img.naturalHeight * width / img.naturalWidth;
            ctx.drawImage(img, -width / 2, -h, width, h);
        } else {
            const trunk = 6 * t.scale;
            fillRect(-trunk / 4, -trunk * 2, trunk / 2, trunk * 2, "#5d4037");
            fillEllipse(0, -trunk * 2.6, 9 * t.scale, 9 * t.scale, "#2e7d32");
        }
        ctx.restore();
    }

    // A ball on the course: a shadow on the ground, with the ball lifted into an arc while it is in the air.
    function drawBall(b) {
        const ix = Math.min(map.width - 1, Math.max(0, Math.floor(b.x)));
        const iy = Math.min(map.height - 1, Math.max(0, Math.floor(b.y)));
        const p = flatPoint(b.x, b.y);
        const groundY = p.y - averageHeight(ix, iy) * LEVEL_H;
        // The arc grows with the distance flown and peaks halfway through the flight.
        const arc = b.inFlight ? Math.sin(Math.PI * b.progress) * Math.min(60, 8 + b.flightTiles * 10) : 0;

        const r = 1.6;
        const by = groundY - arc;
        fillEllipse(p.x, groundY, 2, 1, "rgba(0, 0, 0, 0.4)");
        ctx.beginPath();
        ctx.arc(p.x, by, r, 0, Math.PI * 2);
        ctx.fillStyle = b.colour || "#ffffff";
        ctx.fill();
        ctx.strokeStyle = "rgba(0, 0, 0, 0.6)";
        ctx.lineWidth = 0.4;
        ctx.stroke();
        drawBallTexture(b.texture, p.x, by, r);
    }

    // Ball textures are drawn over the ball. Each name in ballTextures (appearance.json) needs a case here.
    // An unknown name draws a plain ball.
    function drawBallTexture(texture, x, y, r) {
        if (texture === "dimpled") {
            ctx.fillStyle = "rgba(0, 0, 0, 0.25)";
            for (const [dx, dy] of [[-0.5, -0.4], [0.4, -0.3], [0, 0.1], [-0.4, 0.5], [0.5, 0.4]]) {
                ctx.beginPath();
                ctx.arc(x + dx * r, y + dy * r, r * 0.2, 0, Math.PI * 2);
                ctx.fill();
            }
        } else if (texture === "striped") {
            ctx.save();
            ctx.beginPath();
            ctx.arc(x, y, r, 0, Math.PI * 2);
            ctx.clip();
            ctx.fillStyle = "rgba(0, 0, 0, 0.4)";
            ctx.fillRect(x - r, y - r * 0.15, r * 2, r * 0.3);
            ctx.restore();
        }
    }

    // Balls sorted by the depth of their ground tile, after the golfer on that tile.
    function ballItems() {
        return balls.map((b) => ({ key: Math.floor(depthOf(b.x, b.y)) + 0.5, rank: 3, ball: b }));
    }

    function golferItems() {
        return golfers.map((g) => ({ key: Math.floor(depthOf(g.x, g.y)) + 0.5, rank: 2, golfer: g }));
    }

    // Walk cycle speed, in radians per second of real time.
    const WALK_SPEED = 7;
    // Club angles in radians from straight down. Positive swings forward, in the direction the golfer faces.
    const BACKSWING = -2.2;
    const IMPACT = 0.9;
    const FOLLOW_THROUGH = 2.0;
    // Shoulder-to-hands length, and the club shaft beyond the hands.
    const ARM_LENGTH = 5.5;
    const CLUB_LENGTH = 7;

    function lerp(a, b, t) {
        return a + (b - a) * t;
    }

    // Swing progress from 0 to 1 maps to the club angle: back, through impact, then follow through.
    function swingAngle(progress) {
        const p = Math.min(1, Math.max(0, progress));
        if (p < 0.45) return lerp(0, BACKSWING, p / 0.45);
        if (p < 0.7) return lerp(BACKSWING, IMPACT, (p - 0.45) / 0.25);
        return lerp(IMPACT, FOLLOW_THROUGH, (p - 0.7) / 0.3);
    }

    // A golfer stands on the ground of the tile it is in. The figure is drawn from its appearance:
    // while walking, legs and arms swing and the body bobs; while swinging, the arms lift a club.
    function drawGolfer(g) {
        const ix = Math.min(map.width - 1, Math.max(0, Math.floor(g.x)));
        const iy = Math.min(map.height - 1, Math.max(0, Math.floor(g.y)));
        const p = flatPoint(g.x, g.y);
        const wx = p.x;
        const wy = p.y - averageHeight(ix, iy) * LEVEL_H;
        const a = g.appearance;

        const walking = g.pose === "walking";
        const swinging = g.pose === "swinging";
        const phase = (animClock / 1000) * WALK_SPEED + g.id * 1.7;
        const stride = walking ? Math.sin(phase) : 0;
        const bob = walking ? Math.abs(Math.cos(phase)) * 0.6 : 0;
        const legAngles = [stride * 0.45, -stride * 0.45];
        const armAngles = [-stride * 0.5, stride * 0.5];

        ctx.save();
        ctx.translate(wx, wy);
        ctx.scale(GOLFER_SCALE * g.facing * FACING_SIGN[rotation], GOLFER_SCALE);

        fillEllipse(0, 0.6, 4, 1.4, "rgba(0, 0, 0, 0.35)");

        // Legs swing from the hips, and each shoe stays on the end of its leg.
        [-1.6, 1.6].forEach((dx, i) => {
            ctx.save();
            ctx.translate(dx, -5.6);
            ctx.rotate(legAngles[i]);
            fillRect(-0.9, 0, 1.8, 4.1, a.trouserColour);
            fillRect(-1.1, 4.1, 2.2, 1.5, a.shoeColour);
            ctx.restore();
        });

        // The upper body, head included, bobs a little with each step.
        ctx.save();
        ctx.translate(0, -bob);
        fillRect(-3, -11.6, 6, 6.6, a.shirtColour);

        if (swinging) {
            drawSwingingArms(a, swingAngle(g.progress));
        } else {
            [-1, 1].forEach((side, i) => drawArm(a, side, armAngles[i]));
        }

        fillEllipse(0, -14, 3, 3, a.skinTone);
        drawHair(a);
        drawFace(a);

        ctx.restore();
        ctx.restore();
    }

    // One arm, from the shoulder down to the hand.
    function drawArm(a, side, angle) {
        const sx = side * 3.4;
        const sy = -10.6;
        const hx = sx + Math.sin(angle) * ARM_LENGTH;
        const hy = sy + Math.cos(angle) * ARM_LENGTH;
        strokeLine(sx, sy, hx, hy, a.shirtColour, 1.6);
        fillEllipse(hx, hy, 0.9, 0.9, a.skinTone);
    }

    // Both hands grip the club at the chest, and the club shaft and head point along the swing.
    function drawSwingingArms(a, angle) {
        const hx = Math.sin(angle) * 4.5;
        const hy = -9 + Math.cos(angle) * 4.5;
        [-1, 1].forEach((side) => strokeLine(side * 3.4, -10.6, hx, hy, a.shirtColour, 1.6));

        const tipX = hx + Math.sin(angle) * CLUB_LENGTH;
        const tipY = hy + Math.cos(angle) * CLUB_LENGTH;
        strokeLine(hx, hy, tipX, tipY, "#cfd8dc", 0.7);
        fillEllipse(tipX, tipY, 1.1, 0.7, "#37474f");
        fillEllipse(hx, hy, 0.9, 0.9, a.skinTone);
    }

    function fillRect(x, y, w, h, color) {
        ctx.fillStyle = color;
        ctx.fillRect(x, y, w, h);
    }

    function fillEllipse(cx, cy, rx, ry, color) {
        ctx.beginPath();
        ctx.ellipse(cx, cy, rx, ry, 0, 0, Math.PI * 2);
        ctx.fillStyle = color;
        ctx.fill();
    }

    function strokeLine(x1, y1, x2, y2, color, width) {
        ctx.beginPath();
        ctx.moveTo(x1, y1);
        ctx.lineTo(x2, y2);
        ctx.strokeStyle = color;
        ctx.lineWidth = width;
        ctx.stroke();
    }

    // Hair styles: short (a cap), long (a cap with sides), curly (bumps along the top), bald (none).
    function drawHair(a) {
        const c = a.hairColour;
        if (a.hairStyle === "bald") return;

        if (a.hairStyle === "curly") {
            for (let i = 0; i <= 6; i++) {
                const t = Math.PI + (Math.PI * i) / 6;
                fillEllipse(Math.cos(t) * 2.7, -14 + Math.sin(t) * 2.7, 1.1, 1.1, c);
            }
            return;
        }

        ctx.beginPath();
        ctx.ellipse(0, -14.2, 3.1, 2.2, 0, Math.PI, Math.PI * 2);
        ctx.fillStyle = c;
        ctx.fill();

        if (a.hairStyle === "long") {
            fillRect(-3.1, -14.2, 0.9, 5.2, c);
            fillRect(2.2, -14.2, 0.9, 5.2, c);
        }
    }

    // Eye, nose, and mouth styles, placed on the front of the head.
    function drawFace(a) {
        const ink = "#1b1b1b";
        const nose = shade(a.skinTone, 0.82);

        for (const ex of [-1.1, 1.1]) {
            if (a.eyeStyle === "round") {
                fillEllipse(ex, -14.4, 0.75, 0.85, "#ffffff");
                fillEllipse(ex, -14.4, 0.4, 0.45, ink);
            } else if (a.eyeStyle === "narrow") {
                strokeLine(ex - 0.5, -14.4, ex + 0.5, -14.4, ink, 0.45);
            } else {
                fillEllipse(ex, -14.4, 0.42, 0.42, ink);
            }
        }

        if (a.noseStyle === "big") fillEllipse(0, -13.1, 0.9, 0.7, nose);
        else if (a.noseStyle === "button") fillEllipse(0, -13.2, 0.55, 0.55, nose);
        else fillEllipse(0, -13.2, 0.35, 0.35, nose);

        if (a.mouthStyle === "grin") {
            ctx.beginPath();
            ctx.arc(0, -11.9, 1.1, 0, Math.PI);
            ctx.closePath();
            ctx.fillStyle = ink;
            ctx.fill();
        } else if (a.mouthStyle === "flat") {
            strokeLine(-0.7, -11.9, 0.7, -11.9, ink, 0.4);
        } else {
            ctx.beginPath();
            ctx.arc(0, -12.2, 1.0, 0.2 * Math.PI, 0.8 * Math.PI);
            ctx.strokeStyle = ink;
            ctx.lineWidth = 0.4;
            ctx.stroke();
        }
    }

    // Keeps the hole details popup beside the hole's tee as the view pans and zooms.
    // It hides when the tee is off screen, and it stays inside the map when it is near an edge.
    function positionPopup() {
        const el = document.getElementById("hole-popup");
        if (!el || !canvas) return;
        if (!map || !popupTile) {
            el.style.display = "none";
            return;
        }

        const rect = canvas.getBoundingClientRect();
        const c = tileCentre(popupTile.x, popupTile.y);
        const sx = (c.x - camera.x) * camera.zoom + rect.width / 2;
        const sy = (c.y - camera.y) * camera.zoom + rect.height / 2;
        if (sx < 0 || sy < 0 || sx > rect.width || sy > rect.height) {
            el.style.display = "none";
            return;
        }

        el.style.display = "block";
        const pw = el.offsetWidth;
        const ph = el.offsetHeight;
        const left = Math.min(Math.max(8, sx + 18), rect.width - pw - 8);
        const top = Math.min(Math.max(8, sy - ph - 12), rect.height - ph - 8);
        el.style.left = left + "px";
        el.style.top = top + "px";
    }

    // Golfers animate while any are on the course, so the canvas redraws on each animation frame.
    let animating = false;
    let lastAnimationDraw = 0;
    // The animation clock advances at the course speed, so a slow course also shows slow strides and swings.
    let animationSpeed = 1;
    let animClock = 0;           // milliseconds of animation time
    let lastAnimationTime = null;

    function startAnimation() {
        if (animating || !map) return;
        animating = true;
        requestAnimationFrame(animationFrame);
    }

    function setGolfers(list, speed, ballList, weatherView) {
        golfers = list || [];
        balls = ballList || [];
        animationSpeed = speed === undefined ? 1 : speed;
        if (weatherView) weather = weatherView;
        startAnimation();
    }

    // The canvas animates the whole time a map is shown: water, grass, trees, flags, and the weather all move.
    function animationFrame(time) {
        if (!map) {
            animating = false;
            lastAnimationTime = null;
            return;
        }
        const realDt = lastAnimationTime === null ? 0 : time - lastAnimationTime;
        animClock += realDt * animationSpeed;
        lastAnimationTime = time;
        easeWeather(realDt * animationSpeed);
        // About 30 redraws a second is smooth enough and keeps the map light.
        if (time - lastAnimationDraw >= 33) {
            lastAnimationDraw = time;
            draw();
        }
        requestAnimationFrame(animationFrame);
    }

    // ---- weather and wind --------------------------------------------------

    // The weather from C#: { id, name, rain, cloud, lightningPerMinute, windX, windY, windMax, minutesPerSecond }.
    // Rain, cloud, and lightning are drawing values from weather.json. Wind is in tile space, as the rules use it.
    let weather = { id: "", name: "", rain: 0, cloud: 0, lightningPerMinute: 0, windX: 0, windY: 0, windMax: 6, minutesPerSecond: 1 };
    // What is drawn eases toward the weather over a second or two, so a change of weather rolls in rather than snaps.
    const shown = { rain: 0, cloud: 0, windX: 0, windY: 0 };
    // Grass textures that ripple in the wind. Each is a texture name from terrain.json.
    const GRASS_TEXTURES = new Set(["sandpaper", "mowStripes"]);
    const WEATHER_EASE_MS = 1500;

    function easeWeather(dt) {
        const t = Math.min(1, dt / WEATHER_EASE_MS);
        shown.rain += (weather.rain - shown.rain) * t;
        shown.cloud += (weather.cloud - shown.cloud) * t;
        shown.windX += (weather.windX - shown.windX) * t;
        shown.windY += (weather.windY - shown.windY) * t;
    }

    // A tile-space direction turned by the view and projected, so it points the right way on screen.
    function tileDirOnScreen(dx, dy) {
        for (let i = 0; i < rotation; i++) {
            const t = dx;
            dx = -dy;
            dy = t;
        }
        return { x: (dx - dy) * TILE_W / 2, y: (dx + dy) * TILE_H / 2 };
    }

    // Wind strength from 0 (calm) to 1 (the strongest wind the course allows).
    function windStrength() {
        return Math.min(1, Math.hypot(shown.windX, shown.windY) / Math.max(0.001, weather.windMax));
    }

    // The wind as a unit direction on screen, with its strength.
    function windOnScreen() {
        const speed = Math.hypot(shown.windX, shown.windY);
        if (speed < 0.001) return { x: 0, y: 0, strength: 0, speed: 0 };
        const d = tileDirOnScreen(shown.windX, shown.windY);
        const len = Math.hypot(d.x, d.y) || 1;
        return { x: d.x / len, y: d.y / len, strength: windStrength(), speed };
    }

    // Gusts move across grass as soft bright bands, travelling downwind. Calm days barely shimmer.
    function drawWindSheen(corners, x, y) {
        const speed = Math.hypot(shown.windX, shown.windY);
        const strength = windStrength();
        const ux = speed > 0.001 ? shown.windX / speed : 1;
        const uy = speed > 0.001 ? shown.windY / speed : 0;
        const along = (x + 0.5) * ux + (y + 0.5) * uy;
        const across = -(x + 0.5) * uy + (y + 0.5) * ux;
        const t = animClock / 1000;
        const wave = Math.sin(along * 0.55 - t * (0.5 + strength * 2.2) + Math.sin(across * 0.3) * 1.2);
        const alpha = Math.pow(Math.max(0, wave), 3) * (0.03 + strength * 0.11);
        if (alpha < 0.005) return;
        tracePath(corners);
        ctx.fillStyle = `rgba(240, 255, 210, ${alpha.toFixed(3)})`;
        ctx.fill();
    }

    // True when the tile is water, or off the map, so shores only show where water meets land.
    function isWaterTile(x, y) {
        if (x < 0 || y < 0 || x >= map.width || y >= map.height) return true;
        const t = terrains[map.tiles[y * map.width + x]];
        return !!(t && t.texture === "waves");
    }

    // Swells roll across open water as light crests and dark troughs. They travel downwind, and still move in a calm.
    function drawWaterSwell(corners, x, y) {
        const speed = Math.hypot(shown.windX, shown.windY);
        const strength = windStrength();
        const ux = speed > 0.001 ? shown.windX / speed : 0.8;
        const uy = speed > 0.001 ? shown.windY / speed : 0.6;
        const along = (x + 0.5) * ux + (y + 0.5) * uy;
        const across = -(x + 0.5) * uy + (y + 0.5) * ux;
        const t = animClock / 1000;
        const wave = Math.sin(along * 1.1 - t * (1.1 + strength * 1.8) + Math.sin(across * 0.5 + t * 0.4) * 0.9);
        tracePath(corners);
        if (wave > 0) {
            ctx.fillStyle = `rgba(190, 225, 255, ${(wave * (0.1 + strength * 0.08)).toFixed(3)})`;
        } else {
            ctx.fillStyle = `rgba(0, 25, 70, ${(-wave * (0.12 + strength * 0.08)).toFixed(3)})`;
        }
        ctx.fill();
    }

    // Foam laps at the edges where water meets land: a pale line that washes in and out.
    // Edges run top-right (north), right-bottom (east), bottom-left (south), and left-top (west).
    function drawShoreFoam(corners, x, y) {
        const [top, right, bottom, left] = corners;
        const edges = [
            [top, right, x, y - 1],
            [right, bottom, x + 1, y],
            [bottom, left, x, y + 1],
            [left, top, x - 1, y],
        ];
        const centre = { x: (top.x + bottom.x) / 2, y: (top.y + bottom.y) / 2 };
        const t = animClock / 1000;
        ctx.lineCap = "round";
        edges.forEach(([a, b, nx, ny], i) => {
            if (isWaterTile(nx, ny)) return;
            const wash = 0.5 + 0.5 * Math.sin(t * 1.6 + tileHash(x, y, i + 70) * Math.PI * 2);
            const inset = 0.05 + wash * 0.12;
            const pa = { x: a.x + (centre.x - a.x) * inset, y: a.y + (centre.y - a.y) * inset };
            const pb = { x: b.x + (centre.x - b.x) * inset, y: b.y + (centre.y - b.y) * inset };
            ctx.strokeStyle = `rgba(240, 250, 255, ${(0.35 + 0.35 * (1 - wash)).toFixed(3)})`;
            ctx.lineWidth = 1.2 + (1 - wash) * 1.2;
            ctx.beginPath();
            ctx.moveTo(pa.x, pa.y);
            ctx.lineTo(pb.x, pb.y);
            ctx.stroke();
        });
    }

    // Sunlight glints off the water: brief bright sparkles, fewer under cloud and none in heavy overcast.
    function drawWaterGlints(corners, x, y) {
        const sun = 1 - Math.min(1, shown.cloud * 1.6);
        if (sun < 0.05) return;
        const t = animClock / 1000;
        for (let k = 0; k < 2; k++) {
            const pulse = Math.sin(t * (1.5 + tileHash(x, y, k + 80)) + tileHash(x, y, k + 90) * 40);
            const alpha = Math.pow(Math.max(0, pulse), 14) * sun;
            if (alpha < 0.03) continue;
            const p = tilePoint(corners, 0.2 + 0.6 * tileHash(x, y, k + 100), 0.2 + 0.6 * tileHash(x, y, k + 110));
            const r = 1 + alpha * 1.6;
            strokeLine(p.x - r * 1.6, p.y, p.x + r * 1.6, p.y, `rgba(255, 255, 240, ${alpha.toFixed(3)})`, 0.8);
            strokeLine(p.x, p.y - r, p.x, p.y + r, `rgba(255, 255, 240, ${alpha.toFixed(3)})`, 0.8);
        }
    }

    // Raindrops landing on water: small rings that spread and fade, each on its own timing and in a new place each time.
    function drawRainRings(corners, x, y) {
        const rings = shown.rain > 0.6 ? 3 : 2;
        ctx.lineWidth = 0.8;
        for (let k = 0; k < rings; k++) {
            const cycle = 0.9 + tileHash(x, y, k + 30) * 0.6;
            const run = (animClock / 1000) / cycle + tileHash(x, y, k + 40);
            const f = run % 1;
            const n = Math.floor(run);
            const p = tilePoint(corners, 0.15 + 0.7 * tileHash(x + n, y, k + 50), 0.15 + 0.7 * tileHash(x, y + n, k + 60));
            const alpha = (1 - f) * 0.6 * Math.min(1, shown.rain * 1.5);
            ctx.strokeStyle = `rgba(225, 240, 255, ${alpha.toFixed(3)})`;
            ctx.beginPath();
            ctx.ellipse(p.x, p.y, 1 + f * 5, 0.5 + f * 2.5, 0, 0, Math.PI * 2);
            ctx.stroke();
        }
    }

    // A hole's flag streams downwind and ripples. In a calm it hangs and barely moves.
    function drawFlag(px, py, seed) {
        const wind = windOnScreen();
        const side = wind.strength > 0.05 && wind.x < 0 ? -1 : 1;
        const len = 6 + wind.strength * 6;
        const droop = (1 - wind.strength) * 5;
        const t = (animClock / 1000) * (2 + wind.strength * 8) + seed;
        const wave = Math.sin(t) * (0.8 + wind.strength * 1.6);
        ctx.fillStyle = "#e53935";
        ctx.beginPath();
        ctx.moveTo(px, py);
        ctx.quadraticCurveTo(px + side * len * 0.5, py + droop * 0.5 + wave, px + side * len, py + droop + wave * 0.4 + 3);
        ctx.quadraticCurveTo(px + side * len * 0.5, py + 8 + droop * 0.5 - wave, px, py + 8);
        ctx.closePath();
        ctx.fill();
    }

    // Cloud shadows: soft dark patches that drift over the course with the wind. More cloud, darker shadows.
    const CLOUDS = Array.from({ length: 7 }, (_, i) => ({
        u: tileHash(i, 3, 1), v: tileHash(i, 5, 2), size: 4 + tileHash(i, 7, 3) * 6,
    }));

    function drawCloudShadows() {
        const alpha = shown.cloud * 0.22;
        if (alpha < 0.01) return;
        const t = animClock / 1000;
        const span = Math.max(map.width, map.height) + 20;
        // Clouds drift at least a little even on a still day.
        const driftX = shown.windX * 0.08 + 0.05;
        const driftY = shown.windY * 0.08;
        for (const c of CLOUDS) {
            const gx = ((c.u * span + driftX * t) % span + span) % span - 10;
            const gy = ((c.v * span + driftY * t) % span + span) % span - 10;
            const p = flatPoint(gx, gy);
            const rx = c.size * TILE_W / 2;
            const g = ctx.createRadialGradient(p.x, p.y, 0, p.x, p.y, rx);
            g.addColorStop(0, `rgba(10, 20, 35, ${alpha.toFixed(3)})`);
            g.addColorStop(1, "rgba(10, 20, 35, 0)");
            ctx.save();
            ctx.translate(p.x, p.y);
            ctx.scale(1, 0.5);
            ctx.translate(-p.x, -p.y);
            ctx.fillStyle = g;
            ctx.beginPath();
            ctx.arc(p.x, p.y, rx, 0, Math.PI * 2);
            ctx.fill();
            ctx.restore();
        }
    }

    // Overcast skies dim the whole view a little, toward a cool grey-blue.
    function drawSkyShade(w, h) {
        const alpha = shown.cloud * 0.3;
        if (alpha < 0.01) return;
        ctx.fillStyle = `rgba(25, 35, 55, ${alpha.toFixed(3)})`;
        ctx.fillRect(0, 0, w, h);
    }

    // Rain streaks fall across the screen, slanted by the wind. The same drops loop, so it costs the same every frame.
    const RAIN_DROPS = Array.from({ length: 600 }, (_, i) => ({
        x: tileHash(i, 11, 4), y: tileHash(i, 13, 5), speed: 0.8 + tileHash(i, 17, 6) * 0.5, len: 9 + tileHash(i, 19, 7) * 8,
    }));

    function drawRain(w, h) {
        const count = Math.round(RAIN_DROPS.length * shown.rain);
        if (count === 0) return;
        const wind = windOnScreen();
        const slant = wind.x * (0.15 + wind.strength * 0.6);
        const t = animClock / 1000;
        const wide = w + 200;
        ctx.strokeStyle = `rgba(200, 215, 235, ${(0.25 + shown.rain * 0.25).toFixed(3)})`;
        ctx.lineWidth = 1;
        ctx.lineCap = "round";
        ctx.beginPath();
        for (let i = 0; i < count; i++) {
            const d = RAIN_DROPS[i];
            const fall = h + d.len;
            const y = ((d.y * fall + t * 700 * d.speed) % fall) - d.len;
            const x = ((d.x * wide + slant * y) % wide + wide) % wide - 100;
            ctx.moveTo(x, y);
            ctx.lineTo(x + slant * d.len, y + d.len);
        }
        ctx.stroke();
    }

    // Lightning flashes at the weather's rate per game minute. A flash lights the whole view, and a bolt forks down.
    let nextFlashAt = null;   // animation clock time of the next flash
    let flash = null;         // { at, bolt: [{x, y}] } while a flash is showing
    const FLASH_MS = 450;

    function scheduleFlash() {
        const perMs = weather.lightningPerMinute * weather.minutesPerSecond / 1000;
        nextFlashAt = perMs > 0 ? animClock - Math.log(1 - Math.random()) / perMs : null;
    }

    function drawLightning(w, h) {
        if (weather.lightningPerMinute <= 0) {
            nextFlashAt = null;
        } else if (nextFlashAt === null) {
            scheduleFlash();
        } else if (animClock >= nextFlashAt) {
            const bolt = [];
            let x = w * (0.15 + Math.random() * 0.7);
            for (let y = 0; y < h * 0.7; y += 14 + Math.random() * 18) {
                bolt.push({ x, y });
                x += (Math.random() - 0.5) * 36;
            }
            flash = { at: animClock, bolt };
            scheduleFlash();
        }
        if (!flash) return;
        const age = animClock - flash.at;
        if (age > FLASH_MS || age < 0) {
            flash = null;
            return;
        }
        // Two quick pulses, then a fade.
        const f = 1 - age / FLASH_MS;
        const flicker = age < 90 ? 1 : age < 150 ? 0.3 : 0.8;
        ctx.fillStyle = `rgba(235, 240, 255, ${(0.4 * f * flicker).toFixed(3)})`;
        ctx.fillRect(0, 0, w, h);
        if (age < 220) {
            ctx.strokeStyle = `rgba(255, 255, 240, ${(0.95 * flicker).toFixed(3)})`;
            ctx.lineWidth = 2;
            ctx.lineJoin = "round";
            ctx.beginPath();
            flash.bolt.forEach((p, i) => (i === 0 ? ctx.moveTo(p.x, p.y) : ctx.lineTo(p.x, p.y)));
            ctx.stroke();
        }
    }

    // A small compass in the top right of the map: the arrow points the way the wind blows, as seen in this view.
    function drawWindCompass(w) {
        const cx = w - 34;
        const cy = 34;
        ctx.fillStyle = "rgba(13, 26, 18, 0.75)";
        ctx.strokeStyle = "rgba(255, 255, 255, 0.25)";
        ctx.lineWidth = 1;
        ctx.beginPath();
        ctx.arc(cx, cy, 22, 0, Math.PI * 2);
        ctx.fill();
        ctx.stroke();

        const wind = windOnScreen();
        ctx.textAlign = "center";
        if (wind.speed < 0.1) {
            ctx.fillStyle = "#e8f5e9";
            ctx.font = "10px Segoe UI, sans-serif";
            ctx.fillText("calm", cx, cy + 3);
            return;
        }
        const len = 8 + wind.strength * 8;
        const tipX = cx + wind.x * len;
        const tipY = cy + wind.y * len;
        strokeLine(cx - wind.x * len, cy - wind.y * len, tipX, tipY, "#ffeb3b", 2);
        ctx.fillStyle = "#ffeb3b";
        ctx.beginPath();
        ctx.moveTo(tipX + wind.x * 5, tipY + wind.y * 5);
        ctx.lineTo(tipX - wind.y * 4, tipY + wind.x * 4);
        ctx.lineTo(tipX + wind.y * 4, tipY - wind.x * 4);
        ctx.closePath();
        ctx.fill();
    }

    // A cart path tile is a square with a path inside it. The path reaches the middle of each flat side
    // that has a path tile next door. No neighbours is a dot, one is a stub, two in a line is straight,
    // two at a right angle is a turn, three is a T, and four is a crossing.
    function isPathTile(x, y) {
        if (x < 0 || y < 0 || x >= map.width || y >= map.height) return false;
        const t = terrains[map.tiles[y * map.width + x]];
        return !!(t && t.isPath);
    }

    function drawPathShape(x, y, color) {
        const z = averageHeight(x, y) * LEVEL_H;
        const screen = (fx, fy) => {
            const p = flatPoint(fx, fy);
            return { x: p.x, y: p.y - z };
        };
        const centre = screen(x + 0.5, y + 0.5);
        // Middle of the four flat sides, named by the neighbour across each one.
        const sides = {
            n: { linked: isPathTile(x, y - 1), at: screen(x + 0.5, y) },
            e: { linked: isPathTile(x + 1, y), at: screen(x + 1, y + 0.5) },
            s: { linked: isPathTile(x, y + 1), at: screen(x + 0.5, y + 1) },
            w: { linked: isPathTile(x - 1, y), at: screen(x, y + 0.5) },
        };
        const linked = Object.values(sides).filter((s) => s.linked);

        ctx.fillStyle = color;
        ctx.strokeStyle = color;
        ctx.lineCap = "round";
        ctx.lineWidth = PATH_WIDTH;

        if (linked.length === 0) {
            ctx.beginPath();
            ctx.arc(centre.x, centre.y, PATH_WIDTH * 0.6, 0, Math.PI * 2);
            ctx.fill();
            return;
        }

        ctx.beginPath();
        for (const side of linked) {
            ctx.moveTo(centre.x, centre.y);
            ctx.lineTo(side.at.x, side.at.y);
        }
        ctx.stroke();
    }

    // Two white balls side by side across the tee box, marking the line golfers start from.
    function drawTeeBalls(x, y) {
        const centre = tileCentre(x, y);
        for (const dx of [-8, 8]) {
            ctx.beginPath();
            ctx.arc(centre.x + dx, centre.y, 3, 0, Math.PI * 2);
            ctx.fillStyle = "#ffffff";
            ctx.fill();
            ctx.strokeStyle = "rgba(0, 0, 0, 0.5)";
            ctx.lineWidth = 0.75;
            ctx.stroke();
        }
    }

    function drawHoles() {
        for (const hole of map.holes) {
            if (!hole.tee) continue;
            const tee = tileCentre(hole.tee.x, hole.tee.y);

            if (hole.cup) {
                const cup = tileCentre(hole.cup.x, hole.cup.y);

                ctx.setLineDash([3, 3]);
                ctx.strokeStyle = "rgba(255, 255, 255, 0.55)";
                ctx.lineWidth = 1;
                ctx.beginPath();
                ctx.moveTo(tee.x, tee.y);
                ctx.lineTo(cup.x, cup.y);
                ctx.stroke();
                ctx.setLineDash([]);

                ctx.fillStyle = "#111";
                ctx.beginPath();
                ctx.ellipse(cup.x, cup.y, 4, 2, 0, 0, Math.PI * 2);
                ctx.fill();

                ctx.strokeStyle = "#f5f5f5";
                ctx.lineWidth = 1.5;
                ctx.beginPath();
                ctx.moveTo(cup.x, cup.y);
                ctx.lineTo(cup.x, cup.y - 22);
                ctx.stroke();

                drawFlag(cup.x, cup.y - 22, hole.number);
            }

            // The tee box's own balls mark the start, so the hole only needs its number above them.
            ctx.fillStyle = "#ffffff";
            ctx.font = "bold 10px Segoe UI, sans-serif";
            ctx.textAlign = "center";
            ctx.fillText(String(hole.number), tee.x, tee.y - 10);
        }
    }

    function drawHover() {
        if (!hover) return;
        tracePath(tileCorners(hover.tile.x, hover.tile.y));
        ctx.strokeStyle = "rgba(255, 255, 255, 0.9)";
        ctx.lineWidth = 2;
        ctx.stroke();

        // The corner that a raise or lower would change.
        const p = cornerPoint(hover.corner.x, hover.corner.y);
        ctx.beginPath();
        ctx.arc(p.x, p.y, 4, 0, Math.PI * 2);
        ctx.fillStyle = "#ffffff";
        ctx.fill();
        ctx.strokeStyle = "#000000";
        ctx.lineWidth = 1;
        ctx.stroke();
    }

    function draw() {
        if (!ctx) return;
        const rect = canvas.getBoundingClientRect();
        const dpr = window.devicePixelRatio || 1;

        ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
        ctx.fillStyle = "#0d1a12";
        ctx.fillRect(0, 0, rect.width, rect.height);
        if (!map) return;

        // Camera: world point (camera.x, camera.y) sits at the centre of the canvas.
        const z = camera.zoom;
        ctx.setTransform(
            dpr * z, 0, 0, dpr * z,
            dpr * (rect.width / 2 - camera.x * z),
            dpr * (rect.height / 2 - camera.y * z));

        // Back to front: tiles are sorted by depth in this view, then buildings and golfers at their depth.
        const w = map.width;
        const h = map.height;
        const items = [];
        for (let y = 0; y < h; y++) {
            for (let x = 0; x < w; x++) items.push({ key: tileKey(x, y), rank: 0, x, y });
        }
        for (const item of pieceItems()) items.push(item);
        for (const t of map.trees || []) items.push({ key: tileKey(t.x, t.y), rank: 1, tree: t });
        for (const item of golferItems()) items.push(item);
        for (const item of ballItems()) items.push(item);
        items.sort((a, b) => a.key - b.key || a.rank - b.rank);

        for (const item of items) {
            if (item.golfer) {
                drawGolfer(item.golfer);
            } else if (item.tree) {
                drawTree(item.tree);
            } else if (item.ball) {
                drawBall(item.ball);
            } else if (item.piece) {
                drawPiece(item.piece, item.alpha);
            } else {
                drawTile(item.x, item.y, map.tiles[item.y * w + item.x], map.grounds ? map.grounds[item.y * w + item.x] : null);
                if (pendingSet.has(item.x + "," + item.y)) overlayTile(item.x, item.y);
            }
        }

        drawCloudShadows();
        drawHoles();
        drawHover();

        // Weather sits over the whole view in screen pixels, not world pixels.
        ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
        drawSkyShade(rect.width, rect.height);
        drawRain(rect.width, rect.height);
        drawLightning(rect.width, rect.height);
        drawWindCompass(rect.width);
        ctx.textAlign = "start";
        positionPopup();
    }

    // ---- camera and sizing ------------------------------------------------

    function centreCamera() {
        // Centre of the map: tile centre (w / 2, h / 2) in world space.
        camera.x = (map.width - map.height) * TILE_W / 4;
        camera.y = (map.width + map.height) * TILE_H / 4;
        camera.zoom = START_ZOOM;
        cameraCentred = true;
    }

    function setMap(next) {
        map = next;
        pendingSet = new Set((map.pending || []).map((t) => t.x + "," + t.y));
        popupTile = map.popupTile || null;
        maxAbsHeight = 0;
        for (const h of map.heights) maxAbsHeight = Math.max(maxAbsHeight, Math.abs(h));
        if (!cameraCentred && map) centreCamera();
        draw();
        startAnimation();
    }

    function resize() {
        const rect = canvas.getBoundingClientRect();
        const dpr = window.devicePixelRatio || 1;
        canvas.width = Math.round(rect.width * dpr);
        canvas.height = Math.round(rect.height * dpr);
        draw();
    }

    // ---- pointer input ----------------------------------------------------

    function onMouseDown(e) {
        const rect = canvas.getBoundingClientRect();
        const sx = e.clientX - rect.left;
        const sy = e.clientY - rect.top;

        if (e.button === 0) {
            const loc = locate(sx, sy);
            pointer = { button: 0, lastX: sx, lastY: sy, last: loc };
            if (loc) dotNet.invokeMethodAsync("OnPointerDown", loc.tile.x, loc.tile.y, loc.corner.x, loc.corner.y);
        } else if (e.button === 1 || e.button === 2) {
            // The location under a right press, so a right click without a drag can act on it.
            pointer = { button: e.button, lastX: sx, lastY: sy, startX: sx, startY: sy, moved: false, last: null, secondary: locate(sx, sy) };
        }
        e.preventDefault();
    }

    function onMouseMove(e) {
        if (!canvas) return;
        const rect = canvas.getBoundingClientRect();
        const sx = e.clientX - rect.left;
        const sy = e.clientY - rect.top;

        if (pointer && pointer.button !== 0) {
            // Right or middle drag pans the camera. Moving more than a few pixels makes it a drag, not a click.
            if (Math.hypot(sx - pointer.startX, sy - pointer.startY) > 4) pointer.moved = true;
            camera.x -= (sx - pointer.lastX) / camera.zoom;
            camera.y -= (sy - pointer.lastY) / camera.zoom;
            pointer.lastX = sx;
            pointer.lastY = sy;
            draw();
        } else if (pointer && pointer.button === 0) {
            // Left drag acts again whenever the pointer moves to a new tile or corner.
            const loc = locate(sx, sy);
            if (loc && !sameLocation(loc, pointer.last)) {
                pointer.last = loc;
                dotNet.invokeMethodAsync("OnPointerDrag", loc.tile.x, loc.tile.y, loc.corner.x, loc.corner.y);
            }
        }

        const loc = insideCanvas(sx, sy) ? locate(sx, sy) : null;
        if (!sameLocation(loc, hover)) {
            hover = loc;
            draw();
            if (loc) {
                dotNet.invokeMethodAsync("OnPointerHover", loc.tile.x, loc.tile.y, loc.corner.x, loc.corner.y);
            } else {
                dotNet.invokeMethodAsync("OnPointerHover", -1, -1, -1, -1);
            }
        }
    }

    function onMouseUp(e) {
        // A left release reports the tile it ended on, so footprint tiles can be marked on release.
        if (pointer && pointer.button === 0 && canvas) {
            const rect = canvas.getBoundingClientRect();
            const loc = locate(e.clientX - rect.left, e.clientY - rect.top);
            dotNet.invokeMethodAsync("OnPointerUp", loc ? loc.tile.x : -1, loc ? loc.tile.y : -1);
        }
        // A right click without a drag. The corner tool lowers the corner under the press, and other tools turn off.
        // A right drag only pans.
        if (pointer && pointer.button === 2 && !pointer.moved) {
            const loc = pointer.secondary;
            if (loc) dotNet.invokeMethodAsync("OnSecondaryClick", loc.tile.x, loc.tile.y, loc.corner.x, loc.corner.y);
            else dotNet.invokeMethodAsync("OnCancelTool");
        }
        pointer = null;
    }

    function onWheel(e) {
        e.preventDefault();
        const rect = canvas.getBoundingClientRect();
        const sx = e.clientX - rect.left;
        const sy = e.clientY - rect.top;

        // Zoom around the pointer: the world point under the cursor stays under the cursor.
        const before = screenToWorld(sx, sy);
        const factor = e.deltaY < 0 ? 1.12 : 1 / 1.12;
        camera.zoom = Math.min(MAX_ZOOM, Math.max(MIN_ZOOM, camera.zoom * factor));
        const after = screenToWorld(sx, sy);
        camera.x += before.x - after.x;
        camera.y += before.y - after.y;
        draw();
    }

    function init(element, dotNetRef, terrainList, buildingList) {
        canvas = element;
        ctx = canvas.getContext("2d");
        dotNet = dotNetRef;
        terrains = {};
        for (const t of terrainList) terrains[t.id] = t;
        buildingDefs = {};
        for (const b of buildingList) buildingDefs[b.id] = b;

        canvas.addEventListener("mousedown", onMouseDown);
        canvas.addEventListener("wheel", onWheel, { passive: false });
        canvas.addEventListener("contextmenu", (e) => e.preventDefault());
        window.addEventListener("mousemove", onMouseMove);
        window.addEventListener("mouseup", onMouseUp);

        new ResizeObserver(resize).observe(canvas);
        resize();
    }

    // Turns the view by quarter turns. Positive turns clockwise, and the map turns about its centre.
    function rotate(quarterTurns) {
        rotation = (((rotation + quarterTurns) % 4) + 4) % 4;
        draw();
    }

    window.simGolfCanvas = { init, setMap, setGolfers, positionPopup: () => positionPopup(), rotate };

    // Browser storage for the per-browser save. Every call is guarded: storage can be blocked.
    window.simGolfStorage = {
        get(key) {
            try { return window.localStorage.getItem(key); } catch (e) { return null; }
        },
        set(key, value) {
            try { window.localStorage.setItem(key, value); return true; } catch (e) { return false; }
        },
    };

    // Saving a course to a file and picking one to load. Both are plain browser actions, so they can't fail for the course itself.
    window.simGolfFile = {
        download(fileName, text) {
            const url = URL.createObjectURL(new Blob([text], { type: "application/json" }));
            const link = document.createElement("a");
            link.href = url;
            link.download = fileName;
            document.body.appendChild(link);
            link.click();
            link.remove();
            setTimeout(() => URL.revokeObjectURL(url), 1000);
        },
        openPicker(inputId) {
            const input = document.getElementById(inputId);
            if (input) input.click();
        },
    };
})();
