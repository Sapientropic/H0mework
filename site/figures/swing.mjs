// A small swing of the camera for figures drawn to be read from one front: a sideways drag turns the
// view up to ±30° about the figure's own middle, and it eases home once the figure is left alone.
// The kit's light is camera-locked, so a figure redrawn from azimuth a + θ is the same machine seen
// from θ round; each figure redraws itself through `onSwing` with the projection from `swingOf`.
// Both functions are shipped to the page as source (`swingSource`), so they use only their arguments
// and browser globals.

// The projection θ degrees round from P0, framed like the figure's own fit: its fit points centred in
// the card at P0's scale, or a little smaller where the turned outline would not fit (the camera steps
// back rather than cut the drawing off). At θ = 0 this is P0 itself.
export function swingOf(iso, P0, { points, width, height, pad }, degrees) {
  const azimuth = P0.azimuth + degrees;
  const flat = points.map((point) => iso(point, { origin: [0, 0], scale: 1, azimuth, elevation: P0.elevation }));
  const xs = flat.map(([x]) => x), ys = flat.map(([, y]) => y);
  const left = Math.min(...xs), right = Math.max(...xs), up = Math.min(...ys), down = Math.max(...ys);
  const scale = Math.min(P0.scale, (width - 2 * pad) / (right - left), (height - 2 * pad) / (down - up));
  return { ...P0, azimuth, scale, origin: [width / 2 - ((left + right) / 2) * scale, height / 2 - ((up + down) / 2) * scale] };
}

export function mountSwing(stage, { onSwing, onHold, limit = 30, home = 9000 }) {
  const still = matchMedia("(prefers-reduced-motion: reduce)");
  const svg = stage.querySelector("svg");
  let angle = 0, goal = null, press = null, quiet = -1e9, frame = 0, last = 0, back = 0, dragged = null, paint = 0;
  // A drag across the whole drawing sweeps the whole range; past the limit it gives like a rubber band.
  const perPx = () => (2 * limit) / Math.max(400, svg.getBoundingClientRect().width);
  const give = (a) => (Math.abs(a) <= limit ? a : Math.sign(a) * (limit + (Math.abs(a) - limit) * 0.25));
  const clamp = (a) => Math.max(-limit, Math.min(limit, a));
  const show = (a) => { if (a !== angle) { angle = a; onSwing(angle); } };
  function tick(now) {
    const dt = last ? Math.min((now - last) / 1000, 1 / 30) : 1 / 60;
    last = now;
    const next = angle + (goal - angle) * (1 - Math.exp(-dt / 0.22));
    show(Math.abs(goal - next) < 0.02 ? goal : next);
    if (angle === goal) { goal = null; frame = 0; } else frame = requestAnimationFrame(tick);
  }
  const ease = (to) => {
    goal = to;
    if (still.matches) { show(goal); goal = null; return; }
    if (!frame) { last = 0; frame = requestAnimationFrame(tick); }
  };
  // Home after the figure has been left alone; without motion it stays where it was left.
  const later = () => { clearTimeout(back); if (!still.matches) back = setTimeout(() => ease(0), home); };
  stage.addEventListener("pointerdown", (event) => {
    if (event.button !== 0) return;
    press = { id: event.pointerId, x: event.clientX, y: event.clientY, from: angle, moved: false };
  });
  stage.addEventListener("pointermove", (event) => {
    if (!press || event.pointerId !== press.id) return;
    const dx = event.clientX - press.x;
    if (!press.moved) {
      if (Math.abs(dx) < 6 || Math.abs(dx) < Math.abs(event.clientY - press.y)) return;
      press.moved = true;
      cancelAnimationFrame(frame); frame = 0; goal = null; clearTimeout(back);
      stage.setPointerCapture(event.pointerId);
      stage.classList.add("swinging");
      onHold?.();
    }
    // A pointer can report several moves a frame; the drawing follows once per frame.
    dragged = give(press.from + dx * perPx());
    if (!paint) paint = requestAnimationFrame(() => { paint = 0; if (dragged !== null) show(dragged); });
  });
  const release = (event) => {
    if (!press || event.pointerId !== press.id) return;
    if (press.moved) {
      cancelAnimationFrame(paint); paint = 0;
      if (dragged !== null) show(dragged);
      dragged = null;
      quiet = event.timeStamp;
      stage.classList.remove("swinging");
      ease(clamp(angle));
      later();
    }
    press = null;
  };
  stage.addEventListener("pointerup", release);
  stage.addEventListener("pointercancel", release);
  // The click that ends a drag is not the figure's click.
  stage.addEventListener("click", (event) => { if (event.timeStamp - quiet < 80) { event.stopImmediatePropagation(); event.preventDefault(); } }, true);
  const control = { get: () => angle, set: (value) => { onHold?.(); cancelAnimationFrame(frame); frame = 0; goal = null; show(clamp(Number(value))); later(); } };
  // The kit's turn hook, so drive.mjs can turn and orbit the figure.
  window.__isoTurn = control;
  return control;
}

// Page source: functions as declarations, plain values as JSON.
export function shipped(entries) {
  return Object.entries(entries).map(([name, value]) => {
    if (typeof value !== "function") return `const ${name} = ${JSON.stringify(value)};`;
    const source = value.toString();
    return /^(async\s+)?function\b/.test(source) ? source : `const ${name} = ${source};`;
  }).join("\n");
}
export const swingSource = shipped({ swingOf, mountSwing });

// The cursor and the swing's own class; a figure adds it to its CSS.
export const SWING_CSS = ".iso-stage.swinging,.iso-stage.swinging *{cursor:grabbing}";
