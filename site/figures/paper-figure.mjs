import { readFileSync } from "node:fs";
import { plateHtml } from "./kit/iso-kit.mjs";
import { shipped, SWING_CSS } from "./swing.mjs";

export const paperFigureCss = readFileSync(new URL("paper-figure.css", import.meta.url), "utf8") + SWING_CSS;

export function paperPlate(options) {
  return plateHtml({ ...options, fig: "" })
    .replace('<span class="iso-plate-corner" data-corner="fig"></span>', "")
    .replace('class="iso-plate-footer" aria-hidden="true"', 'class="iso-plate-footer"')
    .replace(' data-readout', ' data-readout aria-live="off" aria-atomic="true"');
}

function syncFigureArt(parent, markup) {
  let template = syncFigureArt.template;
  if (!template) template = syncFigureArt.template = document.createElement("template");
  template.innerHTML = "<svg>" + markup + "</svg>";
  syncChildren(parent, template.content.firstElementChild);
}

// Keep SVG nodes and paint servers in place while their projected paths change.
function syncChildren(current, next) {
  let node = current.firstElementChild;
  for (let source = next.firstElementChild; source; source = source.nextElementSibling) {
    if (!node) {
      current.append(source.cloneNode(true));
      continue;
    }
    const sibling = node.nextElementSibling;
    if (node.localName !== source.localName) current.replaceChild(source.cloneNode(true), node);
    else syncElement(node, source);
    node = sibling;
  }
  while (node) {
    const sibling = node.nextElementSibling;
    node.remove();
    node = sibling;
  }
}

function syncElement(node, source) {
  const attrs = node.attributes;
  for (let i = attrs.length - 1; i >= 0; i--) {
    const name = attrs[i].name;
    if (!source.hasAttribute(name)) node.removeAttribute(name);
  }
  const incoming = source.attributes;
  for (let i = 0; i < incoming.length; i++) {
    const { name, value } = incoming[i];
    if (node.getAttribute(name) !== value) node.setAttribute(name, value);
  }
  if (source.firstElementChild) syncChildren(node, source);
  else if (node.firstElementChild || node.textContent !== source.textContent) node.textContent = source.textContent;
}

// Static parts keep their markup until their geometry or the camera changes.
function partPainter(stage) {
  const parts = new Map();
  const paint = (name, key, draw) => {
    let part = parts.get(name);
    if (!part) {
      part = { node: stage.querySelector('[data-part="' + name + '"]') };
      parts.set(name, part);
    }
    if (part.key === key) return;
    syncFigureArt(part.node, draw());
    part.key = key;
  };
  paint.reset = () => parts.clear();
  return paint;
}

function playOnScreen(stage, motion, step, settle) {
  let visible = false, paused = false, frame = 0, last = 0;
  const stop = () => { cancelAnimationFrame(frame); frame = 0; last = 0; };
  function tick(time) {
    const dt = last ? Math.min((time - last) / 1000, 1 / 30) : 1 / 60;
    last = time;
    if (step(dt)) frame = requestAnimationFrame(tick);
    else stop();
  }
  const wake = () => {
    if (visible && !paused && !motion.matches && !frame) frame = requestAnimationFrame(tick);
  };
  new IntersectionObserver((entries) => {
    visible = entries[entries.length - 1].isIntersecting;
    if (visible) wake();
    else stop();
  }, { rootMargin: "120px 0px" }).observe(stage);
  motion.addEventListener("change", () => {
    if (motion.matches) { stop(); settle(); }
  });
  wake.pause = () => { paused = true; stop(); };
  wake.resume = () => { paused = false; wake(); };
  return wake;
}

const easeTo = (have, want, dt, time, tolerance) => (
  Math.abs(want - have) <= tolerance ? want : have + (want - have) * (1 - Math.exp(-dt / time))
);

export const paperFigureSource = shipped({ syncFigureArt, syncChildren, syncElement, partPainter, playOnScreen, easeTo });
