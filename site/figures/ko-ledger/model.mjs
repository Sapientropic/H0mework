// Truth model for the ko-ledger figure: §1.1, Example 2.3 and Lemma 3.2 (GO2) of "First-Player
// Non-Negativity and Proof-Carrying Regional DAG Strategy Certificates for Positional-Superko Go"
// (papers/certified-go). Placements use no-suicide positional superko on 19 × 19.
// Pass is exempt from the history test and two consecutive passes end play.

export const N = 19;
export const EMPTY = 0, BLACK = 1, WHITE = 2;
export const other = (c) => (c === BLACK ? WHITE : BLACK);
export const pointOf = (r, j) => (Number.isInteger(r) && Number.isInteger(j) && r >= 0 && r < N && j >= 0 && j < N ? r * N + j : -1);
const neighbours = (p) => {
  const r = Math.floor(p / N), j = p % N, out = [];
  if (r > 0) out.push(p - N);
  if (r < N - 1) out.push(p + N);
  if (j > 0) out.push(p - 1);
  if (j < N - 1) out.push(p + 1);
  return out;
};
const chainOf = (board, p) => {
  const colour = board[p], seen = new Set([p]), stack = [p];
  const libs = new Set();
  while (stack.length) {
    const q = stack.pop();
    for (const n of neighbours(q)) {
      if (board[n] === EMPTY) libs.add(n);
      else if (board[n] === colour && !seen.has(n)) { seen.add(n); stack.push(n); }
    }
  }
  return { stones: [...seen], liberties: libs.size };
};
export const keyOf = (board) => board.join("");
export const emptyBoard = () => new Array(N * N).fill(EMPTY);

// After(B, c, p): place c at p, remove opponent chains left without liberties; null if suicide or occupied.
export function after(board, colour, p) {
  if (board[p] !== EMPTY) return null;
  const next = board.slice();
  next[p] = colour;
  const captured = [];
  for (const n of neighbours(p)) if (next[n] === other(colour)) {
    const chain = chainOf(next, n);
    if (!chain.liberties) { for (const s of chain.stones) next[s] = EMPTY; captured.push(...chain.stones); }
  }
  if (!chainOf(next, p).liberties) return null; // no suicide
  return { board: next, captured };
}

// A move is [colour, [r, j]] or [colour, "pass"]. Replays a sequence from the empty board, keeping the
// full history list of (board, side to move) entries, as the Lean frame does.
export function replay(moves) {
  let board = emptyBoard(), toMove = BLACK, passes = 0;
  const history = [{ board, toMove: BLACK }];
  const seen = new Set([keyOf(board)]);
  const plies = [];
  for (const [colour, move] of moves) {
    if (passes === 2 || colour !== toMove) throw new Error("invalid turn in replay");
    let captured = [];
    if (move === "pass") passes++;
    else {
      const result = after(board, colour, pointOf(...move));
      if (!result || seen.has(keyOf(result.board))) throw new Error("illegal placement in replay " + move);
      board = result.board;
      captured = result.captured;
      passes = 0;
    }
    const key = keyOf(board);
    toMove = other(colour);
    history.push({ board, toMove });
    plies.push({ colour, move, board, captured, toMove, passes, fresh: !seen.has(key) });
    seen.add(key);
  }
  return { board, history, plies, toMove, passes };
}

// The PSK quotient q(F) = (V(F), set(H(F))) of a frame, here with the pass counter folded into V.
export const setOf = (history) => [...new Set(history.map((h) => keyOf(h.board)))];
// Legal non-resigning moves ("ports") of the side to move: every empty point whose After board is
// defined and fresh, plus pass.
const freshAt = (board, colour, seen, point) => {
  const result = after(board, colour, point);
  return result && !seen.has(keyOf(result.board));
};
export function portsOf({ board, toMove, history, passes }) {
  if (passes === 2) return 0;
  const seen = new Set(setOf(history));
  let count = 1;
  for (let p = 0; p < N * N; p++) if (freshAt(board, toMove, seen, p)) count++;
  return count;
}
export const legalAt = ({ board, toMove, history, passes }, r, j) => (
  passes < 2 && Boolean(freshAt(board, toMove, new Set(setOf(history)), pointOf(r, j)))
);

const B = BLACK, W = WHITE;
// §1.1: the 5-ply γ1 and the 7-ply γ2 reach one visible board.
export const GAMMA = [
  [[B, [1, 0]], [W, [0, 2]], [B, [2, 0]], [W, [1, 1]], [B, [0, 1]]],
  [[B, [1, 0]], [W, [0, 0]], [B, [2, 0]], [W, [0, 2]], [B, "pass"], [W, [1, 1]], [B, [0, 1]]],
];
export const KO = [0, 0]; // the tested move W(0,0), A19

// The 3 × 3 corner of a board as rows of colours, for the tiles.
export const cornerOf = (board, size = 3) => Array.from({ length: size }, (_, r) => Array.from({ length: size }, (_, j) => board[r * N + j]));
