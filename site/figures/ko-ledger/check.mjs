// Checks the ko-ledger model against §1.1, Example 2.3, Example 1.1(1) and Lemma 3.2 (GO2).
import { BLACK, GAMMA, KO, N, WHITE, after, emptyBoard, keyOf, legalAt, pointOf, portsOf, replay, setOf } from "./model.mjs";

let failures = 0;
const same = (a, b, message) => {
  if (JSON.stringify(a) !== JSON.stringify(b)) {
    failures++;
    console.error("FAIL", message, a, b);
  }
};
const stones = (board, colour) => board.flatMap((c, p) => (c === colour ? [[Math.floor(p / N), p % N]] : []));

const [g1, g2] = GAMMA.map(replay);
// Both paths reach Black {(0,1),(1,0),(2,0)}, White {(0,2),(1,1)}, White to move.
same(keyOf(g1.board), keyOf(g2.board), "one visible board");
same(stones(g1.board, BLACK), [[0, 1], [1, 0], [2, 0]], "Black stones");
same(stones(g1.board, WHITE), [[0, 2], [1, 1]], "White stones");
same([g1.toMove, g2.toMove], [WHITE, WHITE], "White to move on both");
same([g1.passes, g2.passes], [0, 0], "both reset the consecutive pass count");
// Move 7 of γ2 captures W(0,0); move 5 is a pass that repeats the board of move 4.
same(g2.plies[6].captured, [pointOf(0, 0)], "B(0,1) captures W(0,0)");
same(g2.plies[4].fresh, false, "the pass repeats a board");
same([g1.history.length, setOf(g1.history).length, g2.history.length, setOf(g2.history).length], [6, 6, 8, 7], "lists 6 and 8, sets 6 and 7");
// B* = After(B, W, (0,0)) is the board after move 6 of γ2, absent from γ1's history.
const star = keyOf(after(g1.board, WHITE, pointOf(...KO)).board);
same(star, keyOf(g2.plies[5].board), "B* is the board after move 6 of γ2");
same([setOf(g1.history).includes(star), setOf(g2.history).includes(star)], [false, true], "B* ∉ set(H γ1), B* ∈ set(H γ2)");
same([legalAt(g1, ...KO), legalAt(g2, ...KO)], [true, false], "W(0,0) legal after γ1, blocked after γ2");
same([portsOf(g1), portsOf(g2)], [357, 356], "357 vs 356 non-resigning ports");

// Lemma 3.2: frames with the same board and the same history set have the same legal moves, whatever the
// order or multiplicity of the list. γ2's list reversed, with every board repeated, is one such frame.
const shuffled = [...g2.history].reverse().flatMap(({ board }) => [{ board, toMove: WHITE }, { board, toMove: BLACK }]);
const legal = (frame) => Array.from({ length: N * N }, (_, p) => legalAt(frame, Math.floor(p / N), p % N));
same(legal({ ...g2, history: shuffled }), legal(g2), "same set, same legal moves");
const once = replay([[BLACK, "pass"]]), twice = replay([[BLACK, "pass"], [WHITE, "pass"]]);
same([portsOf(once), portsOf(twice), setOf(twice.history).length], [362, 0, 1], "pass exempt, double-pass terminal, one recorded board");
same([legalAt(once, 0, N), legalAt(once, 1, -1), legalAt(twice, 0, 0)], [false, false, false], "off-board and terminal placements rejected");

// Example 1.1(1): after Black passes and White plays x, the colour-swapped history set equals the set
// reached by Black playing x directly: {B∅, B_x}.
const x = pointOf(3, 3);
const viaPass = [emptyBoard(), emptyBoard(), after(emptyBoard(), WHITE, x).board];
const swap = (board) => board.map((c) => (c === BLACK ? WHITE : c === WHITE ? BLACK : c));
const direct = [emptyBoard(), after(emptyBoard(), BLACK, x).board];
same(new Set(viaPass.map(swap).map(keyOf)).size, 2, "the duplicate empty board collapses");
same([...new Set(viaPass.map(swap).map(keyOf))].sort(), [...new Set(direct.map(keyOf))].sort(), "swap({B∅, W_x}) = {B∅, B_x}");

if (failures) process.exit(1);
console.log("model check passed: γ1 and γ2 share one board; sets 6 and 7; W(0,0) legal vs blocked; 357 vs 356 ports");
