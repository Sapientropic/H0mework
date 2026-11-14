import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.ParityBlock
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Row

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine.Extract

open InterferenceProgram

structure Check where
  accepted : Bool
  visits : Nat
  deriving Repr

/-- Every visited list constructor and literal comparison is charged here. -/
def member {n : Nat} (lit : CNFLiteral n) : CNFClause n → Check
  | [] => ⟨false, 1⟩
  | head :: rest =>
      if lit = head then ⟨true, 2⟩
      else let next := member lit rest; ⟨next.accepted, next.visits + 2⟩

theorem member_accepted {n : Nat} (lit : CNFLiteral n) (clause : CNFClause n) :
    (member lit clause).accepted = true ↔ lit ∈ clause := by
  induction clause with
  | nil => simp [member]
  | cons head rest ih =>
      by_cases equal : lit = head <;> simp [member, equal, ih]

theorem member_visits {n : Nat} (lit : CNFLiteral n) (clause : CNFClause n) :
    (member lit clause).visits ≤ 2 * clause.length + 1 := by
  induction clause with
  | nil => simp [member]
  | cons head rest ih =>
      by_cases equal : lit = head <;> simp only [member, equal, if_true, if_false,
        List.length_cons] <;> omega

def subset {n : Nat} : CNFClause n → CNFClause n → Check
  | [], _ => ⟨true, 1⟩
  | lit :: rest, clause =>
      let hit := member lit clause
      if hit.accepted then
        let next := subset rest clause
        ⟨next.accepted, 1 + hit.visits + next.visits⟩
      else ⟨false, 1 + hit.visits⟩

theorem subset_accepted {n : Nat} (left right : CNFClause n) :
    (subset left right).accepted = true ↔ ∀ lit ∈ left, lit ∈ right := by
  induction left with
  | nil => simp [subset]
  | cons lit rest ih =>
      simp only [subset]
      split
      · rename_i found
        have hit := (member_accepted lit right).mp found
        simp [ih, hit]
      · rename_i absent
        have miss : lit ∉ right := by simpa [member_accepted] using absent
        simp [miss]

theorem subset_visits {n : Nat} (left right : CNFClause n) :
    (subset left right).visits ≤ left.length * (2 * right.length + 2) + 1 := by
  induction left with
  | nil => simp [subset]
  | cons lit rest ih =>
      have hit := member_visits lit right
      simp only [subset, List.length_cons]
      split <;> simp only <;> nlinarith

/-- Clause truth is a set operation; repeated occurrences remain in the original formula. -/
def sameClause {n : Nat} (left right : CNFClause n) : Check :=
  let first := subset left right
  if first.accepted then
    let second := subset right left
    ⟨second.accepted, first.visits + second.visits + 1⟩
  else ⟨false, first.visits + 1⟩

theorem sameClause_accepted {n : Nat} (left right : CNFClause n) :
    (sameClause left right).accepted = true ↔ ∀ lit, lit ∈ left ↔ lit ∈ right := by
  simp only [sameClause]
  split
  · rename_i first
    have leftRight := (subset_accepted left right).mp first
    rw [subset_accepted]
    exact ⟨fun back lit => ⟨leftRight lit, back lit⟩,
      fun same lit member => (same lit).mpr member⟩
  · rename_i absent
    have miss : ¬ ∀ lit ∈ left, lit ∈ right := by
      simpa only [subset_accepted] using absent
    exact ⟨by simp, fun same => False.elim (miss (fun lit hit => (same lit).mp hit))⟩

theorem sameClause_eval {n : Nat} (left right : CNFClause n) (assignment : Nat → Bool)
    (same : (sameClause left right).accepted = true) :
    CNFClause.eval left assignment = CNFClause.eval right assignment := by
  have members := (sameClause_accepted left right).mp same
  apply Bool.eq_iff_iff.mpr
  simp only [CNFClause.eval, List.any_eq_true]
  exact ⟨fun ⟨lit, hit, value⟩ => ⟨lit, (members lit).mp hit, value⟩,
    fun ⟨lit, hit, value⟩ => ⟨lit, (members lit).mpr hit, value⟩⟩

theorem sameClause_visits {n : Nat} (left right : CNFClause n) :
    (sameClause left right).visits ≤
      4 * left.length * right.length + 2 * left.length + 2 * right.length + 3 := by
  have forward := subset_visits left right
  have backward := subset_visits right left
  simp only [sameClause]
  split <;> simp only <;> nlinarith

def findClause {n : Nat} (query : CNFClause n) : CNFFormula n → Check
  | [] => ⟨false, 1⟩
  | clause :: rest =>
      let test := sameClause query clause
      if test.accepted then ⟨true, test.visits + 1⟩
      else let next := findClause query rest; ⟨next.accepted, test.visits + next.visits + 1⟩

theorem findClause_accepted {n : Nat} (query : CNFClause n) (formula : CNFFormula n) :
    (findClause query formula).accepted = true ↔
      ∃ clause ∈ formula, (sameClause query clause).accepted = true := by
  induction formula with
  | nil => simp [findClause]
  | cons clause rest ih =>
      simp only [findClause]
      split
      · rename_i found
        simp [found]
      · rename_i absent
        simpa [absent] using ih

theorem findClause_eval {n : Nat} (query : CNFClause n) (formula : CNFFormula n)
    (assignment : Nat → Bool) (satisfies : CNFFormula.eval formula assignment = true)
    (found : (findClause query formula).accepted = true) :
    CNFClause.eval query assignment = true := by
  obtain ⟨clause, hit, same⟩ := (findClause_accepted query formula).mp found
  rw [sameClause_eval query clause assignment same]
  exact List.all_eq_true.mp satisfies clause hit

def allBlocks {n : Nat} (formula : CNFFormula n) : CNFFormula n → Check
  | [] => ⟨true, 1⟩
  | clause :: rest =>
      let hit := findClause clause formula
      if hit.accepted then
        let next := allBlocks formula rest
        ⟨next.accepted, hit.visits + next.visits + 1⟩
      else ⟨false, hit.visits + 1⟩

theorem allBlocks_accepted {n : Nat} (formula blocks : CNFFormula n) :
    (allBlocks formula blocks).accepted = true ↔
      ∀ clause ∈ blocks, (findClause clause formula).accepted = true := by
  induction blocks with
  | nil => simp [allBlocks]
  | cons clause rest ih =>
      simp only [allBlocks]
      split
      · rename_i hit
        simpa [hit] using ih
      · rename_i miss
        simp [miss]

theorem allBlocks_eval {n : Nat} (formula blocks : CNFFormula n) (assignment : Nat → Bool)
    (satisfies : CNFFormula.eval formula assignment = true)
    (found : (allBlocks formula blocks).accepted = true) :
    CNFFormula.eval blocks assignment = true := by
  apply List.all_eq_true.mpr
  intro clause hit
  exact findClause_eval clause formula assignment satisfies
    ((allBlocks_accepted formula blocks).mp found clause hit)

def binaryBlock {n : Nat} (a b : CNFLiteral n) : CNFFormula n :=
  [[a, b], [Alias.negate a, Alias.negate b]]

def binaryRow {n : Nat} (a b : CNFLiteral n) : Row :=
  (Row.mk [a.var.val, b.var.val] (!(a.positive ^^ b.positive))).normalize

def ternaryRow {n : Nat} (a b c : CNFLiteral n) : Row :=
  (Row.mk [a.var.val, b.var.val, c.var.val]
    (a.positive ^^ (b.positive ^^ c.positive))).normalize

theorem binaryRow_holds {n : Nat} (a b : CNFLiteral n) (assignment : Nat → Bool)
    (satisfies : CNFFormula.eval (binaryBlock a b) assignment = true) :
    (binaryRow a b).holds assignment = true := by
  rw [binaryRow, Row.normalize_holds, Row.holds_iff]
  simp only [binaryBlock, CNFFormula.eval, CNFClause.eval, List.all_cons,
    List.all_nil, List.any_cons, List.any_nil, Alias.negate_eval] at satisfies
  simp only [Row.eval, Parity.eval, Bool.xor_false]
  cases ha : a.positive <;> cases hb : b.positive <;>
    cases hxa : assignment a.var.val <;> cases hxb : assignment b.var.val <;>
    simp_all [CNFLiteral.eval]

theorem ternaryRow_holds {n : Nat} (a b c : CNFLiteral n) (assignment : Nat → Bool)
    (satisfies : CNFFormula.eval (CouncilParityProbe.parityBlock a b c) assignment = true) :
    (ternaryRow a b c).holds assignment = true := by
  rw [CouncilParityProbe.parityBlock_eval] at satisfies
  rw [ternaryRow, Row.normalize_holds, Row.holds_iff]
  simp only [Row.eval, Parity.eval, Bool.xor_false]
  cases ha : a.positive <;> cases hb : b.positive <;> cases hc : c.positive <;>
    cases hxa : assignment a.var.val <;> cases hxb : assignment b.var.val <;>
    cases hxc : assignment c.var.val <;> simp_all [CNFLiteral.eval]

structure Inspection where
  row : Option Row
  visits : Nat
  deriving Repr

def inspect {n : Nat} (formula : CNFFormula n) : CNFClause n → Inspection
  | [a, b] =>
      let test := allBlocks formula (binaryBlock a b)
      ⟨if test.accepted then some (binaryRow a b) else none, test.visits + 16⟩
  | [a, b, c] =>
      let test := allBlocks formula (CouncilParityProbe.parityBlock a b c)
      ⟨if test.accepted then some (ternaryRow a b c) else none, test.visits + 32⟩
  | _ => ⟨none, 4⟩

theorem inspect_holds {n : Nat} (formula : CNFFormula n) (clause : CNFClause n)
    (assignment : Nat → Bool) (satisfies : CNFFormula.eval formula assignment = true)
    (row : Row) (found : (inspect formula clause).row = some row) :
    row.holds assignment = true := by
  unfold inspect at found
  split at found
  · rename_i a b
    dsimp only at found
    split at found
    · cases found
      exact binaryRow_holds a b assignment (allBlocks_eval _ _ _ satisfies (by assumption))
    · contradiction
  · rename_i a b c
    dsimp only at found
    split at found
    · cases found
      exact ternaryRow_holds a b c assignment (allBlocks_eval _ _ _ satisfies (by assumption))
    · contradiction
  · contradiction

structure Result where
  rows : List Row
  visits : Nat
  deriving Repr

def scan {n : Nat} (formula : CNFFormula n) : CNFFormula n → Result
  | [] => ⟨[], 1⟩
  | clause :: rest =>
      let first := inspect formula clause
      let next := scan formula rest
      ⟨first.row.toList ++ next.rows, first.visits + next.visits + 1⟩

def run {n : Nat} (formula : CNFFormula n) : Result := scan formula formula

def extract {n : Nat} (formula : CNFFormula n) : List Row := (run formula).rows

theorem scan_entails {n : Nat} (formula anchors : CNFFormula n) (assignment : Nat → Bool)
    (satisfies : CNFFormula.eval formula assignment = true) :
    holds (scan formula anchors).rows assignment = true := by
  rw [holds_iff]
  induction anchors with
  | nil => simp [scan]
  | cons clause rest ih =>
      intro row member
      simp only [scan, List.mem_append, Option.mem_toList] at member
      rcases member with found | tail
      · exact inspect_holds formula clause assignment satisfies row found
      · exact ih row tail

theorem extract_entails {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (satisfies : CNFFormula.eval formula assignment = true) :
    holds (extract formula) assignment = true := scan_entails formula formula assignment satisfies

theorem scan_length {n : Nat} (formula anchors : CNFFormula n) :
    (scan formula anchors).rows.length ≤ anchors.length := by
  induction anchors with
  | nil => simp [scan]
  | cons clause rest ih =>
      simp only [scan, List.length_append, List.length_cons]
      cases (inspect formula clause).row <;> simp_all <;> omega

theorem extract_length {n : Nat} (formula : CNFFormula n) :
    (extract formula).length ≤ formula.length := scan_length formula formula

theorem scan_member {n : Nat} (formula anchors : CNFFormula n) (row : Row) :
    row ∈ (scan formula anchors).rows ↔
      ∃ clause ∈ anchors, (inspect formula clause).row = some row := by
  induction anchors with
  | nil => simp [scan]
  | cons clause rest ih =>
      simp only [scan, List.mem_append, Option.mem_toList, ih, List.mem_cons]
      aesop

theorem extract_member {n : Nat} (formula : CNFFormula n) (row : Row) :
    row ∈ extract formula ↔
      ∃ clause ∈ formula, (inspect formula clause).row = some row :=
  scan_member formula formula row

theorem allBlocks_of_subset {n : Nat} (formula blocks : CNFFormula n)
    (present : ∀ clause ∈ blocks, clause ∈ formula) :
    (allBlocks formula blocks).accepted = true := by
  apply (allBlocks_accepted formula blocks).mpr
  intro clause hit
  exact (findClause_accepted clause formula).mpr ⟨clause, present clause hit,
    (sameClause_accepted clause clause).mpr (fun _ => Iff.rfl)⟩

theorem ternary_mem {n : Nat} (formula : CNFFormula n) (a b c : CNFLiteral n)
    (present : ∀ clause ∈ CouncilParityProbe.parityBlock a b c, clause ∈ formula) :
    ternaryRow a b c ∈ extract formula := by
  apply (extract_member formula _).mpr
  refine ⟨[a, b, c], present _ (by simp [CouncilParityProbe.parityBlock]), ?_⟩
  simp only [inspect, allBlocks_of_subset formula _ present, if_true]

theorem binary_mem {n : Nat} (formula : CNFFormula n) (a b : CNFLiteral n)
    (present : ∀ clause ∈ binaryBlock a b, clause ∈ formula) :
    binaryRow a b ∈ extract formula := by
  apply (extract_member formula _).mpr
  refine ⟨[a, b], present _ (by simp [binaryBlock]), ?_⟩
  simp only [inspect, allBlocks_of_subset formula _ present, if_true]

def WellFormed (n : Nat) (row : Row) : Prop :=
  row.vars.Nodup ∧ row.vars.length ≤ 3 ∧ Parity.Within n row.vars

theorem normalize_wellFormed (n : Nat) (row : Row) (short : row.vars.length ≤ 3)
    (inside : Parity.Within n row.vars) : WellFormed n row.normalize := by
  refine ⟨row.normalize_nodup, ?_, ?_⟩
  · have bound := Parity.merge_length row.vars []
    simpa only [Row.normalize, List.length_nil, Nat.add_zero] using bound.trans short
  · exact Parity.merge_within row.vars [] n inside (by simp [Parity.Within])

theorem binary_wellFormed {n : Nat} (a b : CNFLiteral n) : WellFormed n (binaryRow a b) := by
  apply normalize_wellFormed
  · simp
  · intro i hit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl
    · exact a.var.isLt
    · exact b.var.isLt

theorem ternary_wellFormed {n : Nat} (a b c : CNFLiteral n) :
    WellFormed n (ternaryRow a b c) := by
  apply normalize_wellFormed
  · simp
  · intro i hit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl | rfl
    · exact a.var.isLt
    · exact b.var.isLt
    · exact c.var.isLt

theorem inspect_wellFormed {n : Nat} (formula : CNFFormula n) (clause : CNFClause n)
    (row : Row) (found : (inspect formula clause).row = some row) : WellFormed n row := by
  unfold inspect at found
  split at found
  · rename_i a b
    dsimp only at found
    split at found
    · cases found
      exact binary_wellFormed a b
    · contradiction
  · rename_i a b c
    dsimp only at found
    split at found
    · cases found
      exact ternary_wellFormed a b c
    · contradiction
  · contradiction

theorem extract_wellFormed {n : Nat} (formula : CNFFormula n) (row : Row)
    (generated : row ∈ extract formula) : WellFormed n row := by
  obtain ⟨clause, _, found⟩ := (extract_member formula row).mp generated
  exact inspect_wellFormed formula clause row found

def literalCount {n : Nat} (formula : CNFFormula n) : Nat := (formula.map List.length).sum

theorem findClause_visits {n : Nat} (query : CNFClause n) (formula : CNFFormula n) :
    (findClause query formula).visits ≤
      (4 * query.length + 2) * literalCount formula +
      (2 * query.length + 4) * formula.length + 1 := by
  induction formula with
  | nil => simp [findClause, literalCount]
  | cons clause rest ih =>
      have test := sameClause_visits query clause
      simp only [findClause, literalCount, List.map_cons, List.sum_cons, List.length_cons]
      simp only [literalCount] at ih
      split <;> simp only <;> nlinarith

theorem allBlocks_visits {n : Nat} (formula blocks : CNFFormula n)
    (short : ∀ clause ∈ blocks, clause.length ≤ 3) :
    (allBlocks formula blocks).visits ≤
      blocks.length * (14 * literalCount formula + 10 * formula.length + 2) + 1 := by
  induction blocks with
  | nil => simp [allBlocks]
  | cons clause rest ih =>
      have head := short clause (by simp)
      have tail := ih (fun value hit => short value (by simp [hit]))
      have hit := findClause_visits clause formula
      have bound : (findClause clause formula).visits ≤
          14 * literalCount formula + 10 * formula.length + 1 := by nlinarith
      simp only [allBlocks, List.length_cons]
      split <;> simp only <;> nlinarith

theorem inspect_visits {n : Nat} (formula : CNFFormula n) (clause : CNFClause n) :
    (inspect formula clause).visits ≤ 56 * literalCount formula + 40 * formula.length + 41 := by
  unfold inspect
  split
  · rename_i a b
    have bound := allBlocks_visits formula (binaryBlock a b) (by simp [binaryBlock])
    simp only [binaryBlock, List.length_cons, List.length_nil] at bound
    dsimp only [binaryBlock]
    omega
  · rename_i a b c
    have bound := allBlocks_visits formula (CouncilParityProbe.parityBlock a b c)
      (by simp [CouncilParityProbe.parityBlock])
    simp only [CouncilParityProbe.parityBlock, List.length_cons, List.length_nil] at bound
    dsimp only [CouncilParityProbe.parityBlock]
    omega
  · dsimp only
    omega

theorem scan_visits {n : Nat} (formula anchors : CNFFormula n) :
    (scan formula anchors).visits ≤
      anchors.length * (56 * literalCount formula + 40 * formula.length + 42) + 1 := by
  induction anchors with
  | nil => simp [scan]
  | cons clause rest ih =>
      have first := inspect_visits formula clause
      simp only [scan, List.length_cons]
      nlinarith

theorem run_visits {n : Nat} (formula : CNFFormula n) :
    (run formula).visits ≤
      formula.length * (56 * literalCount formula + 40 * formula.length + 42) + 1 :=
  scan_visits formula formula

end SaturationMonoid.ComplexityProjection.SATSource.Affine.Extract
