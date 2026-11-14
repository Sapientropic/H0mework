import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Extract
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Action
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Interference.Nodes

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.FunctionalRelations

open InterferenceProgram

structure Relation (n : Nat) where
  output : CNFLiteral n
  left : CNFLiteral n
  right : CNFLiteral n
  deriving DecidableEq, Repr

def Relation.Independent {n : Nat} (relation : Relation n) : Prop :=
  relation.left.var ≠ relation.output.var ∧ relation.right.var ≠ relation.output.var

instance {n : Nat} (relation : Relation n) : Decidable relation.Independent := inferInstanceAs
  (Decidable (relation.left.var ≠ relation.output.var ∧ relation.right.var ≠ relation.output.var))

def Relation.holds {n : Nat} (relation : Relation n) (assignment : Nat → Bool) : Bool :=
  relation.output.eval assignment == (relation.left.eval assignment && relation.right.eval assignment)

def Relation.block {n : Nat} (relation : Relation n) : CNFFormula n :=
  [[relation.output,Alias.negate relation.left,Alias.negate relation.right],
   [Alias.negate relation.output,relation.left], [Alias.negate relation.output,relation.right]]

theorem Relation.block_eval {n : Nat} (relation : Relation n) (assignment : Nat → Bool) :
    CNFFormula.eval relation.block assignment = relation.holds assignment := by
  simp only [Relation.block, CNFFormula.eval, CNFClause.eval, List.all_cons, List.all_nil,
    List.any_cons, List.any_nil, Alias.negate_eval, Relation.holds]
  cases relation.output.eval assignment <;> cases relation.left.eval assignment <;>
    cases relation.right.eval assignment <;> rfl

def Relation.value {n : Nat} (relation : Relation n) (assignment : Nat → Bool) : Bool :=
  let accepted := relation.left.eval assignment && relation.right.eval assignment
  if relation.output.positive then accepted else !accepted

def Relation.bind {n : Nat} (relation : Relation n) (assignment : Nat → Bool) : Nat → Bool :=
  Function.update assignment relation.output.var.val (relation.value assignment)

theorem Relation.bind_other {n : Nat} (relation : Relation n) (assignment : Nat → Bool) (i : Nat)
    (other : i ≠ relation.output.var.val) : relation.bind assignment i = assignment i := by
  simp [Relation.bind, other]

theorem literal_bind_other {n : Nat} (relation : Relation n) (literal : CNFLiteral n)
    (other : literal.var ≠ relation.output.var) (assignment : Nat → Bool) :
    literal.eval (relation.bind assignment) = literal.eval assignment := by
  have different : literal.var.val ≠ relation.output.var.val := fun same => other (Fin.ext same)
  simp [CNFLiteral.eval, Relation.bind_other relation assignment _ different]

theorem Relation.bind_holds {n : Nat} (relation : Relation n) (independent : relation.Independent)
    (assignment : Nat → Bool) : relation.holds (relation.bind assignment) = true := by
  have output : relation.output.eval (relation.bind assignment) =
      (relation.left.eval assignment && relation.right.eval assignment) := by
    cases polarity : relation.output.positive <;>
      simp [CNFLiteral.eval, Relation.bind, Relation.value, polarity]
  rw [Relation.holds, output, literal_bind_other relation relation.left independent.1,
    literal_bind_other relation relation.right independent.2]
  simp

theorem Relation.bind_fixed {n : Nat} (relation : Relation n) (assignment : Nat → Bool)
    (holds : relation.holds assignment = true) : relation.bind assignment = assignment := by
  have value : relation.value assignment = assignment relation.output.var.val := by
    simp only [Relation.holds, beq_iff_eq, CNFLiteral.eval, Relation.value] at *
    cases output : relation.output.positive <;> simp_all
  funext i
  simp [Relation.bind, value]

theorem Relation.bind_fixed_iff {n : Nat} (relation : Relation n) (independent : relation.Independent)
    (assignment : Nat → Bool) : relation.bind assignment = assignment ↔ relation.holds assignment = true := by
  constructor
  · intro fixed
    simpa only [fixed] using relation.bind_holds independent assignment
  · exact relation.bind_fixed assignment

theorem Relation.bind_congr {n : Nat} (relation : Relation n) (independent : relation.Independent)
    (left right : Nat → Bool)
    (same : ∀ i, i ≠ relation.output.var.val → left i = right i) : relation.bind left = relation.bind right := by
  have a : relation.left.eval left = relation.left.eval right := by
    have different : relation.left.var.val ≠ relation.output.var.val := fun h => independent.1 (Fin.ext h)
    simp [CNFLiteral.eval, same _ different]
  have b : relation.right.eval left = relation.right.eval right := by
    have different : relation.right.var.val ≠ relation.output.var.val := fun h => independent.2 (Fin.ext h)
    simp [CNFLiteral.eval, same _ different]
  funext i
  by_cases output : i = relation.output.var.val
  · simp [Relation.bind, output, Relation.value, a, b]
  · simp [Relation.bind, output, same i output]

abbrev Free {n : Nat} (relation : Relation n) := { i : Fin n // i ≠ relation.output.var }
abbrev Parameters {n : Nat} (relation : Relation n) := Free relation → Bool

theorem Relation.free_card {n : Nat} (relation : Relation n) : Fintype.card (Free relation) = n - 1 := by
  change Fintype.card {i : Fin n // ¬ i = relation.output.var} = _
  rw [Fintype.card_subtype_compl]
  simp

def Relation.seed {n : Nat} (relation : Relation n) (parameters : Parameters relation) : Assignment n :=
  fun i => if equal : i = relation.output.var then false else parameters ⟨i,equal⟩

def Relation.project {n : Nat} (relation : Relation n) (assignment : Assignment n) : Parameters relation :=
  fun i => assignment i.val

def Relation.lift {n : Nat} (relation : Relation n) (parameters : Parameters relation) : Assignment n :=
  fun i => relation.bind (extendAssignment (relation.seed parameters)) i.val

theorem Relation.lift_other {n : Nat} (relation : Relation n) (parameters : Parameters relation)
    (i : Free relation) : relation.lift parameters i.val = parameters i := by
  have different : i.val.val ≠ relation.output.var.val := fun same => i.property (Fin.ext same)
  rw [Relation.lift, relation.bind_other _ _ different]
  simp [extendAssignment, i.val.isLt, Relation.seed, i.property]

theorem Relation.project_lift {n : Nat} (relation : Relation n) (parameters : Parameters relation) :
    relation.project (relation.lift parameters) = parameters := by
  funext i
  exact relation.lift_other parameters i

theorem Relation.lift_injective {n : Nat} (relation : Relation n) : Function.Injective relation.lift := by
  intro left right same
  simpa only [relation.project_lift] using congrArg relation.project same

theorem Relation.extend_lift {n : Nat} (relation : Relation n) (parameters : Parameters relation) :
    extendAssignment (relation.lift parameters) = relation.bind (extendAssignment (relation.seed parameters)) := by
  funext i
  by_cases inside : i < n
  · simp [extendAssignment, inside, Relation.lift]
  · have different : i ≠ relation.output.var.val := by have := relation.output.var.isLt; omega
    simp [extendAssignment, inside, relation.bind_other _ _ different]

theorem Relation.lift_holds {n : Nat} (relation : Relation n) (independent : relation.Independent)
    (parameters : Parameters relation) : relation.holds (extendAssignment (relation.lift parameters)) = true := by
  rw [relation.extend_lift]
  exact relation.bind_holds independent _

theorem Relation.lift_project {n : Nat} (relation : Relation n) (independent : relation.Independent)
    (assignment : Assignment n) (holds : relation.holds (extendAssignment assignment) = true) :
    relation.lift (relation.project assignment) = assignment := by
  have same : ∀ i, i ≠ relation.output.var.val →
      extendAssignment (relation.seed (relation.project assignment)) i = extendAssignment assignment i := by
    intro i different
    by_cases inside : i < n
    · have apart : (⟨i,inside⟩ : Fin n) ≠ relation.output.var := fun same => different (congrArg Fin.val same)
      simp [extendAssignment, inside, Relation.seed, Relation.project, apart]
    · simp [extendAssignment, inside]
  have recovered := (relation.bind_congr independent _ _ same).trans (relation.bind_fixed _ holds)
  funext i
  simpa only [Relation.lift, extendAssignment, i.isLt, ↓reduceDIte] using congrFun recovered i.val

theorem Relation.lift_image {n : Nat} (relation : Relation n) (independent : relation.Independent)
    (assignment : Assignment n) :
    (∃ parameters : Parameters relation, relation.lift parameters = assignment) ↔
      relation.holds (extendAssignment assignment) = true := by
  constructor
  · rintro ⟨parameters,rfl⟩
    exact relation.lift_holds independent parameters
  · intro holds
    exact ⟨relation.project assignment, relation.lift_project independent assignment holds⟩

def literalGate {n : Nat} (literal : CNFLiteral n) : Fragment :=
  if literal.positive then Fragment.input literal.var.val else (Fragment.input literal.var.val).not

theorem literalGate_eval {n : Nat} (literal : CNFLiteral n) (environment : Nat → Bool) :
    (literalGate literal).eval environment = bit (literal.eval environment) := by
  cases polarity : literal.positive <;>
    simp [literalGate, polarity, CNFLiteral.eval, Fragment.eval_not, truth_bit]

def Relation.gate {n : Nat} (relation : Relation n) : Fragment :=
  let both := (literalGate relation.left).and (literalGate relation.right)
  if relation.output.positive then both else both.not

theorem Relation.gate_eval {n : Nat} (relation : Relation n) (environment : Nat → Bool) :
    relation.gate.eval environment = bit (relation.value environment) := by
  cases polarity : relation.output.positive <;>
    simp [Relation.gate, Relation.value, polarity, literalGate_eval, truth_bit]

theorem literalGate_size {n : Nat} (literal : CNFLiteral n) : (literalGate literal).code.size ≤ 2 := by
  cases polarity : literal.positive <;>
    simp [literalGate, polarity, Fragment.input, Fragment.not, Fragment.unary]

theorem Relation.gate_size {n : Nat} (relation : Relation n) : relation.gate.code.size ≤ 6 := by
  have left := literalGate_size relation.left
  have right := literalGate_size relation.right
  cases polarity : relation.output.positive <;>
    simp only [Relation.gate, polarity, Bool.false_eq_true, if_false, if_true,
      Fragment.not, Fragment.unary, Fragment.and, Fragment.binary, Array.size_push,
      Array.size_append, Array.size_map] <;> omega

def factor {n : Nat} (relation : Relation n) (source : Source n) : Source n :=
  fun assignment => if relation.holds (extendAssignment assignment) then source assignment else 0

def zeroExtension {n : Nat} (relation : Relation n) (source : Parameters relation → ℚ) : Source n :=
  fun assignment => if relation.holds (extendAssignment assignment) then source (relation.project assignment) else 0

theorem Relation.factor_projector {n : Nat} (relation : Relation n) (source : Source n) :
    factor relation source = zeroProjector relation.block source := by
  funext assignment
  rw [zeroProjector_apply, relation.block_eval]
  rfl

theorem Relation.factor_lift {n : Nat} (relation : Relation n) (independent : relation.Independent)
    (source : Source n) : factor relation source = zeroExtension relation (source ∘ relation.lift) := by
  funext assignment
  by_cases holds : relation.holds (extendAssignment assignment) = true
  · simp [factor, zeroExtension, holds, relation.lift_project independent assignment holds]
  · simp [factor, zeroExtension, holds]

def test {n : Nat} (formula : CNFFormula n) (relation : Relation n) : Affine.Extract.Check :=
  if relation.Independent then
    let queried := Affine.Extract.allBlocks formula relation.block
    ⟨queried.accepted, queried.visits+4⟩
  else ⟨false,4⟩

theorem test_accepted {n : Nat} (formula : CNFFormula n) (relation : Relation n) :
    (test formula relation).accepted = true ↔
      relation.Independent ∧ (Affine.Extract.allBlocks formula relation.block).accepted = true := by
  by_cases independent : relation.Independent <;> simp [test, independent]

theorem test_entails {n : Nat} (formula : CNFFormula n) (relation : Relation n)
    (found : (test formula relation).accepted = true) (assignment : Nat → Bool)
    (satisfies : CNFFormula.eval formula assignment = true) : relation.holds assignment = true := by
  rw [← relation.block_eval]
  exact Affine.Extract.allBlocks_eval formula relation.block assignment satisfies ((test_accepted formula relation).mp found).2

/-- Field-comparison and source-list visits, including actual query/append scans.
Arithmetic on the counters and address bit operations are separate machine costs. -/
structure Result (n : Nat) where
  relations : List (Relation n)
  visits : Nat
  deriving Repr

def sweep {n : Nat} (formula : CNFFormula n) : List (Relation n) → Result n
  | [] => ⟨[],1⟩
  | relation :: rest =>
      let checked := test formula relation
      let next := sweep formula rest
      ⟨if checked.accepted then relation :: next.relations else next.relations,
        checked.visits + next.visits + 1⟩

theorem sweep_member {n : Nat} (formula : CNFFormula n) (relations : List (Relation n)) (relation : Relation n) :
    relation ∈ (sweep formula relations).relations ↔ relation ∈ relations ∧ (test formula relation).accepted = true := by
  induction relations with
  | nil => simp [sweep]
  | cons first rest ih =>
      cases accepted : (test formula first).accepted <;> simp [sweep, accepted, ih] <;> aesop

theorem sweep_length {n : Nat} (formula : CNFFormula n) (relations : List (Relation n)) :
    (sweep formula relations).relations.length ≤ relations.length := by
  induction relations with
  | nil => simp [sweep]
  | cons relation rest ih =>
      simp only [sweep, List.length_cons]
      split <;> simp_all
      omega

def candidates {n : Nat} : CNFClause n → List (Relation n)
  | [a,b,c] => [⟨a,Alias.negate b,Alias.negate c⟩,
      ⟨b,Alias.negate a,Alias.negate c⟩, ⟨c,Alias.negate a,Alias.negate b⟩]
  | _ => []

theorem candidates_length {n : Nat} (clause : CNFClause n) : (candidates clause).length ≤ 3 := by
  unfold candidates
  split <;> simp

def inspect {n : Nat} (formula : CNFFormula n) (clause : CNFClause n) : Result n :=
  let result := sweep formula (candidates clause)
  ⟨result.relations,result.visits+4⟩

theorem inspect_length {n : Nat} (formula : CNFFormula n) (clause : CNFClause n) :
    (inspect formula clause).relations.length ≤ 3 :=
  (sweep_length formula (candidates clause)).trans (candidates_length clause)

def scan {n : Nat} (formula : CNFFormula n) : CNFFormula n → Result n
  | [] => ⟨[],1⟩
  | clause :: rest =>
      let first := inspect formula clause
      let next := scan formula rest
      ⟨first.relations ++ next.relations, first.visits + next.visits + first.relations.length + 1⟩

def run {n : Nat} (formula : CNFFormula n) : Result n := scan formula formula

def extract {n : Nat} (formula : CNFFormula n) : List (Relation n) := (run formula).relations

theorem scan_member {n : Nat} (formula anchors : CNFFormula n) (relation : Relation n) :
    relation ∈ (scan formula anchors).relations ↔
      ∃ clause ∈ anchors, relation ∈ candidates clause ∧ (test formula relation).accepted = true := by
  induction anchors with
  | nil => simp [scan]
  | cons clause rest ih =>
      simp only [scan, inspect, List.mem_append, sweep_member, ih, List.mem_cons]
      aesop

theorem extract_origin {n : Nat} (formula : CNFFormula n) (relation : Relation n)
    (generated : relation ∈ extract formula) :
    ∃ clause ∈ formula, relation ∈ candidates clause ∧ (test formula relation).accepted = true :=
  (scan_member formula formula relation).mp generated

theorem extract_independent {n : Nat} (formula : CNFFormula n) (relation : Relation n)
    (generated : relation ∈ extract formula) : relation.Independent := by
  obtain ⟨_,_,_,found⟩ := extract_origin formula relation generated
  exact ((test_accepted formula relation).mp found).1

theorem extract_entails {n : Nat} (formula : CNFFormula n) (relation : Relation n)
    (generated : relation ∈ extract formula) (assignment : Nat → Bool)
    (satisfies : CNFFormula.eval formula assignment = true) : relation.holds assignment = true := by
  obtain ⟨_,_,_,found⟩ := extract_origin formula relation generated
  exact test_entails formula relation found assignment satisfies

theorem scan_length {n : Nat} (formula anchors : CNFFormula n) :
    (scan formula anchors).relations.length ≤ 3 * anchors.length := by
  induction anchors with
  | nil => simp [scan]
  | cons clause rest ih =>
      have first := inspect_length formula clause
      simp only [scan, List.length_append, List.length_cons]
      omega

theorem extract_length {n : Nat} (formula : CNFFormula n) : (extract formula).length ≤ 3 * formula.length :=
  scan_length formula formula

theorem candidates_source {n : Nat} (clause : CNFClause n) (relation : Relation n)
    (generated : relation ∈ candidates clause) :
    relation.output ∈ clause ∧ Alias.negate relation.left ∈ clause ∧ Alias.negate relation.right ∈ clause := by
  unfold candidates at generated
  split at generated
  · rename_i a b c
    simp only [List.mem_cons, List.not_mem_nil, or_false] at generated
    rcases generated with rfl | rfl | rfl <;> simp [Alias.negate]
  · cases generated

theorem extract_source {n : Nat} (formula : CNFFormula n) (relation : Relation n)
    (generated : relation ∈ extract formula) :
    ∃ clause ∈ formula, relation.output ∈ clause ∧ Alias.negate relation.left ∈ clause ∧
      Alias.negate relation.right ∈ clause := by
  obtain ⟨clause,member,candidate,_⟩ := extract_origin formula relation generated
  exact ⟨clause,member,candidates_source clause relation candidate⟩

theorem Relation.addresses {n : Nat} (relation : Relation n) :
    relation.output.var.val < n ∧ relation.left.var.val < n ∧ relation.right.var.val < n :=
  ⟨relation.output.var.isLt,relation.left.var.isLt,relation.right.var.isLt⟩

theorem test_visits {n : Nat} (formula : CNFFormula n) (relation : Relation n) :
    (test formula relation).visits ≤ 42 * Affine.Extract.literalCount formula + 30 * formula.length + 11 := by
  have bounded := Affine.Extract.allBlocks_visits formula relation.block (by simp [Relation.block])
  change (Affine.Extract.allBlocks formula relation.block).visits ≤
    3 * (14 * Affine.Extract.literalCount formula + 10 * formula.length + 2) + 1 at bounded
  unfold test
  split <;> dsimp only <;> omega

theorem sweep_visits {n : Nat} (formula : CNFFormula n) (relations : List (Relation n)) :
    (sweep formula relations).visits ≤
      relations.length * (42 * Affine.Extract.literalCount formula + 30 * formula.length + 12) + 1 := by
  induction relations with
  | nil => simp [sweep]
  | cons relation rest ih =>
      have first := test_visits formula relation
      simp only [sweep, List.length_cons]
      nlinarith

theorem inspect_visits {n : Nat} (formula : CNFFormula n) (clause : CNFClause n) :
    (inspect formula clause).visits ≤ 126 * Affine.Extract.literalCount formula + 90 * formula.length + 41 := by
  have bound := sweep_visits formula (candidates clause)
  have width := candidates_length clause
  simp only [inspect]
  nlinarith

theorem scan_visits {n : Nat} (formula anchors : CNFFormula n) :
    (scan formula anchors).visits ≤
      anchors.length * (126 * Affine.Extract.literalCount formula + 90 * formula.length + 45) + 1 := by
  induction anchors with
  | nil => simp [scan]
  | cons clause rest ih =>
      have head := inspect_visits formula clause
      have short := inspect_length formula clause
      simp only [scan, List.length_cons]
      nlinarith

theorem run_visits {n : Nat} (formula : CNFFormula n) :
    (run formula).visits ≤ formula.length * (126 * Affine.Extract.literalCount formula + 90 * formula.length + 45) + 1 :=
  scan_visits formula formula

theorem extract_block {n : Nat} (formula : CNFFormula n) (relation : Relation n)
    (independent : relation.Independent) (present : ∀ clause ∈ relation.block, clause ∈ formula) :
    relation ∈ extract formula := by
  apply (scan_member formula formula relation).mpr
  refine ⟨[relation.output,Alias.negate relation.left,Alias.negate relation.right],
    present _ (by simp [Relation.block]), ?_, ?_⟩
  · simp [candidates, Alias.negate]
  · exact (test_accepted formula relation).mpr ⟨independent, Affine.Extract.allBlocks_of_subset formula _ present⟩

theorem generated_projector {n : Nat} (formula : CNFFormula n) (relation : Relation n)
    (generated : relation ∈ extract formula) (source : Source n) :
    zeroProjector formula source = zeroExtension relation (zeroProjector formula source ∘ relation.lift) := by
  have independent := extract_independent formula relation generated
  funext assignment
  by_cases holds : relation.holds (extendAssignment assignment) = true
  · simp [zeroExtension, holds, relation.lift_project independent assignment holds]
  · have rejected : CNFFormula.eval formula (extendAssignment assignment) ≠ true :=
      fun accepted => holds (extract_entails formula relation generated _ accepted)
    simp [zeroExtension, holds, zeroProjector_apply, rejected]

theorem generated_satisfiable {n : Nat} (formula : CNFFormula n) (relation : Relation n)
    (generated : relation ∈ extract formula) : CNFSatisfiable formula ↔
      ∃ parameters : Parameters relation, CNFFormula.eval formula (extendAssignment (relation.lift parameters)) = true := by
  rw [satisfiable_iff_finite_assignment]
  constructor
  · rintro ⟨assignment,accepted⟩
    have holds := extract_entails formula relation generated _ accepted
    exact ⟨relation.project assignment, by
      rw [relation.lift_project (extract_independent formula relation generated) assignment holds]
      exact accepted⟩
  · rintro ⟨parameters,accepted⟩
    exact ⟨relation.lift parameters,accepted⟩

end SaturationMonoid.ComplexityProjection.SATSource.FunctionalRelations
