import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineCollect.Cost

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineJointCover

open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineCarrier (Cells Valid Separated read)

def hull (n : Nat) : Cells → Result
  | [] => .contradiction
  | basis::rest => BranchImage.join n (.basis basis) (hull n rest)

def volume (n : Nat) (cells : Cells) : Nat := (cells.map (fun basis => 2^(freeIndices n basis).length)).sum

def compact (n : Nat) (cells : Cells) : Cells :=
  match hull n cells with
  | .contradiction => []
  | .basis basis => if volume n cells == 2^(freeIndices n basis).length then [basis] else cells

theorem hull_valid (n : Nat) (cells : Cells) (valid : Valid n cells) :
    (hull n cells).within n ∧ (hull n cells).triangular := by
  induction cells with
  | nil => exact ⟨True.intro,True.intro⟩
  | cons basis rest ih =>
      have first := valid basis (by simp)
      have tail := ih (fun b member => valid b (by simp [member]))
      exact BranchImage.join_invariants n (.basis basis) (hull n rest) first.2 first.1 tail.1 tail.2

theorem hull_covers (n : Nat) (cells : Cells) (valid : Valid n cells) (assignment : Nat → Bool)
    (accepted : read cells assignment = true) : (hull n cells).holds assignment = true := by
  induction cells with
  | nil => cases accepted
  | cons basis rest ih =>
      have first := valid basis (by simp)
      have tailValid : Valid n rest := fun b member => valid b (by simp [member])
      have tail := hull_valid n rest tailValid
      apply BranchImage.join_covers n (.basis basis) (hull n rest) first.2 first.1 tail.1 tail.2 assignment
      have alternatives : holds basis assignment = true ∨ read rest assignment = true := by simpa using accepted
      rcases alternatives with yes | later
      · exact Or.inl yes
      · exact Or.inr (ih tailValid later)

noncomputable def points (n : Nat) (basis : List Row) : Finset (Assignment n) := by
  classical
  exact Finset.univ.filter (fun x => holds basis (extendAssignment x) = true)

noncomputable def carrierPoints (n : Nat) (cells : Cells) : Finset (Assignment n) := by
  classical
  exact Finset.univ.filter (fun x => read cells (extendAssignment x) = true)

theorem points_card (n : Nat) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    (points n basis).card = 2^(freeIndices n basis).length := by
  classical
  let equivalence : Assignment (freeIndices n basis).length ≃
      {x : Assignment n // holds basis (extendAssignment x) = true} :=
    { toFun := fun parameter => ⟨parameterLift n basis parameter,parameterLift_holds n basis valid.1 valid.2 parameter⟩
      invFun := fun x => projectFree n basis x.val
      left_inv := projectFree_parameterLift n basis
      right_inv := fun x => Subtype.ext (parameterLift_projectFree n basis valid.1 x.val x.property) }
  have same : Fintype.card {x : Assignment n // holds basis (extendAssignment x) = true} = (points n basis).card := by
    apply Fintype.card_of_subtype
    intro x
    simp [points]
  rw [← same,← Fintype.card_congr equivalence]
  simp [Assignment]

theorem carrierPoints_cons (n : Nat) (basis : List Row) (rest : Cells) :
    carrierPoints n (basis::rest) = points n basis ∪ carrierPoints n rest := by
  classical
  ext x
  simp [carrierPoints,points,AffineCarrier.read]

theorem carrierPoints_card (n : Nat) (cells : Cells) (valid : Valid n cells) (separated : Separated cells) :
    (carrierPoints n cells).card = volume n cells := by
  classical
  induction cells with
  | nil => simp [carrierPoints,AffineCarrier.read,volume]
  | cons basis rest ih =>
      have first := valid basis (by simp)
      have tailValid : Valid n rest := fun b member => valid b (by simp [member])
      have tailSeparated := (List.pairwise_cons.mp separated).2
      have disjoint : Disjoint (points n basis) (carrierPoints n rest) := by
        apply Finset.disjoint_left.mpr
        intro x left right
        have headTrue : holds basis (extendAssignment x) = true := (Finset.mem_filter.mp left).2
        have tailTrue : read rest (extendAssignment x) = true := (Finset.mem_filter.mp right).2
        have impossible := AffineCarrier.separated_cons basis rest separated (extendAssignment x)
        rw [headTrue,tailTrue] at impossible
        cases impossible
      rw [carrierPoints_cons,Finset.card_union_of_disjoint disjoint,points_card n basis first,ih tailValid tailSeparated]
      rfl

theorem volume_covers (n : Nat) (cells : Cells) (valid : Valid n cells) (separated : Separated cells)
    (basis : List Row) (generated : hull n cells = .basis basis)
    (filled : volume n cells = 2^(freeIndices n basis).length) :
    ∀ assignment : Assignment n, holds basis (extendAssignment assignment) = read cells (extendAssignment assignment) := by
  classical
  have basisValid : Triangular basis ∧ RowsWithin n basis := by
    have facts := hull_valid n cells valid
    simpa only [generated,Result.within,Result.triangular] using facts.symm
  have subset : carrierPoints n cells ⊆ points n basis := by
    intro x member
    have accepted : read cells (extendAssignment x) = true := (Finset.mem_filter.mp member).2
    have contained := hull_covers n cells valid (extendAssignment x) accepted
    simpa only [points,Finset.mem_filter,Finset.mem_univ,true_and,generated,Result.holds] using contained
  have counts : (carrierPoints n cells).card = (points n basis).card := by
    rw [carrierPoints_card n cells valid separated,points_card n basis basisValid,filled]
  have equal := Finset.eq_of_subset_of_card_le subset counts.symm.le
  intro assignment
  apply Bool.eq_iff_iff.mpr
  have member := Finset.ext_iff.mp equal assignment
  simpa only [carrierPoints,points,Finset.mem_filter,Finset.mem_univ,true_and] using member.symm

theorem compact_valid (n : Nat) (cells : Cells) (valid : Valid n cells) : Valid n (compact n cells) := by
  have facts := hull_valid n cells valid
  cases generated : hull n cells with
  | contradiction => simp [compact,generated,Valid]
  | basis basis =>
      rw [generated] at facts
      simp only [compact,generated]
      split
      · intro b member
        have same : b=basis := List.mem_singleton.mp member
        exact same ▸ facts.symm
      · exact valid

theorem compact_separated (n : Nat) (cells : Cells) (separated : Separated cells) : Separated (compact n cells) := by
  cases generated : hull n cells with
  | contradiction => simp [compact,generated,Separated]
  | basis basis =>
      simp only [compact,generated]
      split
      · simp [Separated]
      · exact separated

theorem compact_read (n : Nat) (cells : Cells) (valid : Valid n cells) (separated : Separated cells) (assignment : Assignment n) :
    read (compact n cells) (extendAssignment assignment) = read cells (extendAssignment assignment) := by
  cases generated : hull n cells with
  | contradiction =>
      have no : read cells (extendAssignment assignment) = false := by
        apply Bool.eq_false_iff.mpr
        intro accepted
        have impossible := hull_covers n cells valid _ accepted
        rw [generated] at impossible
        cases impossible
      simp [compact,generated,no]
  | basis basis =>
      by_cases full : volume n cells = 2^(freeIndices n basis).length
      · have exactRead := volume_covers n cells valid separated basis generated full assignment
        simpa [compact,generated,full,AffineCarrier.read] using exactRead
      · simp [compact,generated,full]

def run {n : Nat} : CNFFormula n → Cells → Cells
  | [],cells => cells
  | clause::rest,cells =>
      let next := (AffineCarrier.clauseAction clause cells).value
      run rest (compact n next)

theorem run_valid {n : Nat} (formula : CNFFormula n) (cells : Cells) (valid : Valid n cells) : Valid n (run formula cells) := by
  induction formula generalizing cells with
  | nil => exact valid
  | cons clause rest ih => exact ih _ (compact_valid n _ (AffineCarrier.clauseAction_valid clause cells valid))

theorem run_separated {n : Nat} (formula : CNFFormula n) (cells : Cells) (separated : Separated cells) : Separated (run formula cells) := by
  induction formula generalizing cells with
  | nil => exact separated
  | cons clause rest ih => exact ih _ (compact_separated n _ (AffineCarrier.clauseAction_separated clause cells separated))

theorem run_read {n : Nat} (formula : CNFFormula n) (cells : Cells) (valid : Valid n cells)
    (separated : Separated cells) (assignment : Assignment n) :
    read (run formula cells) (extendAssignment assignment) =
      (read cells (extendAssignment assignment) && CNFFormula.eval formula (extendAssignment assignment)) := by
  induction formula generalizing cells with
  | nil => simp [run,CNFFormula.eval]
  | cons clause rest ih =>
      have nextValid := AffineCarrier.clauseAction_valid clause cells valid
      have nextSeparated := AffineCarrier.clauseAction_separated clause cells separated
      rw [run,ih _ (compact_valid n _ nextValid) (compact_separated n _ nextSeparated),compact_read n _ nextValid nextSeparated,
        AffineCarrier.clauseAction_read]
      simp [CNFFormula.eval,Bool.and_assoc]

def generate {n : Nat} (formula : CNFFormula n) : Cells := run formula (AffineCarrier.seed formula).value

theorem generate_valid {n : Nat} (formula : CNFFormula n) : Valid n (generate formula) :=
  run_valid formula _ (AffineCarrier.seed_valid formula)

theorem seed_separated {n : Nat} (formula : CNFFormula n) : Separated (AffineCarrier.seed formula).value := by
  rw [AffineCarrier.seed_result]
  exact AffineCarrier.pack_separated _

theorem generate_read {n : Nat} (formula : CNFFormula n) (assignment : Assignment n) :
    read (generate formula) (extendAssignment assignment) = CNFFormula.eval formula (extendAssignment assignment) := by
  rw [generate,run_read formula _ (AffineCarrier.seed_valid formula) (seed_separated formula)]
  by_cases accepted : CNFFormula.eval formula (extendAssignment assignment) = true
  · rw [AffineCarrier.seed_entails formula _ accepted,accepted]
    rfl
  · simp [Bool.eq_false_iff.mpr accepted]

theorem generate_image {n : Nat} (formula : CNFFormula n) (assignment : Assignment n) :
    (∃ parameter : AffineCarrier.Parameters n (generate formula),
      AffineCarrier.lift n (generate formula) parameter = assignment) ↔
        CNFFormula.eval formula (extendAssignment assignment) = true := by
  rw [AffineCarrier.lift_image n _ (generate_valid formula),generate_read]

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool := !(generate formula).isEmpty

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) : decideFormula formula = true ↔ CNFSatisfiable formula := by
  rw [decideFormula,AffineCarrier.nonempty_iff n _ (generate_valid formula)]
  simp only [generate_read]
  constructor
  · rintro ⟨assignment,accepted⟩
    exact ⟨extendAssignment assignment,accepted⟩
  · rintro ⟨assignment,accepted⟩
    exact ⟨(fun i => assignment i.val),(formula_eval_restrict formula assignment).trans accepted⟩

def sourceAction {n : Nat} (formula : CNFFormula n) (source : Source n) : Source n :=
  fun assignment => if read (generate formula) (extendAssignment assignment) then source assignment else 0

theorem original_projector {n : Nat} (formula : CNFFormula n) (source : Source n) :
    zeroProjector formula source = sourceAction formula source := by
  funext assignment
  simp only [zeroProjector_apply,sourceAction,generate_read]

def decideBits (bits : List Bool) : Bool :=
  match Encoding.parse bits with
  | none => false
  | some input => decideFormula input.2

theorem decideBits_eq_original (bits : List Bool) : decideBits bits = Encoding.decideBits bits := by
  cases parsed : Encoding.parse bits with
  | none => simp [decideBits,Encoding.decideBits,parsed]
  | some input =>
      simp only [decideBits,Encoding.decideBits,parsed]
      apply Bool.eq_iff_iff.mpr
      rw [decideFormula_correct,Dense.decideFormula_correct]

theorem decideBits_iff_rootVerify (bits : List Bool) :
    decideBits bits = true ↔ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧
      ∃ assignment : Nat → Bool, CNFSATVerify input.2 (CNFSATNode.root input.1) assignment := by
  rw [decideBits_eq_original,Encoding.decideBits_iff_rootVerify]

end SaturationMonoid.ComplexityProjection.SATSource.AffineJointCover
