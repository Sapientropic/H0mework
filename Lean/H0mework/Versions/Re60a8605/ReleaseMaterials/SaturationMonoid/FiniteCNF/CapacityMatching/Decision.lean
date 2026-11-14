import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.CapacityMatching.SourceCost
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.SignedCapacity

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching.Decision

def possible {n : Nat} (formula : CNFFormula n) : Bool :=
  (SourceCost.run formula).value && (SourceCost.run (SignedCapacity.expand formula)).value

theorem possible_of_satisfied {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) : possible formula = true := by
  rw [possible,SourceCost.run_value,SourceCost.run_value,Source.possible_of_satisfied formula assignment accepted,
    Source.possible_of_satisfied (SignedCapacity.expand formula) (SignedCapacity.lift n assignment)
      ((SignedCapacity.expand_lift formula assignment).trans accepted)]
  rfl

theorem rejected_unsatisfiable {n : Nat} (formula : CNFFormula n) (rejected : possible formula = false) :
    ¬ CNFSatisfiable formula := by
  rintro ⟨assignment,accepted⟩
  have result := possible_of_satisfied formula assignment accepted
  rw [rejected] at result
  cases result

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  if possible formula then SignedCapacity.decideFormula formula else false

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  unfold decideFormula
  split
  · exact SignedCapacity.decideFormula_correct formula
  · rename_i rejected
    simp [rejected_unsatisfiable formula (Bool.eq_false_iff.mpr rejected)]

def read {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) : Bool :=
  if possible formula then SignedCapacity.read n formula assignment else false

theorem read_value {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) :
    read formula assignment = CNFFormula.eval formula assignment := by
  unfold read
  split
  · exact SignedCapacity.read_value formula assignment
  · rename_i rejected
    apply Eq.symm
    apply Bool.eq_false_iff.mpr
    exact fun accepted => rejected (possible_of_satisfied formula assignment accepted)

def sourceAction {n : Nat} (formula : CNFFormula n)
    (source : SaturationMonoid.ComplexityProjection.SATSource.Source n) :
    SaturationMonoid.ComplexityProjection.SATSource.Source n :=
  fun assignment => if read formula (extendAssignment assignment) then source assignment else 0

theorem original_projector {n : Nat} (formula : CNFFormula n)
    (source : SaturationMonoid.ComplexityProjection.SATSource.Source n) :
    zeroProjector formula source = sourceAction formula source := by
  funext assignment
  simp only [zeroProjector_apply,sourceAction,read_value]

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

theorem decideBits_no (bits : List Bool) :
    decideBits bits = false ↔ ¬ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧ CNFSatisfiable input.2 := by
  rw [decideBits_eq_original,Encoding.decideBits_no]

theorem decideBits_invalid (bits : List Bool) (invalid : Encoding.parse bits = none) : decideBits bits = false := by
  simp [decideBits,invalid]

end SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching.Decision
