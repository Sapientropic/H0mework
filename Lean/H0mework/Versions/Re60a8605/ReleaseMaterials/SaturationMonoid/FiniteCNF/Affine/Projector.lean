import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Lift
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Gates

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine

def freeZeroExtension (n : Nat) (basis : List Row)
    (source : Source (freeIndices n basis).length) : Source n :=
  fun assignment => if holds basis (extendAssignment assignment) = true
    then source (projectFree n basis assignment) else 0

/-- Every original clause is evaluated on the generated lift; nonlinear gates remain intact. -/
def residualProjector {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (source : Source (freeIndices n basis).length) : Source (freeIndices n basis).length :=
  fun parameters => if CNFFormula.eval formula
    (extendAssignment (parameterLift n basis parameters)) = true then source parameters else 0

theorem extracted_contradiction_eval {n : Nat} (formula : CNFFormula n)
    (generated : eliminate (Extract.extract formula) = .contradiction) (assignment : Nat → Bool) :
    CNFFormula.eval formula assignment = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have relation := Extract.extract_entails formula assignment accepted
  rw [contradiction_unsatisfiable (Extract.extract formula) generated assignment] at relation
  exact Bool.noConfusion relation

theorem extracted_contradiction_projector {n : Nat} (formula : CNFFormula n)
    (generated : eliminate (Extract.extract formula) = .contradiction) : zeroProjector formula = 0 := by
  apply LinearMap.ext
  intro source
  funext assignment
  rw [zeroProjector_apply, extracted_contradiction_eval formula generated]
  rfl

theorem original_projector_zeroExtension {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : eliminate (Extract.extract formula) = .basis basis) (source : Source n) :
    zeroProjector formula source = freeZeroExtension n basis
      (residualProjector formula basis (source ∘ parameterLift n basis)) := by
  have triangular := eliminate_triangular (Extract.extract formula)
  rw [generated] at triangular
  funext assignment
  rw [zeroProjector_apply]
  by_cases accepted : holds basis (extendAssignment assignment) = true
  · have recovery := parameterLift_projectFree n basis triangular assignment accepted
    simp only [freeZeroExtension, if_pos accepted, residualProjector, Function.comp_apply, recovery]
  · have rejected : CNFFormula.eval formula (extendAssignment assignment) ≠ true := by
      intro satisfies
      apply accepted
      rw [basis_solutions (Extract.extract formula) basis generated]
      exact Extract.extract_entails formula _ satisfies
    simp [freeZeroExtension, accepted, rejected]

theorem satisfiable_iff_free {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : eliminate (Extract.extract formula) = .basis basis) :
    CNFSatisfiable formula ↔ ∃ parameters : Assignment (freeIndices n basis).length,
      CNFFormula.eval formula (extendAssignment (parameterLift n basis parameters)) = true := by
  rw [satisfiable_iff_finite_assignment]
  constructor
  · rintro ⟨assignment, accepted⟩
    have relations := Extract.extract_entails formula (extendAssignment assignment) accepted
    obtain ⟨parameters, recovered⟩ := (extracted_parameterLift_image formula basis generated assignment).mpr relations
    exact ⟨parameters, by simpa only [recovered] using accepted⟩
  · rintro ⟨parameters, accepted⟩
    exact ⟨parameterLift n basis parameters, accepted⟩

end SaturationMonoid.ComplexityProjection.SATSource.Affine
