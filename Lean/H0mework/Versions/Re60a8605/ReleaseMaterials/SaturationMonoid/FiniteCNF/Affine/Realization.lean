import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Decision

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine

/-- The compiled original gates act on an arbitrary source carried by the generated coordinates. -/
def gateAction {n freeWidth : Nat} (formula : CNFFormula n) (coordinates : Array Row)
    (source : Source n) : Source freeWidth :=
  fun parameters =>
    ((Acceptance.compile coordinates formula).eval (extendAssignment parameters) : ℚ) *
      source (Gates.lift n coordinates parameters)

theorem gateAction_residual {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : eliminate (Extract.extract formula) = .basis basis) (source : Source n) :
    gateAction formula (Table.coordinates n basis) source =
      residualProjector formula basis (source ∘ parameterLift n basis) := by
  funext parameters
  rw [gateAction, Acceptance.eval_compile]
  have value := formula_eval_restrict formula
    (Gates.coordinate (Table.coordinates n basis) (extendAssignment parameters))
  change CNFFormula.eval formula (extendAssignment (Gates.lift n (Table.coordinates n basis) parameters)) = _ at value
  rw [← value, Decision.table_lift n basis (extracted_basis_within formula basis generated)]
  simp only [residualProjector, Function.comp_apply, InterferenceProgram.bit]
  split <;> simp_all

theorem original_projector_compiled_gates {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : eliminate (Extract.extract formula) = .basis basis) (source : Source n) :
    zeroProjector formula source = freeZeroExtension n basis
      (gateAction formula (Table.coordinates n basis) source) := by
  rw [gateAction_residual formula basis generated]
  exact original_projector_zeroExtension formula basis generated source

end SaturationMonoid.ComplexityProjection.SATSource.Affine
