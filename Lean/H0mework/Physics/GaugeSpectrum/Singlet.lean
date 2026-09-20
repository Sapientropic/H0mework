import H0mework.Physics.GaugeSpectrum.Cubic

/-! The color trace of the calculated cubic generates a full-carrier
SU(7)-singlet action. Its compression recovers the actual cubic exactly;
no claim identifies it with the cubic on unoccupied ambient components. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open SU7ExteriorMatterRepresentation
open scoped Kronecker

noncomputable section

def cubicSpinMatrix (point : BasePoint) : Matrix DiracSpinorIndex DiracSpinorIndex ℂ :=
  fun row column => (∑ color : Fin 2, cubic point (row, color) (column, color)) / 2

def singletAction (point : BasePoint) : Module.End ℂ DiracExteriorMatterCarrier :=
  diracMatrixMatterAction (cubicSpinMatrix point)

theorem cubicSpinMatrix_normalForm (point : BasePoint) :
    cubicSpinMatrix point = ((curvatureScale : ℂ) ^ 3) • exchange := by
  ext row column
  simp [cubicSpinMatrix, cubic_normalForm]

theorem compression_diracMatrix (matrix : Matrix DiracSpinorIndex DiracSpinorIndex ℂ) :
    compression (diracMatrixMatterAction matrix) = matrix ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  apply Matrix.ext
  intro row column
  rcases row with ⟨spin, color⟩
  rcases column with ⟨other, input⟩
  simp only [compression, LinearMap.toMatrix'_apply, LinearMap.comp_apply, coordinates, embed,
    LinearMap.coe_mk, AddHom.coe_mk, sourceColorDoubletDual_diracMatrix]
  by_cases same : color = input
  · subst input
    simp [Pi.single_apply, Prod.mk.injEq]
  · simp [Prod.mk.injEq, same]

theorem singletAction_recovers_cubic (point : BasePoint) :
    compression (singletAction point) = cubic point := by
  rw [singletAction, compression_diracMatrix, cubicSpinMatrix_normalForm, cubic_normalForm]
  exact Matrix.smul_kronecker _ _ _

theorem singletAction_fullSU7 (point : BasePoint) (element : SU7MotherGroup)
    (matter : DiracExteriorMatterCarrier) :
    singletAction point (diracExteriorMatterGaugeRepresentation element matter) =
      diracExteriorMatterGaugeRepresentation element (singletAction point matter) :=
  congrArg (fun action : Module.End ℂ DiracExteriorMatterCarrier => action matter)
    (diracMatrixMatterAction_commutes_internal (cubicSpinMatrix point)
      (su7ExteriorSpinorMatterRepresentation element))

theorem singletAction_from_actual_cubic (point : BasePoint) (values : Source.Index → ℂ) :
    coordinates (singletAction point (embed values)) = cubic point *ᵥ values := by
  rw [← compression_mulVec, singletAction_recovers_cubic]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
