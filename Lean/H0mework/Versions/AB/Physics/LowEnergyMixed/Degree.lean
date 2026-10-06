import H0mework.Versions.AB.Physics.LowEnergyQuantum.Carrier

/-! The original exterior grading of the frozen-connection matter symbol. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.MixedSymbol
open DiracCliffordRepresentation DiracExteriorMatterAction
open SU7ExteriorMatterRepresentation SU7ExteriorBreakingYukawa
open StageNineHolonomicField StageNineDiracDualYukawaSpinJurisdiction
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource
noncomputable section

def degreeSix : Module.End ℂ DiracExteriorMatterCarrier where
  toFun field := fun spin => ((field spin).1, 0, 0)
  map_add' := by intros; funext spin; simp
  map_smul' := by intros; funext spin; simp

def degreeTwo : Module.End ℂ DiracExteriorMatterCarrier where
  toFun field := fun spin => (0, (field spin).2.1, 0)
  map_add' := by intros; funext spin; simp
  map_smul' := by intros; funext spin; simp

def degreeFour : Module.End ℂ DiracExteriorMatterCarrier where
  toFun field := fun spin => (0, 0, (field spin).2.2)
  map_add' := by intros; funext spin; simp
  map_smul' := by intros; funext spin; simp

theorem degree_sum : degreeSix + degreeTwo + degreeFour = LinearMap.id := by
  apply LinearMap.ext
  intro field
  funext spin
  simp [degreeSix, degreeTwo, degreeFour]

theorem degreeSix_spin (matrix : DiracMatrix) :
    degreeSix.comp (diracMatrixMatterAction matrix) =
      (diracMatrixMatterAction matrix).comp degreeSix := by
  apply LinearMap.ext
  intro field
  funext spin
  simp [degreeSix, diracMatrixMatterAction, Fin.sum_univ_four]

theorem degreeTwo_spin (matrix : DiracMatrix) :
    degreeTwo.comp (diracMatrixMatterAction matrix) =
      (diracMatrixMatterAction matrix).comp degreeTwo := by
  apply LinearMap.ext
  intro field
  funext spin
  simp [degreeTwo, diracMatrixMatterAction, Fin.sum_univ_four]

theorem degreeFour_spin (matrix : DiracMatrix) :
    degreeFour.comp (diracMatrixMatterAction matrix) =
      (diracMatrixMatterAction matrix).comp degreeFour := by
  apply LinearMap.ext
  intro field
  funext spin
  simp [degreeFour, diracMatrixMatterAction, Fin.sum_univ_four]

theorem degreeSix_gauge (matrix : SU7MotherLieAlgebra.SU7MotherLieMatrix) :
    degreeSix.comp (diracExteriorMotherLieAction matrix) =
      (diracExteriorMotherLieAction matrix).comp degreeSix := by
  apply LinearMap.ext
  intro field
  funext spin
  simp [degreeSix, diracExteriorMotherLieAction, internalMatterLinearAction,
    exteriorSpinorMotherLieAction]

theorem degreeTwo_gauge (matrix : SU7MotherLieAlgebra.SU7MotherLieMatrix) :
    degreeTwo.comp (diracExteriorMotherLieAction matrix) =
      (diracExteriorMotherLieAction matrix).comp degreeTwo := by
  apply LinearMap.ext
  intro field
  funext spin
  simp [degreeTwo, diracExteriorMotherLieAction, internalMatterLinearAction,
    exteriorSpinorMotherLieAction]

theorem degreeFour_gauge (matrix : SU7MotherLieAlgebra.SU7MotherLieMatrix) :
    degreeFour.comp (diracExteriorMotherLieAction matrix) =
      (diracExteriorMotherLieAction matrix).comp degreeFour := by
  apply LinearMap.ext
  intro field
  funext spin
  simp [degreeFour, diracExteriorMotherLieAction, internalMatterLinearAction,
    exteriorSpinorMotherLieAction]

theorem yukawa_output (scalar : ExteriorBreakingScalarCarrier) :
    degreeSix.comp (diracDualRightChiralYukawaAction scalar) =
      diracDualRightChiralYukawaAction scalar := by
  apply LinearMap.ext
  intro field
  funext spin
  apply Prod.ext
  · rfl
  · rfl

theorem yukawa_input (scalar : ExteriorBreakingScalarCarrier) :
    (diracDualRightChiralYukawaAction scalar).comp degreeTwo =
      diracDualRightChiralYukawaAction scalar := by
  apply LinearMap.ext
  intro field
  funext spin
  simp [diracDualRightChiralYukawaAction, diracExteriorYukawaInternalAction,
    internalMatterLinearAction, exteriorYukawaInternalAction,
    degreeTwo, diracMatrixMatterAction, Fin.sum_univ_four]

theorem yukawa_degreeSix (scalar : ExteriorBreakingScalarCarrier) :
    (diracDualRightChiralYukawaAction scalar).comp degreeSix = 0 := by
  apply LinearMap.ext
  intro field
  exact Response.Yukawa.apply_eq_zero_of_degree_two_zero scalar _ (fun _ => rfl)

theorem yukawa_degreeFour (scalar : ExteriorBreakingScalarCarrier) :
    (diracDualRightChiralYukawaAction scalar).comp degreeFour = 0 := by
  apply LinearMap.ext
  intro field
  exact Response.Yukawa.apply_eq_zero_of_degree_two_zero scalar _ (fun _ => rfl)

/-- Insert any grading-preserving propagator: the two Yukawa insertions still vanish. -/
theorem yukawa_propagator_yukawa
    (first second : ExteriorBreakingScalarCarrier)
    (propagator : Module.End ℂ DiracExteriorMatterCarrier)
    (preserves : degreeSix.comp propagator = propagator.comp degreeSix) :
    (diracDualRightChiralYukawaAction first).comp
      (propagator.comp (diracDualRightChiralYukawaAction second)) = 0 := by
  apply LinearMap.ext
  intro field
  have fixed : degreeSix (propagator (diracDualRightChiralYukawaAction second field)) =
      propagator (diracDualRightChiralYukawaAction second field) := by
    have commute := LinearMap.congr_fun preserves
      (diracDualRightChiralYukawaAction second field)
    change degreeSix (propagator (diracDualRightChiralYukawaAction second field)) =
      propagator (degreeSix (diracDualRightChiralYukawaAction second field)) at commute
    rw [show degreeSix (diracDualRightChiralYukawaAction second field) =
      diracDualRightChiralYukawaAction second field from
      LinearMap.congr_fun (yukawa_output second) field] at commute
    exact commute
  change diracDualRightChiralYukawaAction first
    (propagator (diracDualRightChiralYukawaAction second field)) = 0
  rw [← fixed]
  exact LinearMap.congr_fun (yukawa_degreeSix first) _

/-- The original scalar-to-matter Hessian map, with the actual chiral placement. -/
def scalarMixing (point : BasePoint) (scalar : ExteriorBreakingScalarCarrier) :
    DiracExteriorMatterCarrier :=
  diracDualRightChiralYukawaAction scalar (actual.matter point)

theorem scalarMixing_degreeSix (point : BasePoint) (scalar : ExteriorBreakingScalarCarrier) :
    degreeSix (scalarMixing point scalar) = scalarMixing point scalar :=
  LinearMap.congr_fun (yukawa_output scalar) (actual.matter point)

theorem scalarMixing_yukawa_zero (point : BasePoint)
    (first second : ExteriorBreakingScalarCarrier) :
    diracDualRightChiralYukawaAction first (scalarMixing point second) = 0 := by
  exact LinearMap.congr_fun (Response.Yukawa.ordered_product_zero first second) _

theorem backgroundDual_yukawa_zero (point : BasePoint)
    (scalar : ExteriorBreakingScalarCarrier) (matter : DiracExteriorMatterCarrier) :
    actual.conjugateMatter point (diracDualRightChiralYukawaAction scalar matter) = 0 :=
  spinPairDual_yukawa_annihilates scalar matter _ _

theorem scalarMixing_nonzero :
    scalarMixing 0 Response.MixedWitness.scalarDirection ≠ 0 := by
  intro zero
  have paired := Response.MixedWitness.mixed_channel_nonzero
  change (Response.MixedWitness.outputDual
    (scalarMixing 0 Response.MixedWitness.scalarDirection)).re ≠ 0 at paired
  rw [zero, map_zero] at paired
  exact paired rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.MixedSymbol
