import H0mework.Versions.R2.Physics.CompositeSpectrum.Trace

/-! The original nonzero breaking scalar supplies an unoccupied ambient
matter witness. The full curvature cubic annihilates it, whereas the
occupied scalar normal form does not; thus the full action is not replaced
by its occupied scalar or by a chosen singlet lift. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracExteriorMatterAction
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open StageNineDynamicBreakingVacuum StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource
open StageNineP286GaugeConnectionVariation SU7MotherLieAlgebra SU7MotherGaugeTheory
open Stage9C.Material.SpinPair Stage9DEF

noncomputable section

def vacuumMatterWitness : DiracExteriorMatterCarrier :=
  fun _ => (0, 0, sourceGeneratedVacuumBase positiveSmoothUnifiedSource)

theorem vacuumMatterWitness_nonzero : vacuumMatterWitness ≠ 0 := by
  intro zero
  have scalarZero := congrArg (fun matter : DiracExteriorMatterCarrier => (matter 0).2.2) zero
  exact positive_sourceGeneratedVacuumBase_nonzero scalarZero

theorem vacuumMotherAction_zero (axis : Fin 3) :
    exteriorMotherLieAction 4 (p286LieBlockEmbed (sourceColorP286Generator axis))
      (sourceGeneratedVacuumBase positiveSmoothUnifiedSource) = 0 := by
  have coordinate := sourceColorP286Generator_vacuum_zero axis
  unfold scalarMotherLieAction sourceGeneratedVacuumCoordinates at coordinate
  rw [scalarCoordinateEquiv.symm_apply_apply] at coordinate
  exact scalarCoordinateEquiv.injective (coordinate.trans (map_zero _).symm)

theorem incomingCurvatureAction_vacuumWitness (point : BasePoint) (axis : Fin 3) :
    incomingCurvatureAction point axis vacuumMatterWitness = 0 := by
  rw [incomingCurvatureAction_eq, curvatureAction, actual_magnetic_component,
    p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul]
  have zero : diracExteriorMotherLieAction
      (p286LieBlockEmbed (sourceColorP286Generator axis)) vacuumMatterWitness = 0 := by
    funext spin
    change (exteriorMotherLieAction 6 _ 0, exteriorMotherLieAction 2 _ 0,
      exteriorMotherLieAction 4 _ (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)) = 0
    rw [map_zero, map_zero, vacuumMotherAction_zero]
    rfl
  simp only [LinearMap.smul_apply, zero, smul_zero]

theorem compositeAction_vacuumWitness (point : BasePoint) :
    compositeAction point vacuumMatterWitness = 0 := by
  simp only [compositeAction, alternatingProduct, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
    incomingCurvatureAction_vacuumWitness, map_zero, add_zero, sub_zero, smul_zero]

theorem compositeAction_not_full_scalar (point : BasePoint) :
    compositeAction point ≠ (curvatureScale : ℂ) ^ 3 • (1 : Module.End ℂ DiracExteriorMatterCarrier) := by
  intro same
  have value := congrArg (fun action : Module.End ℂ DiracExteriorMatterCarrier => action vacuumMatterWitness) same
  rw [compositeAction_vacuumWitness] at value
  have nonzero : (curvatureScale : ℂ) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (by exact_mod_cast ne_of_gt curvatureScale_pos)
  exact vacuumMatterWitness_nonzero ((smul_eq_zero.mp value.symm).resolve_left nonzero)

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
