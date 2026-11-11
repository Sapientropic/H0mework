import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaNativePortFibre
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusPaCayleySource
import H0mework.Realization.Operations.ObservationKernel

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.PaNativeCayleyFaithfulness
open Complex BurnolPhysicalState PaNativePortSource
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped InnerProductSpace
namespace History
export SourceGeneratedActionObservationHistory
  (sourceMap mem_kernel_iff kernel_is_largest_invisible_invariant invariant_submodule_le_kernel)
end History
namespace Original
export OriginalWholeDebtRJointMobiusPaCayleySource
  (sourceNext rawUpdate sourceQ actual_source_Q actual_whole_update actual_Pa_loss
   actual_Pa_loss_zero_iff unitPrice unitPrice_positive)
end Original
local notation "E" => OriginalKCombCofinalPaAction.E
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance : CompleteSpace ↥Pa :=
  IsComplete.completeSpace_coe burnolCompactCoPoissonClosedRange.isClosed.isComplete

private def inclusion : ↥Pa →L[ℂ] BurnolL2 :=
  (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL.comp Pa.subtypeL

/-- The original U action is executed before its dependent Pa projection. -/
def action (c : BurnolCompletedMellinCoordinate) : ↥Pa →L[ℂ] ↥Pa :=
  ((OriginalKCombCofinalPaAction.E).comp ((sourceCayley c).comp inclusion)).codRestrict Pa
    (fun _ => Submodule.starProjection_apply_mem _ _)

private def observer (c : BurnolCompletedMellinCoordinate) : ↥Pa →L[ℂ] ℂ :=
  (burnolPaResolventSourceCoefficient c).comp Pa.subtypeL

private def unitPa (c : BurnolCompletedMellinCoordinate) : ↥Pa :=
  ⟨E (burnolUnitTailResponse c 4), Submodule.starProjection_apply_mem _ _⟩

private theorem E_source (input : ↥Pa) :
    E ((input : BurnolPaAmbientCarrier) : BurnolL2) = input.val := by
  change Pa.starProjection (burnolEvenAmbientProjection (input.val : BurnolL2)) = input.val
  have physical : burnolEvenAmbientProjection (input.val : BurnolL2) = input.val :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self input.val
  rw [physical]
  exact Pa.starProjection_eq_self_iff.mpr input.property

/-- This retains the full actual R correction and its true projected unit vector. -/
theorem action_actual_R_unit (c : BurnolCompletedMellinCoordinate) (input : ↥Pa) :
    action c input = input + (sourceDamping c : ℂ) • correction c input +
      ((sourceDamping c : ℂ) * observer c input) • unitPa c := by
  have original := actual_original_R c 0 input
  have projected := congrArg E original
  change E (burnolDirectRightResolventCLM c (inclusion input)) =
    E (((correction c input : BurnolPaAmbientCarrier) : BurnolL2) +
      observer c input • burnolUnitTailResponse c 4) at projected
  rw [map_add, map_smul, E_source] at projected
  apply Subtype.ext
  change E (sourceCayley c (inclusion input)) = _
  rw [sourceCayley_apply, map_add, map_smul]
  change E ((input.val : BurnolL2)) + (sourceDamping c : ℂ) •
    E (burnolDirectRightResolventCLM c (inclusion input)) = _
  rw [E_source, projected]
  change input.val + (sourceDamping c : ℂ) •
      ((correction c input).val + observer c input • (unitPa c).val) =
    input.val + (sourceDamping c : ℂ) • (correction c input).val +
      ((sourceDamping c : ℂ) * observer c input) • (unitPa c).val
  module

private theorem action_on_invisible (c : BurnolCompletedMellinCoordinate) (input : ↥Pa)
    (invisible : observer c input = 0) :
    action c input = input + (sourceDamping c : ℂ) • correction c input := by
  rw [action_actual_R_unit, invisible, mul_zero, zero_smul, add_zero]

/-- The existing complete future kernel is C-invariant because its own observer vanishes. -/
theorem history_kernel_zero (c : BurnolCompletedMellinCoordinate) :
    LinearMap.ker (History.sourceMap (action c).toLinearMap (observer c).toLinearMap) = ⊥ := by
  let K := LinearMap.ker (History.sourceMap (action c).toLinearMap (observer c).toLinearMap)
  have largest := History.kernel_is_largest_invisible_invariant
    (action c).toLinearMap (observer c).toLinearMap
  have correctionInvariant : K ≤ K.comap (correction c).toLinearMap := by
    intro input member
    have invisible : observer c input = 0 := largest.1 member
    have next : action c input ∈ K := largest.2.1 member
    have deltaNonzero : (sourceDamping c : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sourceDamping_pos c).ne'
    have scaled : (sourceDamping c : ℂ) • correction c input ∈ K := by
      have difference := K.sub_mem next member
      rw [action_on_invisible c input invisible, add_sub_cancel_left] at difference
      exact difference
    have unscaled := K.smul_mem ((sourceDamping c : ℂ)⁻¹) scaled
    change correction c input ∈ K
    simpa only [smul_smul, inv_mul_cancel₀ deltaNonzero, one_smul] using unscaled
  have inCorrection := History.invariant_submodule_le_kernel
    (correction c).toLinearMap (observer c).toLinearMap K largest.1 correctionInvariant
  apply le_antisymm _ bot_le
  intro input member
  change input = 0
  apply (PaNativePortFibre.all_ports_zero_iff c input).mp
  intro n
  have observed := (History.mem_kernel_iff (correction c).toLinearMap
    (observer c).toLinearMap input).mp (inCorrection member) n
  rw [Module.End.pow_apply] at observed
  exact observed

def orbit (c : BurnolCompletedMellinCoordinate) (stage : Nat) (input : ↥Pa) : ↥Pa :=
  ((action c).toLinearMap ^ stage) input

theorem orbit_succ (c : BurnolCompletedMellinCoordinate) (stage : Nat) (input : ↥Pa) :
    orbit c (stage + 1) input = action c (orbit c stage input) := by
  unfold orbit
  rw [pow_succ']
  rfl

theorem all_observations_zero_iff (c : BurnolCompletedMellinCoordinate) (input : ↥Pa) :
    (∀ n, observer c (orbit c n input) = 0) ↔ input = 0 := by
  change (∀ n, (observer c).toLinearMap (((action c).toLinearMap ^ n) input) = 0) ↔ input = 0
  rw [← History.mem_kernel_iff (action c).toLinearMap (observer c).toLinearMap input,
    history_kernel_zero, Submodule.mem_bot]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

theorem action_sourceNext (input : ↥Pa) :
    action c input = Original.sourceNext observation nontrivial half input := rfl

def actualLoss (stage : Nat) (input : ↥Pa) : ℝ :=
  ‖(orbit c stage input : BurnolPaAmbientCarrier)‖ ^ 2 -
    ‖(orbit c (stage + 1) input : BurnolPaAmbientCarrier)‖ ^ 2

/-- Both whole-U components are the original same-step Pa/Q vectors at every actual stage. -/
theorem actual_whole_at (stage : Nat) (input : ↥Pa) :
    Original.rawUpdate observation nontrivial half (orbit c stage input) =
      ((orbit c (stage + 1) input : BurnolPaAmbientCarrier) : BurnolL2) +
        (Original.sourceQ observation nontrivial half (orbit c stage input) : BurnolL2) := by
  rw [orbit_succ, action_sourceNext]
  exact Original.actual_whole_update observation nontrivial half _

theorem actual_Q_at (stage : Nat) (input : ↥Pa) :
    OriginalKCombCofinalPaAction.Q
      (Original.rawUpdate observation nontrivial half (orbit c stage input)) =
        Original.sourceQ observation nontrivial half (orbit c stage input) :=
  Original.actual_source_Q observation nontrivial half _

theorem actual_loss_at (stage : Nat) (input : ↥Pa) :
    actualLoss observation nontrivial half stage input =
      Original.unitPrice observation nontrivial half * ‖observer c (orbit c stage input)‖ ^ 2 := by
  unfold actualLoss
  rw [orbit_succ, action_sourceNext]
  exact Original.actual_Pa_loss observation nontrivial half _

theorem actual_loss_zero_iff (stage : Nat) (input : ↥Pa) :
    actualLoss observation nontrivial half stage input = 0 ↔
      observer c (orbit c stage input) = 0 := by
  unfold actualLoss
  rw [orbit_succ, action_sourceNext]
  exact Original.actual_Pa_loss_zero_iff observation nontrivial half _

/-- The entire actual physical loss fibre is the original zero Pa, with its true unit price. -/
theorem all_actual_losses_zero_iff (input : ↥Pa) :
    (∀ stage, actualLoss observation nontrivial half stage input = 0) ↔ input = 0 := by
  rw [← all_observations_zero_iff c input]
  exact forall_congr' (fun stage => actual_loss_zero_iff observation nontrivial half stage input)

theorem exists_actual_positive_loss (input : ↥Pa) (nonzero : input ≠ 0) :
    ∃ stage, 0 < actualLoss observation nontrivial half stage input := by
  classical
  have notAll : ¬∀ stage, actualLoss observation nontrivial half stage input = 0 :=
    fun all => nonzero ((all_actual_losses_zero_iff observation nontrivial half input).mp all)
  obtain ⟨stage, nonzeroLoss⟩ := not_forall.mp notAll
  refine ⟨stage, lt_of_le_of_ne ?_ (Ne.symm nonzeroLoss)⟩
  rw [actual_loss_at]
  exact mul_nonneg (Original.unitPrice_positive observation nontrivial half).le (sq_nonneg _)

end OriginalKCrossParameterRAdjointSource.PaNativeCayleyFaithfulness
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
