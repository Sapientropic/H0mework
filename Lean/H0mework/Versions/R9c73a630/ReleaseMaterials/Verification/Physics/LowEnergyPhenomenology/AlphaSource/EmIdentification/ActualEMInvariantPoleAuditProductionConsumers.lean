import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMInvariantCurvature
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMInvariantPole

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMInvariantPoleAudit
elab "checked_native_curvature_gram_holonomicContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.native_curvature_gram_holonomic).type
theorem checked_native_curvature_gram_holonomic : checked_native_curvature_gram_holonomicContract := @LowEnergy.GaussComposite.ActualEMInvariantCurvature.native_curvature_gram_holonomic

elab "checked_curvature_gram_first_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_first_generated).type
theorem checked_curvature_gram_first_generated : checked_curvature_gram_first_generatedContract := @LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_first_generated

elab "checked_curvature_gram_second_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_second_generated).type
theorem checked_curvature_gram_second_generated : checked_curvature_gram_second_generatedContract := @LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_second_generated

elab "checked_curvature_gram_and_original_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_and_original_action).type
theorem checked_curvature_gram_and_original_action : checked_curvature_gram_and_original_actionContract := @LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_gram_and_original_action

elab "checked_curvature_pair_orbit_balanceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_pair_orbit_balance).type
theorem checked_curvature_pair_orbit_balance : checked_curvature_pair_orbit_balanceContract := @LowEnergy.GaussComposite.ActualEMInvariantCurvature.curvature_pair_orbit_balance

elab "checked_invariant_curvature_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_original).type
theorem checked_invariant_curvature_original : checked_invariant_curvature_originalContract := @LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_original

elab "checked_invariant_curvature_continuousContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_continuous).type
theorem checked_invariant_curvature_continuous : checked_invariant_curvature_continuousContract := @LowEnergy.GaussComposite.ActualEMInvariantCurvature.invariant_curvature_continuous

elab "checked_native_origin_curvature_orbitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_curvature_orbit).type
theorem checked_native_origin_curvature_orbit : checked_native_origin_curvature_orbitContract := @LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_curvature_orbit

elab "checked_native_origin_invariant_firstContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_invariant_first).type
theorem checked_native_origin_invariant_first : checked_native_origin_invariant_firstContract := @LowEnergy.GaussComposite.ActualEMInvariantPole.native_origin_invariant_first

elab "checked_invariant_origin_modeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_mode).type
theorem checked_invariant_origin_mode : checked_invariant_origin_modeContract := @LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_mode

elab "checked_invariant_origin_responseContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_response).type
theorem checked_invariant_origin_response : checked_invariant_origin_responseContract := @LowEnergy.GaussComposite.ActualEMInvariantPole.invariant_origin_response

elab "checked_dressed_invariant_frequency_leadingContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMInvariantPole.dressed_invariant_frequency_leading).type
theorem checked_dressed_invariant_frequency_leading : checked_dressed_invariant_frequency_leadingContract := @LowEnergy.GaussComposite.ActualEMInvariantPole.dressed_invariant_frequency_leading

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
open LowEnergy.CanonicalGradedSpatialSource LowEnergy.PreparationVacuumPhysicalFeedback
open LowEnergy.PreparationVacuumPhysicalCharacteristic LowEnergy.PreparationVacuumPhysicalPoleSheet
open LowEnergy.PreparationPhysicalNativePhotonFluxReturn
open LowEnergy.PreparationVacuumLowerClassical
open LowEnergy.SourcePropagationNativeActionHessian LowEnergy.PreparationVacuumMixedFieldReturn
open LowEnergy.GaussComposite.ActualEMInvariantCurvature LowEnergy.GaussComposite.ActualEMInvariantPole
open LowEnergy.GaussComposite.ActualEMGaugeCurvature LowEnergy.GaussComposite.ActualEMDressedGaugePole
open LowEnergy.GaussComposite.ActualDressedFullCoulomb LowEnergy.GaussComposite.ActualEMAction
open Filter
open scoped Matrix BigOperators Topology

attribute [local irreducible] dressedGaugePole sourceWholePhotonFrequencyResidue emActionFrequencyJet

theorem checked_same_invariant_action_flux (event : DressedEvent) (branch : Fin 2)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (T : ℝ) (pair other : Fin 6) :
    ∀ᶠ e in scaleApproach,
      invariantCurvatureMap (frequencyRay e.val (sourceSheet branch n unit e.val) n) pair other
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
          (emActionFrequencyJet e.val (sourceFrequency e.val (sourceSheet branch n unit e.val)) n *ᵥ
            dressedGaugePole event e.val (sourceSheet branch n unit e.val) n T)) =
      invariantCurvatureMap (frequencyRay e.val (sourceSheet branch n unit e.val) n) pair other
        (dressedGaugePole event e.val (sourceSheet branch n unit e.val) n T) := by
  filter_upwards [dressed_gauge_frequency_flux event branch n unit T] with e flux
  exact congrArg (invariantCurvatureMap _ pair other) flux

private theorem audit_vec3_last {α : Type} (a b c : α) : (![a,b,c] : Fin 3 → α) 2 = c := rfl

theorem checked_unit_direction : spatialSquare (![1,0,0] : PhysicalMomentum)=1 := by
  norm_num [spatialSquare,audit_vec3_last]

theorem checked_scale_nonempty : scaleApproach.NeBot := scaleApproach_nonempty
end LowEnergy.GaussComposite.ActualEMInvariantPoleAudit

