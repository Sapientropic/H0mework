import H0mework.Versions.AB.Chemistry.LAlanineHeldForce.RuntimeHeldForceRuntime

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.HeldForce.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem heldForceRuntime_physical_installed (runtime : LivingRuntimeState heldForceRuntimeProcess) :
    type_of% (heldForceRuntimeFace_factorizes runtime.tick.next .physical) ∧
    heldForceRuntimeFacade.readoutAt runtime.tick.next .physical =
      (.inl ⟨PUnit.unit, (heldForceParentMaterial, heldForceSourceResult.frame, heldForceSourceResult.energyLedger)⟩ :
        SourceNativeProjectionFiberAt heldForceProjectionLaw .physical (heldForceEmitted runtime.tick.next.state.current)) := by
  refine ⟨heldForceRuntimeFace_factorizes runtime.tick.next .physical, ?_⟩
  rw [← heldForceRuntime_response runtime]
  rfl

theorem heldForceRuntime_realization_installed (runtime : LivingRuntimeState heldForceRuntimeProcess) :
    type_of% (heldForceRuntimeFace_factorizes runtime .realization) ∧
    heldForceRuntimeFacade.readoutAt runtime .realization =
      (.inl ⟨PUnit.unit, (heldForceSourceResult.realized, heldForceSourceResult.realizationResidual)⟩ :
        SourceNativeProjectionFiberAt heldForceProjectionLaw .realization (heldForceEmitted runtime.state.current)) := by
  refine ⟨heldForceRuntimeFace_factorizes runtime .realization, ?_⟩
  rw [← heldForceRuntime_response runtime]
  rfl

theorem heldForceRuntime_gradient_installed (runtime : LivingRuntimeState heldForceRuntimeProcess) :
    type_of% (heldForceRuntimeFace_factorizes runtime .gradient) ∧
    heldForceRuntimeFacade.readoutAt runtime .gradient =
      (.inl ⟨PUnit.unit, (heldForceSourceResult.gradientComponents, heldForceSourceResult.gradientPicohartree,
        heldForceSourceResult.forcePicohartree, heldForceSourceResult.gradientResidual,
        heldForceSourceResult.stationaryCorrection)⟩ :
        SourceNativeProjectionFiberAt heldForceProjectionLaw .gradient (heldForceEmitted runtime.state.current)) := by
  refine ⟨heldForceRuntimeFace_factorizes runtime .gradient, ?_⟩
  rw [← heldForceRuntime_response runtime]
  rfl

theorem heldForceRuntime_no_motion (runtime : LivingRuntimeState heldForceRuntimeProcess) :
    (heldForceFrame runtime.tick.next.state.current).position = heldForceParentFrame.position ∧
    (heldForceFrame runtime.tick.next.state.current).momentum = heldForceParentFrame.momentum ∧
    (heldForceFrame runtime.tick.next.state.current).kinetic = heldForceParentFrame.kinetic := by
  change (heldForceResponse runtime.state.current).frame.position = _ ∧
    (heldForceResponse runtime.state.current).frame.momentum = _ ∧
    (heldForceResponse runtime.state.current).frame.kinetic = _
  rw [heldForceRuntime_response]
  exact generatedHeldForceAction_receipt.noNuclearMotion

theorem heldForceRuntime_actual_response (runtime : LivingRuntimeState heldForceRuntimeProcess) :
    (heldForceFrame runtime.tick.next.state.current).force = -Source.rawGradient ∧
    (heldForceFrame runtime.tick.next.state.current).potential = Source.rawEnergy ∧
    (heldForceFrame runtime.tick.next.state.current).total = heldForceParentFrame.kinetic + Source.rawEnergy ∧
    heldForceCurrentLedger runtime.tick.next.state.current = Source.energyLedger := by
  change (heldForceResponse runtime.state.current).frame.force = _ ∧
    (heldForceResponse runtime.state.current).frame.potential = _ ∧
    (heldForceResponse runtime.state.current).frame.total = _ ∧
    (heldForceResponse runtime.state.current).energyLedger = _
  rw [heldForceRuntime_response]
  exact ⟨generatedHeldForceAction_receipt.physicalResponse.1,
    generatedHeldForceAction_receipt.physicalResponse.2.1,
    generatedHeldForceAction_receipt.physicalResponse.2.2, rfl⟩

theorem heldForceRuntime_realization_error (runtime : LivingRuntimeState heldForceRuntimeProcess) :
    (heldForceResponse runtime.state.current).realized = Producer.exactHeld +
      (heldForceResponse runtime.state.current).realizationResidual ∧
    ‖(heldForceResponse runtime.state.current).realizationResidual‖ < (8 : ℝ) / 10 ^ 9 := by
  rw [heldForceRuntime_response]
  exact ⟨heldForceRuntime_sourceCertificate.2.1, generatedHeldForceAction_receipt.realizationError⟩

theorem heldForceRuntime_force_components (runtime : LivingRuntimeState heldForceRuntimeProcess) :
    (heldForceResponse runtime.state.current).gradientComponents.size = 6 ∧
    (∀ atom axis, Inertia.Producer.forceComponentSum (heldForceResponse runtime.state.current).gradientComponents atom axis +
      (heldForceResponse runtime.state.current).gradientResidual atom axis =
        (heldForceResponse runtime.state.current).gradientPicohartree atom axis) ∧
    (∀ atom axis, (heldForceResponse runtime.state.current).forcePicohartree atom axis =
      -(heldForceResponse runtime.state.current).gradientPicohartree atom axis) ∧
    (heldForceResponse runtime.state.current).stationaryCorrection ≠ 0 := by
  rw [heldForceRuntime_response]
  rcases heldForceRuntime_sourceCertificate.2 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, six, components, sign, _, correction, _, _⟩
  exact ⟨six, components, sign, correction⟩

theorem heldForceRuntime_row_identity (runtime : LivingRuntimeState heldForceRuntimeProcess) :
    (heldForceOccurrenceEntry (heldForceEmitted runtime.state.current)).1 = .bondDensityIncidenceAdjudication ∧
    (heldForceOccurrenceEntry (heldForceEmitted runtime.state.current)).claim =
      .registeredExperimentalGeometryModelBondTopology ∧
    (heldForceOccurrenceEntry (heldForceEmitted runtime.state.current)).progressBudget = 0 ∧
    N.lineageAt heldForceSupport = LAlanine40K2025.Source.key := ⟨rfl, rfl, rfl, rfl⟩

end
end LAlanine40K2025.HeldForce.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
