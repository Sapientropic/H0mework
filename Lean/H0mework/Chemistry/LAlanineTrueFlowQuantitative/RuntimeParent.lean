import H0mework.Chemistry.LAlanineTrueFlowConservation.RuntimeConsumers

/-! The original occurrence installs its actual true-flow quantitative bounds. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowQuantitativeRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def quantitativeParentRuntime := TrueFlowConservationRuntime.conservationRuntimeAfterFirst
def quantitativeParentMaterial : TrueFlowConservationRuntime.ConservationMaterial :=
  match TrueFlowConservationRuntime.conservationRuntimeFacade.readoutAt quantitativeParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def quantitativeParentResult := quantitativeParentMaterial.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.physical
def quantitativeParentHistory := quantitativeParentMaterial.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.parent.history

theorem quantitativeParent_installed :
    type_of% (TrueFlowConservationRuntime.conservationRuntimeFace_factorizes quantitativeParentRuntime (.component .material)) ∧
    type_of% (TrueFlowConservationRuntime.conservationRuntimeFace_factorizes quantitativeParentRuntime (.component .certificate)) :=
  ⟨TrueFlowConservationRuntime.conservationRuntimeFace_factorizes quantitativeParentRuntime (.component .material),
    TrueFlowConservationRuntime.conservationRuntimeFace_factorizes quantitativeParentRuntime (.component .certificate)⟩

theorem quantitativeParent_actual :
    quantitativeParentMaterial = TrueFlowConservationRuntime.generatedConservationMaterial ∧
    quantitativeParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    quantitativeParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    quantitativeParentResult.realized = Reentry.Source.targetRealized ∧
    quantitativeParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem quantitativeParent_clock : quantitativeParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  TrueFlowConservationRuntime.conservationParent_clock

theorem quantitativeParent_error_and_memory :
    quantitativeParentResult.realized = quantitativeParentResult.held + quantitativeParentResult.inheritedResidual +
      quantitativeParentResult.newNumericalResidual ∧
    ‖quantitativeParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  TrueFlowConservationRuntime.conservationParent_error_and_memory

abbrev QuantitativeBase := TrueFlowConservationRuntime.conservationLivingRoot.toAuthoritativeRoot.source
abbrev QuantitativeLedger := QuantitativeBase.restructuringSource.toLedgerSource

theorem quantitativeParent_same_actual_visit :
    quantitativeParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.TrueFlowQuantitativeRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
