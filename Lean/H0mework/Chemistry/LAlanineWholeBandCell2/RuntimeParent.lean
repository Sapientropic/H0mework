import H0mework.Chemistry.LAlanineBandCache.SaturationRuntimeConsumers
/-! Original Root62 occurrence and the entire installed Gaussian and inherited physical material. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell2.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def initialFieldParentRuntime := WholeBandSaturation.Runtime.saturationRuntimeAfterFirst
def initialFieldParentMaterial : WholeBandSaturation.Runtime.SaturationMaterial :=
  match WholeBandSaturation.Runtime.saturationRuntimeFacade.readoutAt initialFieldParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def initialFieldParentResult := WholeBandSaturation.Runtime.saturationParentResult
def initialFieldParentHistory := WholeBandSaturation.Runtime.saturationParentHistory

theorem initialFieldParent_installed :
    type_of% (WholeBandSaturation.Runtime.saturationRuntimeFace_factorizes initialFieldParentRuntime (.component .material)) ∧
    type_of% (WholeBandSaturation.Runtime.saturationRuntimeFace_factorizes initialFieldParentRuntime (.component .certificate)) :=
  ⟨WholeBandSaturation.Runtime.saturationRuntimeFace_factorizes initialFieldParentRuntime (.component .material),
    WholeBandSaturation.Runtime.saturationRuntimeFace_factorizes initialFieldParentRuntime (.component .certificate)⟩

theorem initialFieldParent_actual :
    initialFieldParentMaterial = WholeBandSaturation.Runtime.generatedSaturationMaterial ∧
    initialFieldParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    initialFieldParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    initialFieldParentResult.realized = Reentry.Source.targetRealized ∧
    initialFieldParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem initialFieldParent_clock : initialFieldParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  WholeBandSaturation.Runtime.saturationParent_clock

theorem initialFieldParent_error_and_memory :
    initialFieldParentResult.realized = initialFieldParentResult.held + initialFieldParentResult.inheritedResidual +
      initialFieldParentResult.newNumericalResidual ∧
    ‖initialFieldParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  WholeBandSaturation.Runtime.saturationParent_error_and_memory

abbrev InitialFieldBase := WholeBandSaturation.Runtime.saturationLivingRoot.toAuthoritativeRoot.source
abbrev InitialFieldLedger := InitialFieldBase.restructuringSource.toLedgerSource

theorem initialFieldParent_same_actual_visit :
    initialFieldParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandCell2.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
