import H0mework.Versions.R9c73a630.Chemistry.LAlanineAtomicMass.RuntimeConsumers

/-! Original Root60 occurrence and complete inherited material. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSaturation.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def saturationParentRuntime := LAlanine40K2025.AtomicMass.Runtime.atomicMassRuntimeAfterFirst
def saturationParentMaterial : LAlanine40K2025.AtomicMass.Runtime.AtomicMassMaterial :=
  match LAlanine40K2025.AtomicMass.Runtime.atomicMassRuntimeFacade.readoutAt saturationParentRuntime (.component .material) with
  | .inl ⟨_, _, material⟩ => material
  | .inr impossible => nomatch impossible

def saturationParentResult := LAlanine40K2025.AtomicMass.Runtime.atomicMassParentResult
def saturationParentHistory := LAlanine40K2025.AtomicMass.Runtime.atomicMassParentHistory

theorem saturationParent_installed :
    type_of% (LAlanine40K2025.AtomicMass.Runtime.atomicMassRuntimeFace_factorizes saturationParentRuntime (.component .material)) ∧
    type_of% (LAlanine40K2025.AtomicMass.Runtime.atomicMassRuntimeFace_factorizes saturationParentRuntime (.component .certificate)) :=
  ⟨LAlanine40K2025.AtomicMass.Runtime.atomicMassRuntimeFace_factorizes saturationParentRuntime (.component .material),
    LAlanine40K2025.AtomicMass.Runtime.atomicMassRuntimeFace_factorizes saturationParentRuntime (.component .certificate)⟩

theorem saturationParent_actual :
    saturationParentMaterial = LAlanine40K2025.AtomicMass.Runtime.generatedAtomicMassMaterial ∧
    saturationParentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    saturationParentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    saturationParentResult.realized = Reentry.Source.targetRealized ∧
    saturationParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem saturationParent_clock : saturationParentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  LAlanine40K2025.AtomicMass.Runtime.atomicMassParent_clock

theorem saturationParent_error_and_memory :
    saturationParentResult.realized = saturationParentResult.held + saturationParentResult.inheritedResidual +
      saturationParentResult.newNumericalResidual ∧
    ‖saturationParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  LAlanine40K2025.AtomicMass.Runtime.atomicMassParent_error_and_memory

abbrev SaturationBase := LAlanine40K2025.AtomicMass.Runtime.atomicMassLivingRoot.toAuthoritativeRoot.source
abbrev SaturationLedger := SaturationBase.restructuringSource.toLedgerSource

theorem saturationParent_same_actual_visit :
    saturationParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandSaturation.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule