import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell2.RuntimeConsumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandFullCarrier.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

/-- The complete Root64 material is read from its actual installed facade. -/
def parentRuntime := WholeBandCell2.Runtime.initialFieldRuntimeAfterFirst
def parentMaterial : WholeBandCell2.Runtime.InitialFieldMaterial := WholeBandCell2.Runtime.readMaterial parentRuntime

def parentResult := WholeBandCell2.Runtime.initialFieldParentResult
def parentHistory := WholeBandCell2.Runtime.initialFieldParentHistory

abbrev ParentBase := WholeBandCell2.Runtime.initialFieldAuthoritySource
abbrev ParentLedger := ParentBase.restructuringSource.toLedgerSource

theorem parent_installed :
    type_of% (WholeBandCell2.Runtime.initialFieldRuntimeFace_factorizes parentRuntime (.component .material)) ∧
    type_of% (WholeBandCell2.Runtime.initialFieldRuntimeFace_factorizes parentRuntime (.component .certificate)) :=
  ⟨WholeBandCell2.Runtime.initialFieldRuntimeFace_factorizes parentRuntime (.component .material),
    WholeBandCell2.Runtime.initialFieldRuntimeFace_factorizes parentRuntime (.component .certificate)⟩

theorem parent_actual :
    parentMaterial = WholeBandCell2.Runtime.generatedInitialFieldMaterial ∧
    parentResult.nuclear.target = Reentry.Source.stepReadout.nuclear.target ∧
    parentResult.nuclear.targetLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    parentResult.realized = Reentry.Source.targetRealized ∧ parentHistory = Reentry.Runtime.reentrySourceHistory :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem parent_clock : parentResult.clock = 3 * Propagation.Producer.nativeClockStep :=
  WholeBandCell2.Runtime.initialFieldParent_clock

theorem parent_same_actual_visit : parentRuntime.current.visit =
    Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandFullCarrier.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
