import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Root.Coordinates

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLedgerRoot
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherPatchInventory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

abbrev Emitted {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : SourceNativeSource N V) :=
  (current : V.Current) → source.toRootSource.actual.OccurrenceAt current

def EmittedCheck {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : Coordinates source) (material : M) : Prop :=
  ∀ current, ∃! event : source.toRootSource.actual.OccurrenceAt current,
    r2 material 0 (coordinates.current current) (coordinates.event current event)

def generatedEmitted {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : Coordinates source) (material : M) (checked : EmittedCheck coordinates material) : Emitted source :=
  fun current => Classical.choose (checked current)

def RootCheck (value : CompilerValue) (emitted : Emitted value.1.1.2.2) : Prop :=
  ∀ current, (value.2.compile (emitted current)).CommutesWith emitted

def rootOf (value : CompilerValue) (emitted : Emitted value.1.1.2.2) (checked : RootCheck value emitted) :
    SourceNativeLedgerRootClosure value.1.1.1 value.1.1.2.1 where
  source := ⟨value.1.1.2.2, value.2⟩
  emitted := emitted
  compiler_commutes := checked

abbrev RootValue := Σ N : WorldRelationNetwork.{0}, Σ V : Vocabulary.{0}, SourceNativeLedgerRootClosure N V

def formRootParts (parent material : M) : Option RootValue :=
  (formCompiler parent).pbind (fun value formed =>
    let coordinates := compilerCoordinates parent value formed
    if checked : EmittedCheck coordinates material then
      let emitted := generatedEmitted coordinates material checked
      if commutes : RootCheck value emitted then some ⟨value.1.1.1, value.1.1.2.1, rootOf value emitted commutes⟩
      else none
    else none)

/-- The original source, whole compiler and entire emitter section are formed
from one material; the original root coherence is checked internally. -/
def formRoot (material : M) : Option RootValue :=
  let parts := MotherHigherLawValue.split material
  formRootParts parts.1 parts.2

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLedgerRoot
