import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaRoot.Coordinates
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Root.Factory

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRoot
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms MotherExactPrograms MotherPatchInventory
open MotherPatchInventory
open MotherLedgerRoot
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

def EmittedCheck {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (material : M) : Prop :=
  ∀ current, ∃! event : source.toRootSource.actual.OccurrenceAt current,
    r2 material 0 (coordinates.current current) (coordinates.event current event)

def generatedEmitted {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (material : M) (checked : EmittedCheck coordinates material) : Emitted source :=
  fun current => Classical.choose (checked current)

def formRootParts (parent material : M) : Option RootValue :=
  (MotherArenaPatches.formCompiler parent).pbind (fun value formed =>
    let coordinates := compilerCoordinates parent value formed
    if checked : EmittedCheck coordinates material then
      let emitted := generatedEmitted coordinates material checked
      if commutes : RootCheck value emitted then some ⟨value.1.1.1, value.1.1.2.1, rootOf value emitted commutes⟩
      else none
    else none)

/-- The original source, whole compiler and entire emitter section are formed
from one material; the original root coherence is checked internally. -/
def formRoot (material : M) : Option RootValue :=
  let parts := (MotherArenaHigher.split rank) material
  formRootParts parts.1 parts.2

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRoot
