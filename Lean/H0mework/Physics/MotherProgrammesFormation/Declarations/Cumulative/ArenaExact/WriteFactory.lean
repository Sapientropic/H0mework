import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaExact.WriteCoordinates
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.WriteFactory

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) (operations : Transitions source)
    (exactCode : ∀ context, operations.Exact context ↪ MotherArenaHigher.Base rank)

abbrev WriteEvent (material : M) (context : WriteContext source) :=
  {event : B // r2 material 0 (writeContextEmbedding coordinates ledger context) event}

abbrev RemainderEvent (material : M) (context : RemainderContext source) :=
  {event : B // r2 material 0 (remainderContextEmbedding coordinates ledger context) event}

def rowOutputGraph (material : M) (context : WriteContext source) (event : B) (output : RowOutput operations context) : Prop :=
  let key := MotherArenaCompiler.rowKey ledger output.1
  r3 material (1 + key.1) (writeContextEmbedding coordinates ledger context) event
    ((MotherArenaHigher.pair rank) (key.2, exactCode context output.2))

def WriteRowCheck (material : M) : Prop :=
  ∀ (context : WriteContext source) (event : WriteEvent coordinates ledger material context),
    ∃! output : RowOutput operations context, rowOutputGraph coordinates ledger operations exactCode material context event.val output

def remainderEventKey (context : RemainderContext source) (event : B) : B :=
  (MotherArenaHigher.pair rank) (remainderContextEmbedding coordinates ledger context, event)

/-- A remainder event forms both entire tables and both dependent
certification sections. Neither direction is inferred by inversion. -/
structure RemainderCheck (material wholeMaterial : M) : Prop where
  tables : ∀ (context : RemainderContext source) (event : RemainderEvent coordinates ledger material context),
    MotherArenaCompiler.WriteCheck ledger wholeMaterial (remainderEventKey coordinates ledger context event.val) context.1.2.1 context.2
  destination : ∀ (context : RemainderContext source) (event : RemainderEvent coordinates ledger material context)
      (entry : OpenResponsibilityAt N context.1.2.1),
    let whole := MotherArenaCompiler.write ledger wholeMaterial (remainderEventKey coordinates ledger context event.val) _ _ (tables context event)
    ∃! output : operations.Exact (destinationContext context whole entry),
      r3 material 2 (remainderEventKey coordinates ledger context event.val) (ledger.entry context.1.2.1 entry)
        (exactCode (destinationContext context whole entry) output)
  origin : ∀ (context : RemainderContext source) (event : RemainderEvent coordinates ledger material context)
      (entry : OpenResponsibilityAt N context.2),
    let whole := MotherArenaCompiler.write ledger wholeMaterial (remainderEventKey coordinates ledger context event.val) _ _ (tables context event)
    ∃! output : operations.Exact (originContext context whole entry),
      r3 material 3 (remainderEventKey coordinates ledger context event.val) (ledger.entry context.2 entry)
        (exactCode (originContext context whole entry) output)
  selected_unique : ∀ (context : RemainderContext source) (left right : RemainderEvent coordinates ledger material context),
    r2 material 1 (remainderContextEmbedding coordinates ledger context) left.val →
    r2 material 1 (remainderContextEmbedding coordinates ledger context) right.val → left = right

def remainderSelected? (material : M) (context : RemainderContext source) : Option (RemainderEvent coordinates ledger material context) :=
  if selected : ∃ event : RemainderEvent coordinates ledger material context,
      r2 material 1 (remainderContextEmbedding coordinates ledger context) event.val then
    some (Classical.choose selected)
  else none

def generatedWriteSource (rowMaterial remainderMaterial wholeMaterial : M)
    (rowCheck : WriteRowCheck coordinates ledger operations exactCode rowMaterial)
    (remainderCheck : RemainderCheck coordinates ledger operations exactCode remainderMaterial wholeMaterial) :
    LedgerWriteRowSourceAt source operations.exactTransitionAt where
  IncidenceOccurrenceAt := fun {current} event {target} a b =>
    WriteEvent coordinates ledger rowMaterial ⟨current, event, target, a, b⟩
  compileEvolution := fun {current} {event} {target} {a} {b} value =>
    (Classical.choose (rowCheck ⟨current, event, target, a, b⟩ value)).1
  compileExact := fun {current} {event} {target} {a} {b} value =>
    (Classical.choose (rowCheck ⟨current, event, target, a, b⟩ value)).2
  transportedRemainderSource := {
    OccurrenceAt := fun {current} event target => RemainderEvent coordinates ledger remainderMaterial (⟨current, event⟩, target)
    emit? := fun {current} event target => remainderSelected? coordinates ledger remainderMaterial (⟨current, event⟩, target)
    compileEvolution := fun {current} {event} {target} value =>
      MotherArenaCompiler.write ledger wholeMaterial (remainderEventKey coordinates ledger (⟨current, event⟩, target) value.val) event.1 target
        (remainderCheck.tables (⟨current, event⟩, target) value)
    compileExact := fun {current} {event} {target} value => {
      destination := fun entry => Classical.choose (remainderCheck.destination (⟨current, event⟩, target) value entry)
      origin := fun entry => Classical.choose (remainderCheck.origin (⟨current, event⟩, target) value entry) } }

def formWriteProgramParts (parent rowMaterial remainderMaterial wholeMaterial : M) : Option WriteProgramValue :=
  (formTransitions parent).pbind (fun ⟨value, compiled, terminal, operations⟩ formed =>
    let terminalParent := ((MotherArenaHigher.split rank) parent).1
    let base := ((MotherArenaHigher.split rank) terminalParent).1
    let terminalFormed := transitions_terminal_formed parent value compiled terminal operations formed
    let compiledFormed := terminal_compilation_formed terminalParent value compiled terminal terminalFormed
    let coordinates := MotherArenaPrograms.coordinatesOfCompilation base value compiled compiledFormed
    let ledger := MotherArenaPrograms.ledgerCoordinatesOfCompilation base value compiled compiledFormed
    let exactCode := exactCoordinatesOfTransitions parent ⟨value, compiled, terminal, operations⟩ formed
    if rowCheck : WriteRowCheck coordinates ledger operations exactCode rowMaterial then
      if remainderCheck : RemainderCheck coordinates ledger operations exactCode remainderMaterial wholeMaterial then
        some ⟨value, compiled, terminal, operations,
          generatedWriteSource coordinates ledger operations exactCode rowMaterial remainderMaterial wholeMaterial rowCheck remainderCheck⟩
      else none
    else none)

/-- One material forms the original complete MotherArenaCompiler.write source, including its
remainder law; all type-valued operands come from the actual parent factory. -/
def formWritePrograms (material : M) : Option WriteProgramValue :=
  let first := (MotherArenaHigher.split rank) material
  let second := (MotherArenaHigher.split rank) first.2
  let third := (MotherArenaHigher.split rank) second.2
  formWriteProgramParts first.1 second.1 third.1 third.2

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
