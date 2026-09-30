import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Context

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourcePrograms
open MotherNetworkFactory MotherFullCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : Coordinates source) (ledgerCoordinates : LedgerCoordinates N)

abbrev TerminalEvent (material : M) (context : RowContext source) :=
  {event : B // r2 material 0 (rowContextEmbedding coordinates ledgerCoordinates context) event}

abbrev SettlementEvent (material : M) (point : Point source) :=
  {event : B // r2 material 1 (coordinates.occurrence point) event}

def selected? (material : M) (point : Point source) : Option (SettlementEvent coordinates material point) :=
  if selected : ∃ event : SettlementEvent coordinates material point,
      r2 material 4 (coordinates.occurrence point) event.val then
    some (Classical.choose selected)
  else none

structure TerminalCheck (material : M) : Prop where
  row : ∀ (context : RowContext source) (event : TerminalEvent coordinates ledgerCoordinates material context),
    ∃! receipt : N.DispositionAt context.1.2.1 .supportSettlement,
      r3 material 2 (rowContextEmbedding coordinates ledgerCoordinates context) event.val
        (ledgerCoordinates.settlement context.1.2.1 receipt)
  settlement : ∀ (point : Point source) (event : SettlementEvent coordinates material point),
    ∃! receipt : N.DispositionAt point.2.1 .supportSettlement,
      r3 material 3 (coordinates.occurrence point) event.val (ledgerCoordinates.settlement point.2.1 receipt)
  selected_unique : ∀ (point : Point source) (left right : SettlementEvent coordinates material point),
    r2 material 4 (coordinates.occurrence point) left.val →
    r2 material 4 (coordinates.occurrence point) right.val → left = right

/-- Both complete event families and both actual receipt compilers are source
fields. None in the selector leaves its unselected event family intact. -/
def terminalRows (material : M) (checked : TerminalCheck coordinates ledgerCoordinates material) :
    LedgerTerminalRowSourceAt source where
  IncidenceOccurrenceAt := fun {current} occurrence entry =>
    TerminalEvent coordinates ledgerCoordinates material ⟨⟨current, occurrence⟩, entry⟩
  compile := fun {current} {occurrence} {entry} event =>
    ⟨Classical.choose (checked.row ⟨⟨current, occurrence⟩, entry⟩ event)⟩
  supportSettlementSource := {
    OccurrenceAt := fun {current} occurrence => SettlementEvent coordinates material ⟨current, occurrence⟩
    emit? := fun {current} occurrence => selected? coordinates material ⟨current, occurrence⟩
    compile := fun {current} {occurrence} event => Classical.choose (checked.settlement ⟨current, occurrence⟩ event) }

theorem selected_of_emitted (material : M) (point : Point source)
    (event : SettlementEvent coordinates material point) (emitted : selected? coordinates material point = some event) :
    r2 material 4 (coordinates.occurrence point) event.val := by
  unfold selected? at emitted
  split at emitted
  · rename_i existsEvent
    have same := Option.some.inj emitted
    exact same ▸ Classical.choose_spec existsEvent
  · cases emitted

theorem emitted_of_selected (material : M) (checked : TerminalCheck coordinates ledgerCoordinates material)
    (point : Point source) (event : SettlementEvent coordinates material point)
    (selected : r2 material 4 (coordinates.occurrence point) event.val) : selected? coordinates material point = some event := by
  have existsEvent : ∃ e : SettlementEvent coordinates material point, r2 material 4 (coordinates.occurrence point) e.val :=
    ⟨event, selected⟩
  unfold selected?
  rw [dif_pos existsEvent]
  exact congrArg some (checked.selected_unique point _ event (Classical.choose_spec existsEvent) selected)

/-- The original terminal source declaration is formed together with the
already generated complete compilation section from one mother material. -/
def formTerminalSource (material : M) :
    Option (Σ value : SourceValue, CompilationSection value.2.2 × LedgerTerminalRowSourceAt value.2.2) :=
  let parts := MotherHigherLawValue.split material
  (formCompilation parts.1).pbind (fun ⟨value, compiled⟩ formed =>
    let coordinates := coordinatesOfCompilation parts.1 value compiled formed
    let ledgerCoordinates := ledgerCoordinatesOfCompilation parts.1 value compiled formed
    if checked : TerminalCheck coordinates ledgerCoordinates parts.2 then
      some ⟨value, compiled, terminalRows coordinates ledgerCoordinates parts.2 checked⟩
    else none)

theorem terminal_source_formed (parent material : M) (value : SourceValue)
    (compiled : CompilationSection value.2.2) (formed : formCompilation parent = some ⟨value, compiled⟩)
    (checked : TerminalCheck (coordinatesOfCompilation parent value compiled formed)
      (ledgerCoordinatesOfCompilation parent value compiled formed) material) :
    formTerminalSource (MotherHigherLawValue.pack (parent, material)) =
      some ⟨value, compiled, terminalRows (coordinatesOfCompilation parent value compiled formed)
        (ledgerCoordinatesOfCompilation parent value compiled formed) material checked⟩ := by
  unfold formTerminalSource
  rw [MotherHigherLawValue.split_pack]
  dsimp only
  apply Option.pbind_eq_some_iff.mpr
  refine ⟨⟨value, compiled⟩, formed, ?_⟩
  exact dif_pos checked

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourcePrograms
