import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Ledger.GeneratedRows

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def Presentation.terminalEvent {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    (event : source.toRootSource.actual.OccurrenceAt current) (entry : OpenResponsibilityAt N event.1)
    (value : compiler.terminalRowSource.IncidenceOccurrenceAt event entry) :
    (p.terminalSource compiler).IncidenceOccurrenceAt (p.eventEquiv source current event) (p.ledger event.1 entry) :=
  Program.input (p.terminalProgram_at compiler ⟨current, event, entry⟩) value

def Presentation.terminalRow {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    {event : source.toRootSource.actual.OccurrenceAt current} {entry : OpenResponsibilityAt N event.1}
    (row : GeneratedLedgerTerminalRowAt compiler.terminalRowSource event entry) :
    GeneratedLedgerTerminalRowAt (p.terminalSource compiler) (p.eventEquiv source current event)
      (p.ledger event.1 entry) :=
  (p.terminalSource compiler).generate (p.terminalEvent compiler event entry row.event)

theorem Presentation.terminalRow_value {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    {event : source.toRootSource.actual.OccurrenceAt current} {entry : OpenResponsibilityAt N event.1}
    (row : GeneratedLedgerTerminalRowAt compiler.terminalRowSource event entry) :
    (p.terminalRow compiler row).terminal = p.terminalRowEquiv entry row.terminal :=
  (Program.compile_input (p.terminalProgram_at compiler ⟨current, event, entry⟩) row.event).trans
    (congrArg (p.terminalRowEquiv entry) row.terminal_eq)

def Presentation.settlementEvent {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    (event : source.toRootSource.actual.OccurrenceAt current)
    (value : compiler.terminalRowSource.supportSettlementSource.OccurrenceAt event) :
    (p.settlementSource compiler).OccurrenceAt (p.eventEquiv source current event) :=
  SelectedProgram.input (p.settlementProgram_at compiler ⟨current, event⟩) value

def sealSettlement {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} (rowSource : LedgerTerminalRowSourceAt source)
    {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current)
    (value : rowSource.supportSettlementSource.OccurrenceAt event)
    (selected : rowSource.supportSettlementSource.emit? event = some value) :
    GeneratedLedgerSupportSettlementAt rowSource event :=
  (rowSource.generateSupportSettlement? event).get (by
    unfold LedgerTerminalRowSourceAt.generateSupportSettlement?
    split
    · rename_i absent
      have impossible := selected.symm.trans absent
      cases impossible
    · rfl)

theorem sealSettlement_event {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} (rowSource : LedgerTerminalRowSourceAt source)
    {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current)
    (value : rowSource.supportSettlementSource.OccurrenceAt event)
    (selected : rowSource.supportSettlementSource.emit? event = some value) :
    (sealSettlement rowSource event value selected).event = value := by
  have produced : rowSource.generateSupportSettlement? event =
      some (sealSettlement rowSource event value selected) :=
    (Option.some_get _).symm
  unfold LedgerTerminalRowSourceAt.generateSupportSettlement? at produced
  split at produced
  · cases produced
  · rename_i emitted emitted_eq
    have generated_eq := congrArg GeneratedLedgerSupportSettlementAt.event (Option.some.inj produced)
    exact generated_eq.symm.trans (Option.some.inj (emitted_eq.symm.trans selected))

def Presentation.settlement {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    {event : source.toRootSource.actual.OccurrenceAt current}
    (value : GeneratedLedgerSupportSettlementAt compiler.terminalRowSource event) :
    GeneratedLedgerSupportSettlementAt (p.terminalSource compiler) (p.eventEquiv source current event) := by
  refine sealSettlement (p.terminalSource compiler) (p.eventEquiv source current event)
    (p.settlementEvent compiler event value.event) ?_
  exact (SelectedProgram.emit_input (p.settlementProgram_at compiler ⟨current, event⟩)).symm.trans
    (congrArg (Option.map (p.settlementEvent compiler event)) value.selected)

theorem Presentation.settlement_receipt {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    {event : source.toRootSource.actual.OccurrenceAt current}
    (value : GeneratedLedgerSupportSettlementAt compiler.terminalRowSource event) :
    (p.settlement compiler value).receipt = p.dispositionAt event.1 .supportSettlement value.receipt := by
  change (p.settlementSource compiler).compile (p.settlement compiler value).event = _
  rw [show (p.settlement compiler value).event = p.settlementEvent compiler event value.event from
    sealSettlement_event _ _ _ _]
  exact SelectedProgram.compile_input (p.settlementProgram_at compiler ⟨current, event⟩) value.event

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
