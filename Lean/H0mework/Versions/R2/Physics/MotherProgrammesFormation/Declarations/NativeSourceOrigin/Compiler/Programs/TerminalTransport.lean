import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Terminal
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Ledger.GeneratedRows

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourcePrograms
open MotherFullCompiler
open MotherNetworkOrigin (Program SelectedProgram)
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

abbrev Receipt {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (point : Point source) := N.DispositionAt point.2.1 .supportSettlement

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)

def rowContextEquiv : RowContext original ≃ RowContext generated :=
  Equiv.sigmaCongr (pointEquiv p) (fun point => (n.ledger point.2.1).trans
    (Equiv.cast (congrArg (OpenResponsibilityAt G) (p.support_eq point.1 point.2).symm)))

def receiptEquiv (point : Point original) : Receipt point ≃ Receipt (pointEquiv p point) :=
  (n.dispositionAt point.2.1 .supportSettlement).trans
    (Equiv.cast (congrArg (fun support => G.DispositionAt support .supportSettlement)
      (p.support_eq point.1 point.2).symm))

def terminalImage (rows : LedgerTerminalRowSourceAt original) (context : RowContext original) :
    Program (Receipt (rowContextEquiv p context).1) where
  Event := rows.IncidenceOccurrenceAt context.1.2 context.2
  compile := fun event => receiptEquiv p context.1 (rows.compile event).receipt

def settlementImage (rows : LedgerTerminalRowSourceAt original) (point : Point original) :
    SelectedProgram (Receipt (pointEquiv p point)) where
  Event := rows.supportSettlementSource.OccurrenceAt point.2
  emit := rows.supportSettlementSource.emit? point.2
  compile := fun event => receiptEquiv p point (rows.supportSettlementSource.compile event)

def terminalProgram (rows : LedgerTerminalRowSourceAt original) :
    (context : RowContext generated) → Program (Receipt context.1) :=
  Equiv.piCongrLeft _ (rowContextEquiv p) (terminalImage p rows)

def settlementProgram (rows : LedgerTerminalRowSourceAt original) :
    (point : Point generated) → SelectedProgram (Receipt point) :=
  Equiv.piCongrLeft _ (pointEquiv p) (settlementImage p rows)

theorem terminalProgram_at (rows : LedgerTerminalRowSourceAt original) (context : RowContext original) :
    terminalProgram p rows (rowContextEquiv p context) = terminalImage p rows context :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

theorem settlementProgram_at (rows : LedgerTerminalRowSourceAt original) (point : Point original) :
    settlementProgram p rows (pointEquiv p point) = settlementImage p rows point :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

/-- Whole programs are reindexed, retaining both complete event types and
the actual source selector. Receipt casts follow exact support equality. -/
def transportedTerminal (rows : LedgerTerminalRowSourceAt original) : LedgerTerminalRowSourceAt generated where
  IncidenceOccurrenceAt := fun {current} occurrence entry => (terminalProgram p rows ⟨⟨current, occurrence⟩, entry⟩).Event
  compile := fun {current} {occurrence} {entry} event =>
    ⟨(terminalProgram p rows ⟨⟨current, occurrence⟩, entry⟩).compile event⟩
  supportSettlementSource := {
    OccurrenceAt := fun {current} occurrence => (settlementProgram p rows ⟨current, occurrence⟩).Event
    emit? := fun {current} occurrence => (settlementProgram p rows ⟨current, occurrence⟩).emit
    compile := fun {current} {occurrence} event => (settlementProgram p rows ⟨current, occurrence⟩).compile event }

def terminalEventEquiv (rows : LedgerTerminalRowSourceAt original) (context : RowContext original) :
    rows.IncidenceOccurrenceAt context.1.2 context.2 ≃
      (transportedTerminal p rows).IncidenceOccurrenceAt (rowContextEquiv p context).1.2 (rowContextEquiv p context).2 :=
  Equiv.cast (congrArg Program.Event (terminalProgram_at p rows context)).symm

def settlementEventEquiv (rows : LedgerTerminalRowSourceAt original) (point : Point original) :
    rows.supportSettlementSource.OccurrenceAt point.2 ≃
      (transportedTerminal p rows).supportSettlementSource.OccurrenceAt (pointEquiv p point).2 :=
  Equiv.cast (congrArg (fun program : SelectedProgram (Receipt (pointEquiv p point)) => program.Event)
    (settlementProgram_at p rows point)).symm

theorem terminal_compile (rows : LedgerTerminalRowSourceAt original) (context : RowContext original)
    (event : rows.IncidenceOccurrenceAt context.1.2 context.2) :
    ((transportedTerminal p rows).compile (terminalEventEquiv p rows context event)).receipt =
      receiptEquiv p context.1 (rows.compile event).receipt :=
  Program.compile_input (terminalProgram_at p rows context) event

theorem settlement_compile (rows : LedgerTerminalRowSourceAt original) (point : Point original)
    (event : rows.supportSettlementSource.OccurrenceAt point.2) :
    (transportedTerminal p rows).supportSettlementSource.compile (settlementEventEquiv p rows point event) =
      receiptEquiv p point (rows.supportSettlementSource.compile event) :=
  SelectedProgram.compile_input (settlementProgram_at p rows point) event

theorem settlement_emit (rows : LedgerTerminalRowSourceAt original) (point : Point original) :
    Option.map (settlementEventEquiv p rows point) (rows.supportSettlementSource.emit? point.2) =
      (transportedTerminal p rows).supportSettlementSource.emit? (pointEquiv p point).2 :=
  SelectedProgram.emit_input (settlementProgram_at p rows point)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourcePrograms
