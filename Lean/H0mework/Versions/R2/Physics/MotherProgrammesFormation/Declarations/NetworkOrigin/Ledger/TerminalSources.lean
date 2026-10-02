import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Ledger.PatchSources

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

abbrev SettlementValue {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} (ctx : EventContext source) :=
  N.DispositionAt ctx.2.1 .supportSettlement

def Presentation.terminalImage {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) (ctx : TerminalContext source) :
    Program (TerminalValue (p.terminalContextEquiv source ctx)) where
  Event := compiler.terminalRowSource.IncidenceOccurrenceAt ctx.2.1 ctx.2.2
  compile := fun event => p.terminalRowEquiv ctx.2.2 (compiler.terminalRowSource.compile event)

def Presentation.settlementImage {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) (ctx : EventContext source) :
    SelectedProgram (SettlementValue (p.eventContextEquiv source ctx)) where
  Event := compiler.terminalRowSource.supportSettlementSource.OccurrenceAt ctx.2
  emit := compiler.terminalRowSource.supportSettlementSource.emit? ctx.2
  compile := fun event => p.dispositionAt ctx.2.1 .supportSettlement
    (compiler.terminalRowSource.supportSettlementSource.compile event)

def Presentation.terminalProgram {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) :
    (ctx : TerminalContext (p.source source)) → Program (TerminalValue ctx) :=
  Equiv.piCongrLeft _ (p.terminalContextEquiv source) (p.terminalImage compiler)

def Presentation.settlementProgram {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) :
    (ctx : EventContext (p.source source)) → SelectedProgram (SettlementValue ctx) :=
  Equiv.piCongrLeft _ (p.eventContextEquiv source) (p.settlementImage compiler)

theorem Presentation.terminalProgram_at {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) (ctx : TerminalContext source) :
    p.terminalProgram compiler (p.terminalContextEquiv source ctx) = p.terminalImage compiler ctx :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

theorem Presentation.settlementProgram_at {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) (ctx : EventContext source) :
    p.settlementProgram compiler (p.eventContextEquiv source ctx) = p.settlementImage compiler ctx :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

def Presentation.settlementSource {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) : LedgerSupportSettlementSourceAt (p.source source) where
  OccurrenceAt := fun {current} event => (p.settlementProgram compiler ⟨current, event⟩).Event
  emit? := fun {current} event => (p.settlementProgram compiler ⟨current, event⟩).emit
  compile := fun {current} {event} value => (p.settlementProgram compiler ⟨current, event⟩).compile value

def Presentation.terminalSource {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) : LedgerTerminalRowSourceAt (p.source source) where
  IncidenceOccurrenceAt := fun {current} event entry => (p.terminalProgram compiler ⟨current, event, entry⟩).Event
  compile := fun {current} {event} {entry} value => (p.terminalProgram compiler ⟨current, event, entry⟩).compile value
  supportSettlementSource := p.settlementSource compiler

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
