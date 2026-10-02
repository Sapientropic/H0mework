import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Ledger.TerminalSources

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def SelectedProgram.input {Output : Type} {left right : SelectedProgram Output}
    (same : left = right) (value : right.Event) : left.Event :=
  Program.input (congrArg SelectedProgram.toProgram same) value

theorem SelectedProgram.compile_input {Output : Type} {left right : SelectedProgram Output}
    (same : left = right) (value : right.Event) :
    left.compile (SelectedProgram.input same value) = right.compile value := by
  cases same
  rfl

theorem SelectedProgram.emit_input {Output : Type} {left right : SelectedProgram Output}
    (same : left = right) : Option.map (SelectedProgram.input same) right.emit = left.emit := by
  cases same
  cases left.emit <;> rfl

def Presentation.writeEvent {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    (event : source.toRootSource.actual.OccurrenceAt current) {target : N.Support}
    (a : OpenResponsibilityAt N event.1) (b : OpenResponsibilityAt N target)
    (value : compiler.writeRowSource.IncidenceOccurrenceAt event a b) :
    (p.writeRowSource compiler).IncidenceOccurrenceAt (p.eventEquiv source current event)
      (p.ledger event.1 a) (p.ledger target b) :=
  Program.input (p.rowProgram_at compiler ⟨current, event, target, a, b⟩) value

def Presentation.writeRow {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    {event : source.toRootSource.actual.OccurrenceAt current} {target : N.Support}
    {a : OpenResponsibilityAt N event.1} {b : OpenResponsibilityAt N target}
    (row : GeneratedLedgerWriteRowAt compiler.writeRowSource event a b) :
    GeneratedLedgerWriteRowAt (p.writeRowSource compiler) (p.eventEquiv source current event)
      (p.ledger event.1 a) (p.ledger target b) :=
  (p.writeRowSource compiler).generate (p.writeEvent compiler event a b row.event)

theorem Presentation.writeRow_evolution {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    {event : source.toRootSource.actual.OccurrenceAt current} {target : N.Support}
    {a : OpenResponsibilityAt N event.1} {b : OpenResponsibilityAt N target}
    (row : GeneratedLedgerWriteRowAt compiler.writeRowSource event a b) :
    (p.writeRow compiler row).evolution = p.mapRow row.evolution := by
  have same := congrArg Prod.fst (Program.compile_input
    (p.rowProgram_at compiler ⟨current, event, target, a, b⟩) row.event)
  exact same.trans (congrArg p.mapRow row.evolution_eq)

theorem Presentation.writeRow_exact {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    {event : source.toRootSource.actual.OccurrenceAt current} {target : N.Support}
    {a : OpenResponsibilityAt N event.1} {b : OpenResponsibilityAt N target}
    (row : GeneratedLedgerWriteRowAt compiler.writeRowSource event a b) :
    (p.writeRow compiler row).exact = p.mapExact compiler event a b row.exact := by
  have same := congrArg Prod.snd (Program.compile_input
    (p.rowProgram_at compiler ⟨current, event, target, a, b⟩) row.event)
  exact same.trans (congrArg (p.mapExact compiler event a b) row.exact_eq)

def Presentation.remainderEvent {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    (event : source.toRootSource.actual.OccurrenceAt current) (target : N.Support)
    (value : compiler.writeRowSource.transportedRemainderSource.OccurrenceAt event target) :
    (p.remainderSource compiler).OccurrenceAt (p.eventEquiv source current event) (p.support target) :=
  SelectedProgram.input (p.remainderProgram_at compiler (⟨current, event⟩, target)) value

def Presentation.remainder {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    {event : source.toRootSource.actual.OccurrenceAt current} {target : N.Support}
    (value : GeneratedLedgerTransportedRemainderAt compiler.writeRowSource event ⟨target⟩) :
    GeneratedLedgerTransportedRemainderAt (p.writeRowSource compiler)
      (p.eventEquiv source current event) ⟨p.support target⟩ := by
  refine (p.writeRowSource compiler).generateTransportedRemainder
    (p.eventEquiv source current event) ⟨p.support target⟩
    (p.remainderEvent compiler event target value.event) ?_
  have same := (SelectedProgram.emit_input
    (p.remainderProgram_at compiler (⟨current, event⟩, target))).symm
  change (p.remainderSource compiler).emit? (p.eventEquiv source current event) (p.support target) =
    some (p.remainderEvent compiler event target value.event)
  exact same.trans (congrArg (Option.map (p.remainderEvent compiler event target)) value.selected)

theorem Presentation.remainder_evolution {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    {event : source.toRootSource.actual.OccurrenceAt current} {target : N.Support}
    (value : GeneratedLedgerTransportedRemainderAt compiler.writeRowSource event ⟨target⟩) :
    (p.remainder compiler value).evolution = p.wholeLedgerEquiv event.1 target value.evolution :=
  congrArg Sigma.fst (SelectedProgram.compile_input
    (p.remainderProgram_at compiler (⟨current, event⟩, target)) value.event)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
