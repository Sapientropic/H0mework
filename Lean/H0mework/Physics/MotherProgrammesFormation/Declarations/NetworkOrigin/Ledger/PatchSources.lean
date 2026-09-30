import H0mework.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Ledger.Contexts

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

abbrev ExactField {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} (compiler : SourceNativeLedgerCompiler source) (ctx : RowContext source) :=
  compiler.ExactTransitionAt ctx.2.1 ctx.2.2.2.1 ctx.2.2.2.2

def Presentation.exactTransition {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source)
    {current : V.Current} (event : (p.source source).toRootSource.actual.OccurrenceAt current)
    {target : G.Support} (a : OpenResponsibilityAt G event.1) (b : OpenResponsibilityAt G target) : Type :=
  ExactField compiler ((p.rowContextEquiv source).symm ⟨current, event, target, a, b⟩)

def Presentation.mapExact {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source)
    {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current)
    {target : N.Support} (a : OpenResponsibilityAt N event.1) (b : OpenResponsibilityAt N target)
    (value : compiler.ExactTransitionAt event a b) :
    p.exactTransition compiler (p.eventEquiv source current event) (p.ledger event.1 a) (p.ledger target b) :=
  Eq.mp (congrArg (ExactField compiler)
    ((p.rowContextEquiv source).symm_apply_apply ⟨current, event, target, a, b⟩).symm) value

def Presentation.mapCertification {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source)
    {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current)
    {target : N.Support} (whole : LedgerWriteEvolutionAt N ⟨event.1⟩ ⟨target⟩)
    (exact : ExactLedgerWriteCertificationAt N ⟨event.1⟩ ⟨target⟩ (compiler.ExactTransitionAt event) whole) :
    ExactLedgerWriteCertificationAt G ⟨p.support event.1⟩ ⟨p.support target⟩
      (p.exactTransition compiler (p.eventEquiv source current event))
      (p.wholeLedgerEquiv event.1 target whole) where
  destination := Equiv.piCongrLeft _ (p.ledger event.1) (fun a => by
    rw [p.whole_destination]
    exact p.mapExact compiler event a (whole.destination a).1 (exact.destination a))
  origin := Equiv.piCongrLeft _ (p.ledger target) (fun b => by
    rw [p.whole_origin]
    exact p.mapExact compiler event (whole.origin b).1 b (exact.origin b))

/-- A dependent source section keeps its event carrier and whole output together. -/
structure Program (Output : Type) : Type 1 where
  Event : Type
  compile : Event → Output

structure SelectedProgram (Output : Type) extends Program Output where
  emit : Option Event

abbrev RemainderProgram {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} (Exact : RowContext source → Type) (ctx : RemainderContext source) :=
  SelectedProgram (Σ whole : WholeValue ctx,
    ExactLedgerWriteCertificationAt N ⟨ctx.1.2.1⟩ ⟨ctx.2⟩
      (fun a b => Exact ⟨ctx.1.1, ctx.1.2, ctx.2, a, b⟩) whole)

abbrev RowProgram {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} (Exact : RowContext source → Type) (ctx : RowContext source) :=
  Program (RowValue ctx × Exact ctx)

def Program.input {Output : Type} {left right : Program Output}
    (same : left = right) (value : right.Event) : left.Event :=
  Eq.mp (congrArg Program.Event same.symm) value

theorem Program.compile_input {Output : Type} {left right : Program Output}
    (same : left = right) (value : right.Event) :
    left.compile (Program.input same value) = right.compile value := by
  cases same
  rfl

def Presentation.remainderImage {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) (ctx : RemainderContext source) :
    RemainderProgram (fun ctx => ExactField compiler ((p.rowContextEquiv source).symm ctx))
      (p.remainderContextEquiv source ctx) where
  Event := compiler.writeRowSource.transportedRemainderSource.OccurrenceAt ctx.1.2 ctx.2
  emit := compiler.writeRowSource.transportedRemainderSource.emit? ctx.1.2 ctx.2
  compile := fun event =>
    ⟨p.wholeLedgerEquiv ctx.1.2.1 ctx.2
        (compiler.writeRowSource.transportedRemainderSource.compileEvolution event),
      p.mapCertification compiler ctx.1.2 _
        (compiler.writeRowSource.transportedRemainderSource.compileExact event)⟩

def Presentation.rowImage {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) (ctx : RowContext source) :
    RowProgram (fun ctx => ExactField compiler ((p.rowContextEquiv source).symm ctx))
      (p.rowContextEquiv source ctx) where
  Event := compiler.writeRowSource.IncidenceOccurrenceAt ctx.2.1 ctx.2.2.2.1 ctx.2.2.2.2
  compile := fun event =>
    ⟨p.mapRow (compiler.writeRowSource.compileEvolution event),
      p.mapExact compiler ctx.2.1 ctx.2.2.2.1 ctx.2.2.2.2
        (compiler.writeRowSource.compileExact event)⟩

def Presentation.remainderProgram {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) :
    (ctx : RemainderContext (p.source source)) →
      RemainderProgram (fun ctx => ExactField compiler ((p.rowContextEquiv source).symm ctx)) ctx :=
  Equiv.piCongrLeft _ (p.remainderContextEquiv source) (p.remainderImage compiler)

def Presentation.rowProgram {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) :
    (ctx : RowContext (p.source source)) →
      RowProgram (fun ctx => ExactField compiler ((p.rowContextEquiv source).symm ctx)) ctx :=
  Equiv.piCongrLeft _ (p.rowContextEquiv source) (p.rowImage compiler)

theorem Presentation.rowProgram_at {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) (ctx : RowContext source) :
    p.rowProgram compiler (p.rowContextEquiv source ctx) = p.rowImage compiler ctx :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

theorem Presentation.remainderProgram_at {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) (ctx : RemainderContext source) :
    p.remainderProgram compiler (p.remainderContextEquiv source ctx) = p.remainderImage compiler ctx :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

def Presentation.remainderSource {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) :
    LedgerTransportedRemainderSourceAt (p.source source) (p.exactTransition compiler) where
  OccurrenceAt := fun {current} event target => (p.remainderProgram compiler (⟨current, event⟩, target)).Event
  emit? := fun {current} event target => (p.remainderProgram compiler (⟨current, event⟩, target)).emit
  compileEvolution := fun {current} {event} {target} value =>
    ((p.remainderProgram compiler (⟨current, event⟩, target)).compile value).1
  compileExact := fun {current} {event} {target} value =>
    ((p.remainderProgram compiler (⟨current, event⟩, target)).compile value).2

def Presentation.writeRowSource {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) :
    LedgerWriteRowSourceAt (p.source source) (p.exactTransition compiler) where
  IncidenceOccurrenceAt := fun {current} event {target} a b =>
    (p.rowProgram compiler ⟨current, event, target, a, b⟩).Event
  compileEvolution := fun {current} {event} {target} {a} {b} value =>
    ((p.rowProgram compiler ⟨current, event, target, a, b⟩).compile value).1
  compileExact := fun {current} {event} {target} {a} {b} value =>
    ((p.rowProgram compiler ⟨current, event, target, a, b⟩).compile value).2
  transportedRemainderSource := p.remainderSource compiler

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
