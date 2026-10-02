import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Ledger.Source

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

abbrev EventContext {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (source : SourceNativeSource N V) := Σ c : V.Current, source.toRootSource.actual.OccurrenceAt c

abbrev RemainderContext {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (source : SourceNativeSource N V) := EventContext source × N.Support

abbrev RowContext {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (source : SourceNativeSource N V) :=
  Σ c : V.Current, Σ event : source.toRootSource.actual.OccurrenceAt c,
    Σ t : N.Support, OpenResponsibilityAt N event.1 × OpenResponsibilityAt N t

abbrev TerminalContext {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (source : SourceNativeSource N V) :=
  Σ c : V.Current, Σ event : source.toRootSource.actual.OccurrenceAt c,
    OpenResponsibilityAt N event.1

def Presentation.eventContextEquiv {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} (source : SourceNativeSource N V) :
    EventContext source ≃ EventContext (p.source source) :=
  Equiv.sigmaCongr (Equiv.refl V.Current) (p.eventEquiv source)

def Presentation.remainderContextEquiv {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} (source : SourceNativeSource N V) :
    RemainderContext source ≃ RemainderContext (p.source source) :=
  Equiv.prodCongr (p.eventContextEquiv source) p.support

def Presentation.rowContextEquiv {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} (source : SourceNativeSource N V) :
    RowContext source ≃ RowContext (p.source source) :=
  Equiv.sigmaCongr (Equiv.refl V.Current) (fun c =>
    Equiv.sigmaCongr (p.eventEquiv source c) (fun event =>
      Equiv.sigmaCongr p.support (fun t => Equiv.prodCongr (p.ledger event.1) (p.ledger t))))

def Presentation.terminalContextEquiv {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} (source : SourceNativeSource N V) :
    TerminalContext source ≃ TerminalContext (p.source source) :=
  Equiv.sigmaCongr (Equiv.refl V.Current) (fun c =>
    Equiv.sigmaCongr (p.eventEquiv source c) (fun event => p.ledger event.1))

abbrev RowValue {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} (ctx : RowContext source) :=
  LedgerEntryEvolutionAt N ctx.2.2.2.1 ctx.2.2.2.2

abbrev WholeValue {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} (ctx : RemainderContext source) :=
  LedgerWriteEvolutionAt N ⟨ctx.1.2.1⟩ ⟨ctx.2⟩

abbrev TerminalValue {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} (ctx : TerminalContext source) := LedgerEntryTerminalAt N ctx.2.2


end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
