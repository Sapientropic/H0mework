import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Ledger.Whole
import H0mework.Foundation.Ledger.Evolution

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

/-- Rechart the original complete event algebra over the generated network.
The original event and its current remain in the dependent value. -/
def Presentation.source {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} (original : SourceNativeSource N V) : SourceNativeSource G V where
  initial := original.initial
  law := {
    EventAt := fun current support =>
      { event : original.toRootSource.actual.OccurrenceAt current // p.support event.1 = support }
    compile := fun event => original.toRootSource.actual.compile event.val
    AffectedInventoryAt := fun event => original.law.AffectedInventoryAt event.val.2
    affectedInventoryPresentation := fun event => by
      rcases event with ⟨event, same⟩
      cases same
      exact (original.law.affectedInventoryPresentation event.2).trans {
        forward := p.ledger event.1, backward := (p.ledger event.1).symm,
        forward_backward := (p.ledger event.1).right_inv,
        backward_forward := (p.ledger event.1).left_inv }
    anchorKey := fun a => p.anchor (original.law.anchorKey a)
    incidenceKey := fun a => p.incidence (original.law.incidenceKey a)
    lineageKey := fun a => p.lineage (original.law.lineageKey a)
    anchor_commutes := fun event => by
      rcases event with ⟨event, same⟩
      cases same
      exact (congrArg p.anchor (original.law.anchor_commutes event.2)).trans (p.anchor_commutes event.1).symm
    incidence_commutes := fun event => by
      rcases event with ⟨event, same⟩
      cases same
      exact (congrArg p.incidence (original.law.incidence_commutes event.2)).trans (p.incidence_commutes event.1).symm
    lineage_commutes := fun event => by
      rcases event with ⟨event, same⟩
      cases same
      exact (congrArg p.lineage (original.law.lineage_commutes event.2)).trans (p.lineage_commutes event.1).symm }

def Presentation.eventEquiv {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} (original : SourceNativeSource N V) (current : V.Current) :
    original.toRootSource.actual.OccurrenceAt current ≃
      (p.source original).toRootSource.actual.OccurrenceAt current where
  toFun := fun event => ⟨p.support event.1, ⟨event, rfl⟩⟩
  invFun := fun event => event.2.val
  left_inv := fun _ => rfl
  right_inv := by
    rintro ⟨support, ⟨event, same⟩⟩
    cases same
    rfl

theorem Presentation.event_compile {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} (original : SourceNativeSource N V)
    {current : V.Current} (event : original.toRootSource.actual.OccurrenceAt current) :
    (p.source original).toRootSource.actual.compile (p.eventEquiv original current event) =
      original.toRootSource.actual.compile event := rfl

def Presentation.mapCompilation {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {original : SourceNativeSource N V}
    {current : V.Current} {event : original.toRootSource.actual.OccurrenceAt current}
    (compiled : SourceNativeLedgerEvolutionAt original event) :
    SourceNativeLedgerEvolutionAt (p.source original) (p.eventEquiv original current event) := by
  cases compiled with
  | nativeWrite write structural target whole =>
      exact .nativeWrite write structural (p.eventEquiv original _ target) (p.wholeLedgerEquiv _ _ whole)
  | relationWrite write structural target whole =>
      exact .relationWrite write structural (p.eventEquiv original _ target) (p.wholeLedgerEquiv _ _ whole)
  | continuedTransport write structural target whole =>
      exact .continuedTransport write structural (p.eventEquiv original _ target) (p.wholeLedgerEquiv _ _ whole)
  | borromeanRedirect write structural target whole =>
      exact .borromeanRedirect write structural (p.eventEquiv original _ target) (p.wholeLedgerEquiv _ _ whole)
  | faithfulTerminal terminal structural whole =>
      exact .faithfulTerminal terminal structural (p.wholeTerminalEquiv _ whole)

def Presentation.restoreCompilation {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {original : SourceNativeSource N V}
    {current : V.Current} {event : original.toRootSource.actual.OccurrenceAt current}
    (compiled : SourceNativeLedgerEvolutionAt (p.source original) (p.eventEquiv original current event)) :
    SourceNativeLedgerEvolutionAt original event := by
  cases compiled with
  | nativeWrite write structural target whole =>
      rcases target with ⟨support, ⟨target, same⟩⟩
      cases same
      exact .nativeWrite write structural target ((p.wholeLedgerEquiv _ _).symm whole)
  | relationWrite write structural target whole =>
      rcases target with ⟨support, ⟨target, same⟩⟩
      cases same
      exact .relationWrite write structural target ((p.wholeLedgerEquiv _ _).symm whole)
  | continuedTransport write structural target whole =>
      rcases target with ⟨support, ⟨target, same⟩⟩
      cases same
      exact .continuedTransport write structural target ((p.wholeLedgerEquiv _ _).symm whole)
  | borromeanRedirect write structural target whole =>
      rcases target with ⟨support, ⟨target, same⟩⟩
      cases same
      exact .borromeanRedirect write structural target ((p.wholeLedgerEquiv _ _).symm whole)
  | faithfulTerminal terminal structural whole =>
      exact .faithfulTerminal terminal structural ((p.wholeTerminalEquiv _).symm whole)

theorem Presentation.restore_map_compilation {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {original : SourceNativeSource N V}
    {current : V.Current} {event : original.toRootSource.actual.OccurrenceAt current}
    (compiled : SourceNativeLedgerEvolutionAt original event) :
    p.restoreCompilation (p.mapCompilation compiled) = compiled := by
  cases compiled with
  | nativeWrite write structural target whole =>
      change SourceNativeLedgerEvolutionAt.nativeWrite write structural target
        ((p.wholeLedgerEquiv event.1 target.1).symm (p.wholeLedgerEquiv event.1 target.1 whole)) = _
      exact congrArg (SourceNativeLedgerEvolutionAt.nativeWrite write structural target)
        ((p.wholeLedgerEquiv event.1 target.1).symm_apply_apply whole)
  | relationWrite write structural target whole =>
      change SourceNativeLedgerEvolutionAt.relationWrite write structural target
        ((p.wholeLedgerEquiv event.1 target.1).symm (p.wholeLedgerEquiv event.1 target.1 whole)) = _
      exact congrArg (SourceNativeLedgerEvolutionAt.relationWrite write structural target)
        ((p.wholeLedgerEquiv event.1 target.1).symm_apply_apply whole)
  | continuedTransport write structural target whole =>
      change SourceNativeLedgerEvolutionAt.continuedTransport write structural target
        ((p.wholeLedgerEquiv event.1 target.1).symm (p.wholeLedgerEquiv event.1 target.1 whole)) = _
      exact congrArg (SourceNativeLedgerEvolutionAt.continuedTransport write structural target)
        ((p.wholeLedgerEquiv event.1 target.1).symm_apply_apply whole)
  | borromeanRedirect write structural target whole =>
      change SourceNativeLedgerEvolutionAt.borromeanRedirect write structural target
        ((p.wholeLedgerEquiv event.1 target.1).symm (p.wholeLedgerEquiv event.1 target.1 whole)) = _
      exact congrArg (SourceNativeLedgerEvolutionAt.borromeanRedirect write structural target)
        ((p.wholeLedgerEquiv event.1 target.1).symm_apply_apply whole)
  | faithfulTerminal terminal structural whole =>
      change SourceNativeLedgerEvolutionAt.faithfulTerminal terminal structural
        ((p.wholeTerminalEquiv event.1).symm (p.wholeTerminalEquiv event.1 whole)) = _
      exact congrArg (SourceNativeLedgerEvolutionAt.faithfulTerminal terminal structural)
        ((p.wholeTerminalEquiv event.1).symm_apply_apply whole)

theorem Presentation.map_restore_compilation {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {original : SourceNativeSource N V}
    {current : V.Current} {event : original.toRootSource.actual.OccurrenceAt current}
    (compiled : SourceNativeLedgerEvolutionAt (p.source original) (p.eventEquiv original current event)) :
    p.mapCompilation (p.restoreCompilation compiled) = compiled := by
  cases compiled with
  | nativeWrite write structural target whole =>
      rcases target with ⟨support, ⟨target, same⟩⟩
      cases same
      change SourceNativeLedgerEvolutionAt.nativeWrite write structural (p.eventEquiv original _ target)
        (p.wholeLedgerEquiv event.1 target.1 ((p.wholeLedgerEquiv event.1 target.1).symm whole)) = _
      exact congrArg (SourceNativeLedgerEvolutionAt.nativeWrite write structural (p.eventEquiv original _ target))
        ((p.wholeLedgerEquiv event.1 target.1).apply_symm_apply whole)
  | relationWrite write structural target whole =>
      rcases target with ⟨support, ⟨target, same⟩⟩
      cases same
      change SourceNativeLedgerEvolutionAt.relationWrite write structural (p.eventEquiv original _ target)
        (p.wholeLedgerEquiv event.1 target.1 ((p.wholeLedgerEquiv event.1 target.1).symm whole)) = _
      exact congrArg (SourceNativeLedgerEvolutionAt.relationWrite write structural (p.eventEquiv original _ target))
        ((p.wholeLedgerEquiv event.1 target.1).apply_symm_apply whole)
  | continuedTransport write structural target whole =>
      rcases target with ⟨support, ⟨target, same⟩⟩
      cases same
      change SourceNativeLedgerEvolutionAt.continuedTransport write structural (p.eventEquiv original _ target)
        (p.wholeLedgerEquiv event.1 target.1 ((p.wholeLedgerEquiv event.1 target.1).symm whole)) = _
      exact congrArg (SourceNativeLedgerEvolutionAt.continuedTransport write structural (p.eventEquiv original _ target))
        ((p.wholeLedgerEquiv event.1 target.1).apply_symm_apply whole)
  | borromeanRedirect write structural target whole =>
      rcases target with ⟨support, ⟨target, same⟩⟩
      cases same
      change SourceNativeLedgerEvolutionAt.borromeanRedirect write structural (p.eventEquiv original _ target)
        (p.wholeLedgerEquiv event.1 target.1 ((p.wholeLedgerEquiv event.1 target.1).symm whole)) = _
      exact congrArg (SourceNativeLedgerEvolutionAt.borromeanRedirect write structural (p.eventEquiv original _ target))
        ((p.wholeLedgerEquiv event.1 target.1).apply_symm_apply whole)
  | faithfulTerminal terminal structural whole =>
      change SourceNativeLedgerEvolutionAt.faithfulTerminal terminal structural
        (p.wholeTerminalEquiv event.1 ((p.wholeTerminalEquiv event.1).symm whole)) = _
      exact congrArg (SourceNativeLedgerEvolutionAt.faithfulTerminal terminal structural)
        ((p.wholeTerminalEquiv event.1).apply_symm_apply whole)

def Presentation.compilationEquiv {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {original : SourceNativeSource N V}
    {current : V.Current} (event : original.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt original event ≃
      SourceNativeLedgerEvolutionAt (p.source original) (p.eventEquiv original current event) where
  toFun := p.mapCompilation
  invFun := p.restoreCompilation
  left_inv := p.restore_map_compilation
  right_inv := p.map_restore_compilation


/-- The existing full compiler is transported at every legal event.  It is not
an input to the mother network factory. -/
def Presentation.compileAt {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {original : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler original)
    {current : V.Current}
    (event : (p.source original).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt (p.source original) event := by
  rcases event with ⟨support, ⟨event, same⟩⟩
  cases same
  exact p.mapCompilation (compiler.compile event)

theorem Presentation.compileAt_exchange {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {original : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler original)
    {current : V.Current} (event : original.toRootSource.actual.OccurrenceAt current) :
    p.compileAt compiler (p.eventEquiv original current event) =
      p.mapCompilation (compiler.compile event) := rfl

theorem Presentation.compileAt_full_recovery {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {original : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler original)
    {current : V.Current} (event : original.toRootSource.actual.OccurrenceAt current) :
    p.restoreCompilation (p.compileAt compiler (p.eventEquiv original current event)) =
      compiler.compile event :=
  p.restore_map_compilation (compiler.compile event)

theorem Presentation.generated_target_commutes_iff {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {original : SourceNativeSource N V}
    {current : V.Current} {event : original.toRootSource.actual.OccurrenceAt current}
    (compiled : SourceNativeLedgerEvolutionAt original event)
    (emitted : (c : V.Current) → original.toRootSource.actual.OccurrenceAt c) :
    (p.mapCompilation compiled).CommutesWith (fun c => p.eventEquiv original c (emitted c)) ↔
      compiled.CommutesWith emitted := by
  cases compiled with
  | nativeWrite write structural target whole =>
      change (p.eventEquiv original _ target = p.eventEquiv original _ (emitted (V.nativeTarget write))) ↔
        target = emitted (V.nativeTarget write)
      exact (p.eventEquiv original _).injective.eq_iff
  | relationWrite write structural target whole =>
      change (p.eventEquiv original _ target = p.eventEquiv original _ (emitted (V.relationTarget write))) ↔
        target = emitted (V.relationTarget write)
      exact (p.eventEquiv original _).injective.eq_iff
  | continuedTransport write structural target whole =>
      change (p.eventEquiv original _ target = p.eventEquiv original _ (emitted (V.continuedTarget write))) ↔
        target = emitted (V.continuedTarget write)
      exact (p.eventEquiv original _).injective.eq_iff
  | borromeanRedirect write structural target whole =>
      change (p.eventEquiv original _ target = p.eventEquiv original _ (emitted (V.redirectTarget write))) ↔
        target = emitted (V.redirectTarget write)
      exact (p.eventEquiv original _).injective.eq_iff
  | faithfulTerminal => exact Iff.rfl

theorem formed_network_consumes_original_compiler (N : WorldRelationNetwork.{0})
    (encode : Total N ↪ MotherNetworkFactory.B) :
    ∃ m : MotherNetworkFactory.M, ∃ G : WorldRelationNetwork.{0}, ∃ p : Presentation N G,
      MotherNetworkFactory.formNetwork m = some G ∧
      ∀ {V : ConstructiveRoot.Vocabulary.{0}} {original : SourceNativeSource N V}
        (compiler : SourceNativeLedgerCompiler original) {current : V.Current}
        (event : original.toRootSource.actual.OccurrenceAt current),
        p.restoreCompilation (p.compileAt compiler (p.eventEquiv original current event)) =
          compiler.compile event := by
  obtain ⟨m, G, formed, ⟨p⟩⟩ := every_jointly_embedded_network N encode
  refine ⟨m, G, p, formed, ?_⟩
  intro V original compiler current event
  exact p.compileAt_full_recovery compiler event

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
