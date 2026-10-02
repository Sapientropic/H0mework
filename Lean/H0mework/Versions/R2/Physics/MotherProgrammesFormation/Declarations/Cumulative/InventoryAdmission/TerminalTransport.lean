import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.TransportLaws

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
namespace AdmissionTransport

theorem successor_nonempty_iff {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} {current : V.Current}
    (event : source.toRootSource.actual.OccurrenceAt current)
    (compiled : SourceNativeLedgerEvolutionAt source event) :
    Nonempty (SourceNativeLedgerGeneratedSuccessorAt event compiled) ↔
      (source.toRootSource.actual.compile event).nextCurrent? ≠ none := by
  cases compiled with
  | nativeWrite _ structural _ _ =>
      rw [structural]
      exact ⟨(fun _ impossible => nomatch impossible), fun _ => ⟨PUnit.unit⟩⟩
  | relationWrite _ structural _ _ =>
      rw [structural]
      exact ⟨(fun _ impossible => nomatch impossible), fun _ => ⟨PUnit.unit⟩⟩
  | continuedTransport _ structural _ _ =>
      rw [structural]
      exact ⟨(fun _ impossible => nomatch impossible), fun _ => ⟨PUnit.unit⟩⟩
  | borromeanRedirect _ structural _ _ =>
      rw [structural]
      exact ⟨(fun _ impossible => nomatch impossible), fun _ => ⟨PUnit.unit⟩⟩
  | faithfulTerminal _ structural _ =>
      rw [structural]
      exact ⟨(fun ⟨impossible⟩ => nomatch impossible), fun impossible => False.elim (impossible rfl)⟩

theorem noOutgoing_transport {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {old : SourceNativeLedgerSource N V} {fresh : SourceNativeLedgerSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v old.source fresh.source)
    (current : V.Current) (empty : IsEmpty (SourceNativeActualOutgoingEventAt old current)) :
    IsEmpty (SourceNativeActualOutgoingEventAt fresh (v.current current)) := by
  refine ⟨fun ⟨event, successor⟩ => ?_⟩
  obtain ⟨event, rfl⟩ := (p.event current).surjective event
  have freshNext := (successor_nonempty_iff _ (fresh.ledgerCompiler.compile (p.event current event))).mp ⟨successor⟩
  have oldNext : (old.source.toRootSource.actual.compile event).nextCurrent? ≠ none := by
    intro absent
    apply freshNext
    rw [p.compile_eq, ← v.evolution_next, absent]
    rfl
  obtain ⟨oldSuccessor⟩ := (successor_nonempty_iff event (old.ledgerCompiler.compile event)).mpr oldNext
  exact empty.false ⟨event, oldSuccessor⟩

private theorem terminal_of_kind {V : ConstructiveRoot.Vocabulary.{0}} {current : V.Current}
    (evolution : EvolutionAt V current) (same : evolution.kind = .faithfulTerminal) :
    ∃ terminal : V.FaithfulTerminalAt current, evolution = .faithfulTerminal terminal := by
  cases evolution with
  | faithfulTerminal terminal => exact ⟨terminal, rfl⟩
  | nativeWrite => cases same
  | relationWrite => cases same
  | continuedTransport => cases same
  | borromeanRedirect => cases same

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
  {old : SourceNativeRestructuringLedgerSource N V}
  (admission : SourceNativeCompleteEventInventoryAdmission old)
  (value : SourcePair)
  (n : MotherNetworkOrigin.Presentation N value.1.1.1.1.1)
  (v : MotherVocabularyOrigin.Presentation V (RepresentedV value))
  (w : MotherVocabularyOrigin.Presentation admission.ActualV value.2.1)
  (p : MotherNativeSourceOrigin.Presentation n v old.source (Represented value).source)
  (a : MotherNativeSourceOrigin.Presentation n w admission.actualSource.source value.2.2.source)

theorem transportedData_terminal {current : (RepresentedV value).Current}
    (event : value.2.2.source.toRootSource.actual.OccurrenceAt
      ((transportedData admission value n v w p a).current.backward current))
    (terminal : (RepresentedV value).FaithfulTerminalAt current)
    (terminal_eq : ((transportedData admission value n v w p a).evolution current).forward
      (value.2.2.source.toRootSource.actual.compile event) = .faithfulTerminal terminal) :
    IsEmpty (SourceNativeActualOutgoingEventAt value.2.2
      ((transportedData admission value n v w p a).current.backward current)) := by
  obtain ⟨event, rfl⟩ := (a.event (admission.currentPresentation.backward (v.current.symm current))).surjective event
  change evolutionAt v current ((admission.evolutionPresentation _).forward
    ((w.evolution _).symm (value.2.2.source.toRootSource.actual.compile (a.event _ event)))) = _ at terminal_eq
  rw [a.compile_eq, Equiv.symm_apply_apply] at terminal_eq
  have kind : ((admission.evolutionPresentation _).forward
      (admission.actualSource.source.toRootSource.actual.compile event)).kind = .faithfulTerminal :=
    (evolutionAt_kind v current _).symm.trans (congrArg EvolutionAt.kind terminal_eq)
  obtain ⟨originalTerminal, originalEq⟩ := terminal_of_kind _ kind
  exact noOutgoing_transport a _ (admission.terminal_exhausts_actual_inventory event originalTerminal originalEq)

end AdmissionTransport
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
