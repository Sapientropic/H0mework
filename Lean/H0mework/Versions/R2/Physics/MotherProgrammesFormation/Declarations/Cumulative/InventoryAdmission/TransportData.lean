import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.Factory

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

def presentationEquiv {A C : Type} (value : ConstructivePresentation A C) : A ≃ C where
  toFun := value.forward
  invFun := value.backward
  left_inv := value.backward_forward
  right_inv := value.forward_backward

namespace AdmissionTransport

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
  {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
  {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}

def eventAt (p : MotherNativeSourceOrigin.Presentation n v original generated) (current : W.Current) :
    original.toRootSource.actual.OccurrenceAt (v.current.symm current) ≃
      generated.toRootSource.actual.OccurrenceAt current :=
  (p.event (v.current.symm current)).trans
    (Equiv.cast (congrArg generated.toRootSource.actual.OccurrenceAt (v.current.apply_symm_apply current)))

def evolutionAt (v : MotherVocabularyOrigin.Presentation V W) (current : W.Current) :
    EvolutionAt V (v.current.symm current) ≃ EvolutionAt W current :=
  (v.evolution (v.current.symm current)).trans
    (Equiv.cast (congrArg (EvolutionAt W) (v.current.apply_symm_apply current)))

private theorem cast_event_compile {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (source : SourceNativeSource N V) {left right : V.Current} (same : left = right)
    (event : source.toRootSource.actual.OccurrenceAt left) :
    source.toRootSource.actual.compile (Equiv.cast (congrArg source.toRootSource.actual.OccurrenceAt same) event) =
      Equiv.cast (congrArg (EvolutionAt V) same) (source.toRootSource.actual.compile event) := by
  cases same
  rfl

private theorem cast_event_support {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (source : SourceNativeSource N V) {left right : V.Current} (same : left = right)
    (event : source.toRootSource.actual.OccurrenceAt left) :
    (Equiv.cast (congrArg source.toRootSource.actual.OccurrenceAt same) event).1 = event.1 := by
  cases same
  rfl

private theorem cast_evolution_kind {V : ConstructiveRoot.Vocabulary.{0}}
    {left right : V.Current} (same : left = right) (evolution : EvolutionAt V left) :
    (Equiv.cast (congrArg (EvolutionAt V) same) evolution).kind = evolution.kind := by
  cases same
  rfl

private theorem cast_evolution_next {V : ConstructiveRoot.Vocabulary.{0}}
    {left right : V.Current} (same : left = right) (evolution : EvolutionAt V left) :
    (Equiv.cast (congrArg (EvolutionAt V) same) evolution).nextCurrent? = evolution.nextCurrent? := by
  cases same
  rfl

theorem eventAt_compile (p : MotherNativeSourceOrigin.Presentation n v original generated)
    (current : W.Current) (event : original.toRootSource.actual.OccurrenceAt (v.current.symm current)) :
    generated.toRootSource.actual.compile (eventAt p current event) =
      evolutionAt v current (original.toRootSource.actual.compile event) := by
  exact (cast_event_compile generated (v.current.apply_symm_apply current) (p.event _ event)).trans
    (congrArg (Equiv.cast (congrArg (EvolutionAt W) (v.current.apply_symm_apply current)))
      (p.compile_eq _ event))

theorem eventAt_support (p : MotherNativeSourceOrigin.Presentation n v original generated)
    (current : W.Current) (event : original.toRootSource.actual.OccurrenceAt (v.current.symm current)) :
    (eventAt p current event).1 = n.support event.1 := by
  exact (cast_event_support generated (v.current.apply_symm_apply current) (p.event _ event)).trans (p.support_eq _ event)

theorem evolutionAt_kind (v : MotherVocabularyOrigin.Presentation V W)
    (current : W.Current) (evolution : EvolutionAt V (v.current.symm current)) :
    (evolutionAt v current evolution).kind = evolution.kind := by
  exact (cast_evolution_kind (v.current.apply_symm_apply current) (v.evolution _ evolution)).trans (v.evolution_kind evolution)

theorem evolutionAt_next (v : MotherVocabularyOrigin.Presentation V W)
    (current : W.Current) (evolution : EvolutionAt V (v.current.symm current)) :
    Option.map v.current evolution.nextCurrent? = (evolutionAt v current evolution).nextCurrent? := by
  exact (v.evolution_next evolution).trans (cast_evolution_next (v.current.apply_symm_apply current) (v.evolution _ evolution)).symm

variable {V : ConstructiveRoot.Vocabulary.{0}}
  {old : SourceNativeRestructuringLedgerSource N V}
  (admission : SourceNativeCompleteEventInventoryAdmission old)
  (value : SourcePair)
  (n : MotherNetworkOrigin.Presentation N value.1.1.1.1.1)
  (v : MotherVocabularyOrigin.Presentation V (RepresentedV value))
  (w : MotherVocabularyOrigin.Presentation admission.ActualV value.2.1)
  (p : MotherNativeSourceOrigin.Presentation n v old.source (Represented value).source)
  (a : MotherNativeSourceOrigin.Presentation n w admission.actualSource.source value.2.2.source)

def currentMap : value.2.1.Current ≃ (RepresentedV value).Current :=
  w.current.symm.trans ((presentationEquiv admission.currentPresentation).trans v.current)

def transportedData : PresentationData value where
  current := presentationFromEquiv (currentMap admission value v w)
  occurrence := fun current => presentationFromEquiv
    ((a.event (admission.currentPresentation.backward (v.current.symm current))).symm.trans
      ((presentationEquiv (admission.occurrencePresentation (v.current.symm current))).trans
        (eventAt p current)))
  evolution := fun current => presentationFromEquiv
    ((w.evolution (admission.currentPresentation.backward (v.current.symm current))).symm.trans
      ((presentationEquiv (admission.evolutionPresentation (v.current.symm current))).trans
        (evolutionAt v current)))
  cofinal := presentationFromEquiv
    (w.cofinal.symm.trans ((presentationEquiv admission.cofinalEventPresentation).trans v.cofinal))

theorem transportedData_initial :
    (transportedData admission value n v w p a).current.forward value.2.2.source.initial =
      (Represented value).source.initial := by
  change v.current (admission.currentPresentation.forward (w.current.symm value.2.2.source.initial)) = _
  rw [a.initial_eq, Equiv.symm_apply_apply, admission.initial_eq, p.initial_eq]

theorem transportedData_structural (current : (RepresentedV value).Current)
    (event : value.2.2.source.toRootSource.actual.OccurrenceAt
      ((transportedData admission value n v w p a).current.backward current)) :
    ((transportedData admission value n v w p a).evolution current).forward
        (value.2.2.source.toRootSource.actual.compile event) =
      (Represented value).source.toRootSource.actual.compile
        (((transportedData admission value n v w p a).occurrence current).forward event) := by
  obtain ⟨event, rfl⟩ := (a.event (admission.currentPresentation.backward (v.current.symm current))).surjective event
  change evolutionAt v current
    ((admission.evolutionPresentation _).forward
      ((w.evolution _).symm (value.2.2.source.toRootSource.actual.compile (a.event _ event)))) =
    (Represented value).source.toRootSource.actual.compile
      (eventAt p current ((admission.occurrencePresentation _).forward ((a.event _).symm (a.event _ event))))
  rw [a.compile_eq, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    admission.structural_commutes, eventAt_compile]

theorem transportedData_kind (current : (RepresentedV value).Current)
    (evolution : EvolutionAt value.2.1
      ((transportedData admission value n v w p a).current.backward current)) :
    (((transportedData admission value n v w p a).evolution current).forward evolution).kind = evolution.kind := by
  obtain ⟨evolution, rfl⟩ := (w.evolution (admission.currentPresentation.backward (v.current.symm current))).surjective evolution
  change (evolutionAt v current ((admission.evolutionPresentation _).forward ((w.evolution _).symm (w.evolution _ evolution)))).kind = _
  rw [Equiv.symm_apply_apply, evolutionAt_kind, admission.kind_commutes]
  exact (w.evolution_kind evolution).symm

theorem transportedData_support (current : (RepresentedV value).Current)
    (event : value.2.2.source.toRootSource.actual.OccurrenceAt
      ((transportedData admission value n v w p a).current.backward current)) :
    (Represented value).source.toRootSource.account.supportOf
        (((transportedData admission value n v w p a).occurrence current).forward event) =
      value.2.2.source.toRootSource.account.supportOf event := by
  obtain ⟨event, rfl⟩ := (a.event (admission.currentPresentation.backward (v.current.symm current))).surjective event
  change (eventAt p current ((admission.occurrencePresentation _).forward ((a.event _).symm (a.event _ event)))).1 = (a.event _ event).1
  rw [Equiv.symm_apply_apply, eventAt_support, a.support_eq]
  exact congrArg n.support (admission.support_commutes _ event)

end AdmissionTransport
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
