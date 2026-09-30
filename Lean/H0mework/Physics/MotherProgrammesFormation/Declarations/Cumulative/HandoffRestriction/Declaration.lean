import H0mework.Foundation.Runtime.AnswerNext
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.Recovery

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffRestriction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}

/-- The complete causal input, including every finite and post-cofinal
history and the exact lower compiler's terminal occurrence. -/
structure Index (source : SourceNativeAuthoritySource N V) : Type where
  current : V.Current
  history : SourceNativeAuthorityTemporalHistoryAt source current
  occurrence : source.restructuringSource.source.toRootSource.actual.OccurrenceAt current
  terminal : SourceFaithfulTerminalOccurrenceAt source occurrence

abbrev EventFamily (source : SourceNativeAuthoritySource N V) := Index source → Type
abbrev EventPoint {source : SourceNativeAuthoritySource N V} (events : EventFamily source) :=
  Σ index, events index
abbrev NextRoot (N : WorldRelationNetwork.{0}) :=
  Σ nextVocabulary : ConstructiveRoot.Vocabulary.{0}, SourceNativeAuthoritativeRootClosure N nextVocabulary

/-- One whole successor packet, indexed by an arbitrary legal event rather
than only the selected emitter trajectory. -/
structure Continuation {source : SourceNativeAuthoritySource N V} (events : EventFamily source)
    (point : EventPoint events) : Type 2 where
  next : NextRoot N
  occurrencePresentation : ConstructivePresentation
    (next.2.toRoot.actual.OccurrenceAt next.2.toRoot.source.initial) (events point.1)
  occurrence_commutes : occurrencePresentation.forward (next.2.emitted next.2.toRoot.source.initial) = point.2
  lawSurface_eq : next.2.source.lawSurface = source.lawSurface
  targetDebtOrigin : (targetEntry : OpenResponsibilityAt N (next.2.toRoot.supportAt next.2.toRoot.source.initial)) →
    (Σ sourceEntry : OpenResponsibilityAt N
      (source.restructuringSource.source.toRootSource.account.supportOf point.1.occurrence),
      RootDebtLineageAt N sourceEntry targetEntry) ⊕
    RootDebtFreshAt N (source.restructuringSource.source.toRootSource.account.supportOf point.1.occurrence) targetEntry
  sameDebtBudget_not_refilled :
    (sourceEntry : OpenResponsibilityAt N
      (source.restructuringSource.source.toRootSource.account.supportOf point.1.occurrence)) →
    (targetEntry : OpenResponsibilityAt N (next.2.toRoot.supportAt next.2.toRoot.source.initial)) →
    RootDebtLineageAt N sourceEntry targetEntry → targetEntry.progressBudget ≤ sourceEntry.progressBudget
  sameDebtTarget_unique :
    (sourceEntry : OpenResponsibilityAt N
      (source.restructuringSource.source.toRootSource.account.supportOf point.1.occurrence)) →
    (first last : OpenResponsibilityAt N (next.2.toRoot.supportAt next.2.toRoot.source.initial)) →
    RootDebtLineageAt N sourceEntry first → RootDebtLineageAt N sourceEntry last → first = last

structure Declaration (source : SourceNativeAuthoritySource N V) (events : EventFamily source) : Type 2 where
  emit : ∀ index, events index
  continuation : ∀ point : EventPoint events, Continuation events point

/-- Source construction uses the original seal. This is assembly, not a
material producer or a new terminal execution interface. -/
def assembleLaw {source : SourceNativeAuthoritySource N V} {events : EventFamily source}
    (declaration : Declaration source events) : SourceNativeTerminalHandoffLaw source :=
  SourceNativeTerminalHandoffLaw.create
    (fun {current} history {occurrence} terminal => events ⟨current, history, occurrence, terminal⟩)
    (fun {current} history {occurrence} terminal => declaration.emit ⟨current, history, occurrence, terminal⟩)
    (fun {current} {history} {occurrence} {terminal} event =>
      (declaration.continuation ⟨⟨current, history, occurrence, terminal⟩, event⟩).next.1)
    (fun {current} {history} {occurrence} {terminal} event =>
      (declaration.continuation ⟨⟨current, history, occurrence, terminal⟩, event⟩).next.2)
    (fun {current} {history} {occurrence} {terminal} event =>
      (declaration.continuation ⟨⟨current, history, occurrence, terminal⟩, event⟩).occurrencePresentation)
    (fun {current} {history} {occurrence} {terminal} event =>
      (declaration.continuation ⟨⟨current, history, occurrence, terminal⟩, event⟩).occurrence_commutes)
    (fun {current} {history} {occurrence} {terminal} event =>
      (declaration.continuation ⟨⟨current, history, occurrence, terminal⟩, event⟩).lawSurface_eq)
    (fun {current} {history} {occurrence} {terminal} event =>
      (declaration.continuation ⟨⟨current, history, occurrence, terminal⟩, event⟩).targetDebtOrigin)
    (fun {current} {history} {occurrence} {terminal} event =>
      (declaration.continuation ⟨⟨current, history, occurrence, terminal⟩, event⟩).sameDebtBudget_not_refilled)
    (fun {current} {history} {occurrence} {terminal} event =>
      (declaration.continuation ⟨⟨current, history, occurrence, terminal⟩, event⟩).sameDebtTarget_unique)

private def declarationOf {source : SourceNativeAuthoritySource N V}
    (law : SourceNativeTerminalHandoffLaw source) : Σ events : EventFamily source, Declaration source events := by
  cases law
  rename_i events emit nextVocabulary nextRoot occurrencePresentation occurrenceCommutes lawSurface debtOrigin debtBudget debtUnique
  refine ⟨(fun index => events index.history index.terminal), ?_⟩
  exact {
    emit := fun index => emit index.history index.terminal
    continuation := fun point => {
      next := ⟨nextVocabulary point.2, nextRoot point.2⟩
      occurrencePresentation := occurrencePresentation point.2
      occurrence_commutes := occurrenceCommutes point.2
      lawSurface_eq := lawSurface point.2
      targetDebtOrigin := debtOrigin point.2
      sameDebtBudget_not_refilled := debtBudget point.2
      sameDebtTarget_unique := debtUnique point.2 } }

private theorem assemble_declarationOf {source : SourceNativeAuthoritySource N V}
    (law : SourceNativeTerminalHandoffLaw source) : assembleLaw (declarationOf law).2 = law := by
  cases law
  rfl

private theorem declarationOf_assemble {source : SourceNativeAuthoritySource N V}
    {events : EventFamily source} (declaration : Declaration source events) :
    declarationOf (assembleLaw declaration) = ⟨events, declaration⟩ := by
  cases declaration
  rfl

/-- Read the full event schema without exposing a raw continuation or a
next-root execution mouth. -/
def eventsOf {source : SourceNativeAuthoritySource N V}
    (law : SourceNativeTerminalHandoffLaw source) : EventFamily source :=
  (declarationOf law).1

theorem eventsOf_assemble {source : SourceNativeAuthoritySource N V}
    {events : EventFamily source} (declaration : Declaration source events) :
    eventsOf (assembleLaw declaration) = events :=
  congrArg Sigma.fst (declarationOf_assemble declaration)

/-- The actual sealed value is opened only inside this transporter, and its
complete readback is immediately returned under the original seal. -/
def restrictSealed {source : SourceNativeAuthoritySource N V}
    {original generated : EventFamily source} (actual : SourceNativeTerminalHandoffLaw source)
    (schema : eventsOf actual = generated)
    (readback : Declaration source generated → Declaration source original) :
    SourceNativeTerminalHandoffLaw source :=
  assembleLaw (readback (Equiv.cast (congrArg (Declaration source) schema) (declarationOf actual).2))

private theorem declaration_value_eq {source : SourceNativeAuthoritySource N V}
    (read : Σ events : EventFamily source, Declaration source events)
    (events : EventFamily source) (value : Declaration source events) (same : read = ⟨events, value⟩) :
    Equiv.cast (congrArg (Declaration source) (congrArg Sigma.fst same)) read.2 = value := by
  cases same
  rfl

theorem restrictSealed_assemble {source : SourceNativeAuthoritySource N V}
    {original generated : EventFamily source} (actual : Declaration source generated)
    (readback : Declaration source generated → Declaration source original) :
    restrictSealed (assembleLaw actual) (eventsOf_assemble actual) readback = assembleLaw (readback actual) :=
  congrArg (fun value => assembleLaw (readback value))
    (declaration_value_eq (declarationOf (assembleLaw actual)) generated actual (declarationOf_assemble actual))

/-- Complete source-construction data are available for every original sealed
law at the coverage boundary. The private extractor adds no raw next-root
projection to the installed-law API. -/
theorem exists_declaration {source : SourceNativeAuthoritySource N V}
    (law : SourceNativeTerminalHandoffLaw source) :
    ∃ events : EventFamily source, ∃ declaration : Declaration source events, assembleLaw declaration = law :=
  ⟨(declarationOf law).1, (declarationOf law).2, assemble_declarationOf law⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffRestriction
