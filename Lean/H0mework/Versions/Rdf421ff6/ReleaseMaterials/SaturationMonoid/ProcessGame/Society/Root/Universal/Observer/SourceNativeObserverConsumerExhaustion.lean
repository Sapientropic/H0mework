import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.SourceNativeUniversalRootGrammar
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.ReadoutFactorization
import H0mework.Foundation.Responsibility.Observer

/-!
# Source-native observer / consumer exhaustion

Observer output is unrestricted.  World authority is not: it is generated
only by the source-declared actual scenario together with the exact living
root evolution.  Grammar success/failure is an independent axis, so all four
actual/nonactual × canonical/failed combinations remain representable.

This module installs no observer law, projection, registry, ledger, root or
future.  It consumes the already installed universal grammar and the existing
observer/readout interfaces.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace UniversalRootGrammar

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer

universe u v w x y

/-! ## Universe-polymorphic full-root consumer safety -/

/-- The exact unquotiented root coface is safe for a consumer in any output
universe.  The existing root theorem is recovered when `w = u`. -/
theorem rootCofaceRead_consumerSafe_universe
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {Disposition : Type w}
    (consumer : ExactTemporalCausalRootEvent root → Disposition) :
    ConsumerSafe (@rootCofaceRead _ _ root) consumer := by
  intro left right sameRoot
  exact congrArg consumer sameRoot

/-- Hiddenness cannot occur at the complete root coface, independently of
the consumer's universe. -/
theorem no_hiddenNull_at_rootCofaceRead_universe
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {Disposition : Type w}
    (consumer : ExactTemporalCausalRootEvent root → Disposition) :
    IsEmpty (HiddenNullWitness (@rootCofaceRead _ _ root) consumer) :=
  ⟨fun hidden =>
    hidden.not_consumerSafe
      (rootCofaceRead_consumerSafe_universe consumer)⟩

/-- An arbitrary parameterized qualitative, quantitative or narrative
readout, followed by an arbitrary downstream consumer, remains safe when it
reads the complete root event. -/
theorem rootCofaceParameterizedReadout_consumerSafe
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {Parameter : Type v} {Output : Type w} {Disposition : Type x}
    (readout : ExactTemporalCausalRootEvent root → Parameter → Output)
    (consumer : Output → Disposition) (parameter : Parameter) :
    ConsumerSafe (@rootCofaceRead _ _ root)
      (fun event => consumer (readout event parameter)) := by
  intro left right sameRoot
  exact congrArg (fun event => consumer (readout event parameter)) sameRoot

/-! ## Independent source-authority axis -/

/-- Total source-derived status of one scenario.  This classifier consults
only the vocabulary's installed decidable scenario equality.  It does not
inspect an observer, readout, consumer or grammar result. -/
inductive SourceNativeScenarioAuthorityStatusAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    (vocabulary : SourceNativeDependentFaceVocabulary source) :
    vocabulary.Scenario → Type u
  | actual {scenario : vocabulary.Scenario}
      (authority : SourceNativeScenarioActualWriteAuthorityAt vocabulary
        scenario) :
      SourceNativeScenarioAuthorityStatusAt vocabulary scenario
  | nonActual {scenario : vocabulary.Scenario}
      (outside : scenario ≠ vocabulary.actualScenario) :
      SourceNativeScenarioAuthorityStatusAt vocabulary scenario

/-- Source-only generation of the actual/nonactual axis. -/
def sourceNativeScenarioAuthorityStatusAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    (vocabulary : SourceNativeDependentFaceVocabulary source)
    (scenario : vocabulary.Scenario) :
    SourceNativeScenarioAuthorityStatusAt vocabulary scenario := by
  letI : DecidableEq vocabulary.Scenario :=
    vocabulary.scenarioDecidableEq
  by_cases exactScenario : scenario = vocabulary.actualScenario
  · subst scenario
    exact .actual .actual
  · exact .nonActual exactScenario

namespace SourceNativeScenarioAuthorityStatusAt

variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
  {source : SourceNativeLedgerSource N V}
  {vocabulary : SourceNativeDependentFaceVocabulary source}
  {scenario : vocabulary.Scenario}

/-- The generated status cannot report nonactual while carrying an actual
write token. -/
theorem actual_nonActual_disjoint
    (status : SourceNativeScenarioAuthorityStatusAt vocabulary scenario) :
    (Nonempty (SourceNativeScenarioActualWriteAuthorityAt vocabulary
      scenario) → scenario = vocabulary.actualScenario) := by
  intro authority
  rcases authority with ⟨authority⟩
  cases authority
  rfl

end SourceNativeScenarioAuthorityStatusAt

/-- Genuine world-authority mouth.  The carrier contains only the existing
source actual-scenario token and the existing living-root evolution.  It does
not store a factorization theorem, consumer-safety receipt, ledger or next. -/
structure SourceNativeObserverConsumerAuthorityAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario) : Type (u + 3) where
  private mk ::
  scenarioAuthority : SourceNativeScenarioActualWriteAuthorityAt
    recognition.law.vocabulary scenario
  rootEvolution : SourceNativeLivingRootCausalEvolutionAt root
    (ULift.up visit)

/-- The exact installed actual scenario generates world authority. -/
def sourceNativeObserverConsumerAuthorityAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeObserverConsumerAuthorityAt recognition visit
      recognition.law.vocabulary.actualScenario :=
  ⟨.actual, root.canonicalCausalAnswerAndNext (ULift.up visit)⟩

namespace SourceNativeObserverConsumerAuthorityAt

variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
  {root : SourceNativeLivingRootClosure N V}
  {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
  {visit : SourceNativeTemporalVisitAt
    root.toAuthoritativeRoot.toLedgerRoot}
  {scenario : recognition.law.vocabulary.Scenario}

/-- Build the sealed source authority from an existing indexed actual-write
token.  Pattern matching the token forces its scenario to the source actual
scenario; no caller equality or factorization is accepted. -/
def ofScenarioAuthority
    (scenarioAuthority : SourceNativeScenarioActualWriteAuthorityAt
      recognition.law.vocabulary scenario) :
    SourceNativeObserverConsumerAuthorityAt recognition visit scenario := by
  cases scenarioAuthority
  exact sourceNativeObserverConsumerAuthorityAt recognition visit

/-- The authority carrier is inhabited exactly at the actual scenario stored
inside the installed trace payload.  The left side is the independent source
token/evolution carrier, not a renamed factorization predicate. -/
theorem nonempty_iff_installedActualScenario :
    Nonempty (SourceNativeObserverConsumerAuthorityAt recognition visit
      scenario) ↔
      scenario = recognition.installedActualScenarioAt visit := by
  constructor
  · rintro ⟨authority⟩
    cases authority.scenarioAuthority
    exact (recognition.installedActualScenario_eq visit).symm
  · intro scenarioExact
    rw [recognition.installedActualScenario_eq visit] at scenarioExact
    subst scenario
    exact ⟨sourceNativeObserverConsumerAuthorityAt recognition visit⟩

/-- Installed trace, exact occurrence, whole ledger and generated next are
derived from the authority's existing living-root evolution. -/
theorem rootLedgerAndNext_factorize
    (authority : SourceNativeObserverConsumerAuthorityAt recognition visit
      scenario) :
    authority.rootEvolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (authority.rootEvolution.generated.projectionOutcome
          recognition.rootProjection)
        (recognition.installedFiberAt visit) ∧
      HEq (recognition.wholeLedgerWriteBackAt visit)
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          visit.current) ∧
      authority.rootEvolution.nextCurrent = recognition.generatedNextAt
        visit := by
  have factorization :=
    authority.rootEvolution.installedSubsystemAuthority_factorizes
      recognition.installation PUnit.unit
  exact
    ⟨factorization.1,
      factorization.2.1.trans
        (heq_of_eq (recognition.componentOutcome_eq_installedFiber visit)),
      HEq.rfl,
      factorization.2.2⟩

/-- Exact root-coface consequence of the lower source-authority carrier.  The
left side is the independent source token and living evolution carrier.  Only
the theorem's right side unfolds it into
installed-actual custody, arbitrary-universe root consumer safety, the exact
installed projection, whole-ledger write-back and generated next. -/
theorem nonempty_iff_exactRootFactorizationAndConsumerSafe
    {Disposition : Type w}
    (consumer : ExactTemporalCausalRootEvent
      root.toAuthoritativeRoot.toLedgerRoot → Disposition) :
    Nonempty (SourceNativeObserverConsumerAuthorityAt recognition visit
      scenario) ↔
      scenario = recognition.installedActualScenarioAt visit ∧
        ConsumerSafe
          (@rootCofaceRead _ _ root.toAuthoritativeRoot.toLedgerRoot)
          consumer ∧
        (let evolution :=
          root.canonicalCausalAnswerAndNext (ULift.up visit)
        evolution.generated =
            root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
              visit ∧
          HEq (evolution.generated.projectionOutcome
              recognition.rootProjection)
            (recognition.installedFiberAt visit) ∧
          HEq (recognition.wholeLedgerWriteBackAt visit)
            (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
              visit.current) ∧
          evolution.nextCurrent = recognition.generatedNextAt visit) := by
  constructor
  · intro authority
    exact
      ⟨(nonempty_iff_installedActualScenario
          (recognition := recognition) (visit := visit)
          (scenario := scenario)).1 authority,
        rootCofaceRead_consumerSafe_universe consumer,
        recognition.installedTraceAuthority_factorizes visit⟩
  · rintro ⟨scenarioExact, _consumerSafe, _factorization⟩
    exact
      (nonempty_iff_installedActualScenario
        (recognition := recognition) (visit := visit)
        (scenario := scenario)).2 scenarioExact

end SourceNativeObserverConsumerAuthorityAt

/-! ## Two-axis total grammar consumption -/

/-- One total source-generated consumption record.  Its authority status and
grammar disposition are stored as independent outputs; a failed actual world
remains actual, while a canonical nonactual search remains nonauthoritative. -/
structure SourceNativeObserverConsumerExhaustionAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario)
    {Disposition : Type w}
    (consumer : ExactTemporalCausalRootEvent
      root.toAuthoritativeRoot.toLedgerRoot → Disposition) : Type (max (u + 3) w) where
  authorityStatus : SourceNativeScenarioAuthorityStatusAt
    recognition.law.vocabulary scenario
  grammar : SourceGeneratedUniversalRootGrammarAt recognition visit scenario
  rootConsumerSafe : ConsumerSafe
    (@rootCofaceRead _ _ root.toAuthoritativeRoot.toLedgerRoot) consumer

/-- Total producer.  Neither the consumer nor its codomain participates in
the source branch selection. -/
def sourceNativeObserverConsumerExhaustionAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario)
    {Disposition : Type w}
    (consumer : ExactTemporalCausalRootEvent
      root.toAuthoritativeRoot.toLedgerRoot → Disposition) :
    SourceNativeObserverConsumerExhaustionAt recognition visit scenario
      consumer where
  authorityStatus :=
    sourceNativeScenarioAuthorityStatusAt recognition.law.vocabulary scenario
  grammar := sourceGeneratedUniversalRootGrammarAt recognition visit scenario
  rootConsumerSafe := rootCofaceRead_consumerSafe_universe consumer

namespace SourceNativeObserverConsumerExhaustionAt

variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
  {root : SourceNativeLivingRootClosure N V}
  {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
  {visit : SourceNativeTemporalVisitAt
    root.toAuthoritativeRoot.toLedgerRoot}
  {scenario : recognition.law.vocabulary.Scenario}
  {Disposition : Type w}
  {consumer : ExactTemporalCausalRootEvent
    root.toAuthoritativeRoot.toLedgerRoot → Disposition}
  (exhaustion : SourceNativeObserverConsumerExhaustionAt recognition visit
    scenario consumer)

/-- Grammar success/failure remains exactly the existing installed fold. -/
theorem grammar_disposition_eq_installedFold :
    exhaustion.grammar.disposition =
      compileUniversalSocietyRootGrammarAt recognition visit scenario :=
  rfl

/-- Root factorization is available for the generated grammar independently
of whether its disposition is canonical or failed. -/
theorem grammar_rootLedgerAndNext_factorize :
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (evolution.generated.projectionOutcome
          recognition.rootProjection)
        (recognition.installedFiberAt visit) ∧
      HEq exhaustion.grammar.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          visit.current) ∧
      evolution.nextCurrent = exhaustion.grammar.generatedNext :=
  exhaustion.grammar.rootLedgerAndNext_factorize

end SourceNativeObserverConsumerExhaustionAt

/-! ## Arbitrary visible presentation and typed authority rejection -/

/-- Any observer-factored readout is consumer-safe as an ordinary visible
presentation. -/
theorem factoredReadout_consumerSafe
    {Occurrence : Type u} {Visible : Type v} {Residual : Type w}
    {Output : Type x}
    {observer : AuthorityObserver Occurrence Visible Residual}
    {readout : OccurrenceReadout Occurrence Output}
    (factorization : ReadoutFactorization observer readout) :
    ConsumerSafe observer.forget readout.read :=
  ConsumerSafe.of_factorization factorization.visibleReadout
    (fun occurrence => (factorization.factorizes occurrence).symm)

/-- Postcomposition by an arbitrary downstream consumer preserves lawful
visible presentation. -/
theorem factoredReadout_downstreamConsumerSafe
    {Occurrence : Type u} {Visible : Type v} {Residual : Type w}
    {Output : Type x} {Disposition : Type y}
    {observer : AuthorityObserver Occurrence Visible Residual}
    {readout : OccurrenceReadout Occurrence Output}
    (factorization : ReadoutFactorization observer readout)
    (consumer : Output → Disposition) :
    ConsumerSafe observer.forget (consumer ∘ readout.read) := by
  intro left right sameVisible
  apply congrArg consumer
  exact factoredReadout_consumerSafe factorization sameVisible

/-- An authority kernel pair is itself the exact hidden residual bearer for
the source-native authority consumer. -/
def authorityKernelPair_hiddenBearer
    {Occurrence : Type u} {Visible : Type v} {Residual : Type w}
    {observer : AuthorityObserver Occurrence Visible Residual}
    (pair : AuthorityKernelPair observer) :
    HiddenNullWitness observer.forget observer.authorityK where
  left := pair.left
  right := pair.right
  sameObservation := pair.visible_eq
  differentDisposition := pair.authority_ne

/-- At any output universe, an ordinary visible factorization over an exact
authority kernel cannot also decode the source authority.  The readout itself
remains available; only the authority-completeness claim is rejected. -/
theorem authorityKernelPair_factoredReadout_authorityComplete_isEmpty
    {Occurrence : Type u} {Visible : Type v} {Residual : Type w}
    {Output : Type x}
    {observer : AuthorityObserver Occurrence Visible Residual}
    (pair : AuthorityKernelPair observer)
    {readout : OccurrenceReadout Occurrence Output}
    (factorization : ReadoutFactorization observer readout) :
    IsEmpty (AuthorityCompleteReadoutAt observer readout) :=
  ⟨fun complete => pair.noAuthorityFactorization
    ⟨factorization.toAuthorityFactorization complete⟩⟩

/-! ## Narrow source-axis relabel no-go -/

/-- Hypothetical source-carrier relabel: a genuine generated world-authority
carrier whose scenario lies outside the actual scenario stored in the exact
installed payload.  Total arbitrary-attempt exhaustion is proved separately
by `SourceNativeObserverConsumerAttemptCompiler`. -/
structure ExactUnaccountedObserverAuthorityAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario) : Type (u + 3) where
  authority : SourceNativeObserverConsumerAuthorityAt recognition visit
    scenario
  outsideInstalled : scenario ≠ recognition.installedActualScenarioAt visit

theorem exactUnaccountedObserverAuthority_isEmpty
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario) :
    IsEmpty (ExactUnaccountedObserverAuthorityAt recognition visit
      scenario) :=
  ⟨fun unaccounted => unaccounted.outsideInstalled
    ((SourceNativeObserverConsumerAuthorityAt.nonempty_iff_installedActualScenario
      (recognition := recognition) (visit := visit) (scenario := scenario)).1
      ⟨unaccounted.authority⟩)⟩

end UniversalRootGrammar
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.rootCofaceRead_consumerSafe_universe
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.sourceNativeScenarioAuthorityStatusAt
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.sourceNativeObserverConsumerExhaustionAt
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeObserverConsumerAuthorityAt.nonempty_iff_installedActualScenario
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeObserverConsumerAuthorityAt.nonempty_iff_exactRootFactorizationAndConsumerSafe
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeObserverConsumerAuthorityAt.rootLedgerAndNext_factorize
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.authorityKernelPair_factoredReadout_authorityComplete_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.exactUnaccountedObserverAuthority_isEmpty
