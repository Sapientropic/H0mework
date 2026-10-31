import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Submission.SourceNativeObserverConsumerSubmissionOccurrence

/-!
# Total compiler of source-generated observer / consumer submissions

The compiler mouth accepts one private execution token indexed by a fixed
submission program and exact temporal root visit.  It receives no material,
certificate, challenge or desired result separately.  The material is
recomputed from that exact root occurrence before world authority is
classified.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace UniversalRootGrammar

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer

universe u v w x y

/-! ## Rooted authority and typed rejection -/

structure SourceNativeObserverConsumerRootedAuthorityAt
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {scenario : recognition.law.vocabulary.Scenario}
    {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
    {attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program
      material) :
    Type (max (u + 3) v w x) where
  private mk ::
  sourceAuthority : SourceNativeObserverConsumerAuthorityAt recognition visit
    scenario
  certificate : SourceNativeSubmittedEffectCertificateAt attempt
  certificateInstalled : material =
    .authorityCertified certificate

namespace SourceNativeObserverConsumerRootedAuthorityAt

variable {N : WorldRelationNetwork.{u}}
  {V : ConstructiveRoot.Vocabulary.{u}}
  {root : SourceNativeLivingRootClosure N V}
  {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
  {visit : SourceNativeTemporalVisitAt
    root.toAuthoritativeRoot.toLedgerRoot}
  {scenario : recognition.law.vocabulary.Scenario}
  {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
  {attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
    Visible Output ClaimedEffect}
  {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
  {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
  {generated : SourceGeneratedObserverConsumerSubmissionAt program material}
  (authority : SourceNativeObserverConsumerRootedAuthorityAt generated)

theorem effect_commutes_with_rootK
    (event : ExactTemporalCausalRootEvent
      root.toAuthoritativeRoot.toLedgerRoot) :
    authority.certificate.complete.decodeAuthority
        (attempt.consumer (attempt.readout.read event)) =
      sourceNativeObserverRootAuthorityKAt recognition event :=
  authority.certificate.complete.readsActualAuthority event

end SourceNativeObserverConsumerRootedAuthorityAt

inductive SourceNativeObserverConsumerRejectionAt
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {scenario : recognition.law.vocabulary.Scenario}
    {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
    {attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program
      material) :
    Type (max (u + 3) v w x)
  | uncertified
      (materialExact : material = .authorityUncertified)
  | hidden
      (challenge : SourceNativeSubmittedKernelChallengeAt attempt)
      (materialExact : material = .authorityChallenged challenge)
      (hiddenBearer : HiddenNullWitness
        attempt.observer.toAuthorityObserver.forget
        attempt.observer.toAuthorityObserver.authorityK)
      (authorityCompleteEmpty : IsEmpty (AuthorityCompleteReadoutAt
        attempt.observer.toAuthorityObserver attempt.consumedReadout))
  | nonActual
      (certificate : SourceNativeSubmittedEffectCertificateAt attempt)
      (materialExact : material = .authorityCertified certificate)
      (outside : scenario ≠ recognition.law.vocabulary.actualScenario)
      (identityDisposition :
        @SourceNativeSearchIdentityDispositionAt N V
          root.toAuthoritativeRoot.toLedgerRoot.source visit.current
          (root.emitted visit.current))

namespace SourceNativeObserverConsumerRejectionAt

variable {N : WorldRelationNetwork.{u}}
  {V : ConstructiveRoot.Vocabulary.{u}}
  {root : SourceNativeLivingRootClosure N V}
  {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
  {visit : SourceNativeTemporalVisitAt
    root.toAuthoritativeRoot.toLedgerRoot}
  {scenario : recognition.law.vocabulary.Scenario}
  {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
  {attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
    Visible Output ClaimedEffect}
  {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
  {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
  {generated : SourceGeneratedObserverConsumerSubmissionAt program material}
  (rejection : SourceNativeObserverConsumerRejectionAt generated)

/-- The exact program-generated occurrence is the visible residual bearer;
its root consumer, whole ledger and next remain available from the index. -/
def residualBearer : AnySourceGeneratedObserverConsumerSubmissionAt attempt :=
  ⟨program, material, generated⟩

end SourceNativeObserverConsumerRejectionAt

inductive SourceNativeObserverConsumerUseDispositionAt
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {scenario : recognition.law.vocabulary.Scenario}
    {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
    {attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program
      material) :
    Type (max (u + 3) v w x)
  | presentation
  | rooted
      (authority : SourceNativeObserverConsumerRootedAuthorityAt generated)
  | rejected
      (rejection : SourceNativeObserverConsumerRejectionAt generated)

namespace SourceNativeObserverConsumerUseDispositionAt

def IsRooted
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {scenario : recognition.law.vocabulary.Scenario}
    {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
    {attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    {generated : SourceGeneratedObserverConsumerSubmissionAt program
      material} :
    SourceNativeObserverConsumerUseDispositionAt generated → Prop
  | .presentation => False
  | .rooted _ => True
  | .rejected _ => False

end SourceNativeObserverConsumerUseDispositionAt

structure SourceNativeCompiledObserverConsumerSubmissionAt
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {scenario : recognition.law.vocabulary.Scenario}
    {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
    {attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program
      material) :
    Type (max (u + 3) v w x) where
  worldAuthorityStatus : SourceNativeScenarioAuthorityStatusAt
    recognition.law.vocabulary scenario
  grammar : SourceGeneratedUniversalRootGrammarAt recognition visit scenario
  presentedEffect : ClaimedEffect
  sourceOccurrence : ExactTemporalCausalRootEvent
    root.toAuthoritativeRoot.toLedgerRoot
  rootConsumerSafe : ConsumerSafe
    (@rootCofaceRead _ _ root.toAuthoritativeRoot.toLedgerRoot)
    attempt.consumedReadout.read
  useDisposition : SourceNativeObserverConsumerUseDispositionAt generated

/-- Total source compiler.  `generated` is the sole explicit mouth. -/
def compileSourceNativeObserverConsumerSubmissionAt
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {scenario : recognition.law.vocabulary.Scenario}
    {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
    {attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program
      material) :
    SourceNativeCompiledObserverConsumerSubmissionAt generated := by
  let status := sourceNativeScenarioAuthorityStatusAt
    recognition.law.vocabulary scenario
  let grammar := sourceGeneratedUniversalRootGrammarAt recognition visit
    scenario
  let presented := generated.presentedEffect
  let sourceOccurrence := generated.sourceOccurrence
  let consumerSafe : ConsumerSafe
      (@rootCofaceRead _ _ root.toAuthoritativeRoot.toLedgerRoot)
      attempt.consumedReadout.read :=
    rootCofaceRead_consumerSafe_universe attempt.consumedReadout.read
  match material with
  | .presentation =>
      exact ⟨status, grammar, presented, sourceOccurrence, consumerSafe,
        .presentation⟩
  | .authorityUncertified =>
      exact ⟨status, grammar, presented, sourceOccurrence, consumerSafe,
        .rejected (.uncertified rfl)⟩
  | .authorityChallenged challenge =>
      exact ⟨status, grammar, presented, sourceOccurrence, consumerSafe,
        .rejected (.hidden challenge rfl challenge.hiddenBearer
          challenge.authorityCompleteEmpty)⟩
  | .authorityCertified certificate =>
      match status with
      | .actual scenarioAuthority =>
          let sourceAuthority :
              SourceNativeObserverConsumerAuthorityAt recognition visit
                scenario :=
            SourceNativeObserverConsumerAuthorityAt.ofScenarioAuthority
              scenarioAuthority
          exact ⟨status, grammar, presented, sourceOccurrence, consumerSafe,
            .rooted ⟨sourceAuthority, certificate, rfl⟩⟩
      | .nonActual outside =>
          let identityDisposition :=
            @sourceNativeSearchIdentityDispositionAt N V
              root.toAuthoritativeRoot.toLedgerRoot.source visit.current
                (root.emitted visit.current)
          exact ⟨status, grammar, presented, sourceOccurrence, consumerSafe,
            .rejected (.nonActual certificate rfl outside
              identityDisposition)⟩

namespace SourceGeneratedObserverConsumerSubmissionAt

def CarriesCertifiedAuthority
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {scenario : recognition.law.vocabulary.Scenario}
    {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
    {attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (_generated : SourceGeneratedObserverConsumerSubmissionAt program
      material) : Prop :=
  ∃ certificate : SourceNativeSubmittedEffectCertificateAt attempt,
    material = .authorityCertified certificate

end SourceGeneratedObserverConsumerSubmissionAt

/-! ## Compiler laws -/

theorem compile_presentation_exact
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {scenario : recognition.law.vocabulary.Scenario}
    {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
    (attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
      Visible Output ClaimedEffect) :
    let program := presentationSubmissionProgramAt attempt
    (compileSourceNativeObserverConsumerSubmissionAt program.generate
      ).useDisposition = .presentation := by
  rfl

theorem compile_uncertified_isRejected
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {scenario : recognition.law.vocabulary.Scenario}
    {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
    (attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
      Visible Output ClaimedEffect) :
    let program := uncertifiedAuthoritySubmissionProgramAt attempt
    ∃ rejection : SourceNativeObserverConsumerRejectionAt program.generate,
      (compileSourceNativeObserverConsumerSubmissionAt program.generate
        ).useDisposition = .rejected rejection := by
  exact ⟨.uncertified rfl, rfl⟩

theorem compile_challenged_isHiddenRejected
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {scenario : recognition.law.vocabulary.Scenario}
    {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
    (attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
      Visible Output ClaimedEffect)
    (challenge : SourceNativeSubmittedKernelChallengeAt attempt) :
    let program := kernelChallengedAuthoritySubmissionProgramAt attempt
      challenge
    ∃ rejection : SourceNativeObserverConsumerRejectionAt program.generate,
      (compileSourceNativeObserverConsumerSubmissionAt program.generate
        ).useDisposition = .rejected rejection := by
  exact
    ⟨.hidden challenge rfl challenge.hiddenBearer
        challenge.authorityCompleteEmpty,
      rfl⟩

theorem compile_isRooted_iff_certifiedAndInstalledActual
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {scenario : recognition.law.vocabulary.Scenario}
    {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
    {attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program
      material) :
    (compileSourceNativeObserverConsumerSubmissionAt generated
        ).useDisposition.IsRooted ↔
      generated.CarriesCertifiedAuthority ∧
        scenario = recognition.installedActualScenarioAt visit := by
  cases material with
  | presentation =>
      simp [compileSourceNativeObserverConsumerSubmissionAt,
        SourceGeneratedObserverConsumerSubmissionAt.CarriesCertifiedAuthority,
        SourceNativeObserverConsumerUseDispositionAt.IsRooted]
  | authorityUncertified =>
      simp [compileSourceNativeObserverConsumerSubmissionAt,
        SourceGeneratedObserverConsumerSubmissionAt.CarriesCertifiedAuthority,
        SourceNativeObserverConsumerUseDispositionAt.IsRooted]
  | authorityChallenged challenge =>
      simp [compileSourceNativeObserverConsumerSubmissionAt,
        SourceGeneratedObserverConsumerSubmissionAt.CarriesCertifiedAuthority,
        SourceNativeObserverConsumerUseDispositionAt.IsRooted]
  | authorityCertified certificate =>
      cases recognition.law.vocabulary.scenarioDecidableEq scenario
          recognition.law.vocabulary.actualScenario with
      | isTrue scenarioExact =>
          subst scenario
          simp [compileSourceNativeObserverConsumerSubmissionAt,
            sourceNativeScenarioAuthorityStatusAt,
            SourceGeneratedObserverConsumerSubmissionAt.CarriesCertifiedAuthority,
            SourceNativeObserverConsumerUseDispositionAt.IsRooted,
            recognition.installedActualScenario_eq]
      | isFalse scenarioExact =>
          have outsideInstalled :
              scenario ≠ recognition.installedActualScenarioAt visit := by
            intro installedExact
            exact scenarioExact
              (installedExact.trans
                (recognition.installedActualScenario_eq visit))
          simp [compileSourceNativeObserverConsumerSubmissionAt,
            sourceNativeScenarioAuthorityStatusAt,
            scenarioExact,
            SourceGeneratedObserverConsumerSubmissionAt.CarriesCertifiedAuthority,
            SourceNativeObserverConsumerUseDispositionAt.IsRooted,
            outsideInstalled]

theorem compile_certified_isRooted_iff_installedActual
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {scenario : recognition.law.vocabulary.Scenario}
    {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
    (attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
      Visible Output ClaimedEffect)
    (certificate : SourceNativeSubmittedEffectCertificateAt attempt) :
    let program := certifiedAuthoritySubmissionProgramAt attempt certificate
    (compileSourceNativeObserverConsumerSubmissionAt program.generate
        ).useDisposition.IsRooted ↔
      scenario = recognition.installedActualScenarioAt visit := by
  let program := certifiedAuthoritySubmissionProgramAt attempt certificate
  have carries : program.generate.CarriesCertifiedAuthority :=
    ⟨certificate, rfl⟩
  have maximum :=
    compile_isRooted_iff_certifiedAndInstalledActual program.generate
  constructor
  · intro rooted
    exact (maximum.mp rooted).2
  · intro actual
    exact maximum.mpr ⟨carries, actual⟩

theorem compiledSubmission_exhaustive
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {scenario : recognition.law.vocabulary.Scenario}
    {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
    {attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program
      material) :
    let compiled := compileSourceNativeObserverConsumerSubmissionAt generated
    (compiled.useDisposition = .presentation) ∨
      (∃ authority : SourceNativeObserverConsumerRootedAuthorityAt generated,
        compiled.useDisposition = .rooted authority) ∨
      (∃ rejection : SourceNativeObserverConsumerRejectionAt generated,
        compiled.useDisposition = .rejected rejection) := by
  intro compiled
  cases compiled.useDisposition with
  | presentation => exact Or.inl rfl
  | rooted authority => exact Or.inr (Or.inl ⟨authority, rfl⟩)
  | rejected rejection => exact Or.inr (Or.inr ⟨rejection, rfl⟩)

/-- Two tokens of one fixed program/exact visit cannot produce a second
disposition.  This consumes token subsingleton, not an `x = f` premise. -/
theorem sameExactSubmission_noSecondDisposition
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {scenario : recognition.law.vocabulary.Scenario}
    {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
    {attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (left right : SourceGeneratedObserverConsumerSubmissionAt program
      material) :
    (compileSourceNativeObserverConsumerSubmissionAt left).useDisposition =
      (compileSourceNativeObserverConsumerSubmissionAt right).useDisposition := by
  have tokenExact : left = right := Subsingleton.elim left right
  cases tokenExact
  rfl

/-! ## Anti-regression no-go -/

def bodyTotalizer_forces_decidable
    {Body : Type y} {Semantic : Body → Prop}
    (totalizer : Body → Bool)
    (exact : ∀ body, totalizer body = true ↔ Semantic body)
    (body : Body) : Decidable (Semantic body) := by
  cases tagged : totalizer body with
  | false =>
      exact isFalse (fun semantic => by
        have : totalizer body = true := (exact body).2 semantic
        simp [tagged] at this)
  | true => exact isTrue ((exact body).1 tagged)

end UniversalRootGrammar
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.compileSourceNativeObserverConsumerSubmissionAt
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeObserverConsumerRootedAuthorityAt.effect_commutes_with_rootK
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.compile_isRooted_iff_certifiedAndInstalledActual
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.compiledSubmission_exhaustive
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.sameExactSubmission_noSecondDisposition
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.bodyTotalizer_forces_decidable
