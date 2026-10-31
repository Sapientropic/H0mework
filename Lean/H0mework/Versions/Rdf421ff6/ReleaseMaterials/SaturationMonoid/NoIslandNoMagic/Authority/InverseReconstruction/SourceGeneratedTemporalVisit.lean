import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Submission.SourceNativeObserverConsumerSubmissionCompiler

/-!
# Source-generated reconstruction from temporal visits

An exact temporal root event is a dependent pair of a visit and the compiler
image generated at that visit.  Forgetting the dependent image is a genuine
observer, but every visit fibre is a singleton by the existing
`eq_generated` law.  The source therefore reconstructs the complete event,
its authority readout, and an actual certified submission without accepting
a reconstruction, decoder, certificate, factorization, or rooted branch from
the caller.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace UniversalRootGrammar

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer

universe u v w x

section


variable
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}

abbrev TemporalVisitVisibleAt
    (_recognition : SourceNativeDependentFaceFamilyRecognitionAt root) :=
  SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot

/-- Observer which forgets only the dependent generated-event token and
retains its exact temporal visit. -/
def temporalVisitObserverAt
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root) :
    SourceNativeSocietyObserverAt recognition
      (TemporalVisitVisibleAt recognition) where
  forget := Sigma.fst

/-- Canonical event reconstructed by rerunning the fixed root generator at
the visible visit. -/
def temporalVisitEventAt
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : TemporalVisitVisibleAt recognition) :
    ExactTemporalCausalRootEvent
      root.toAuthoritativeRoot.toLedgerRoot :=
  ⟨visit,
    root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit⟩

@[simp] theorem temporalVisitEventAt_forget
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : TemporalVisitVisibleAt recognition) :
    (temporalVisitObserverAt recognition).forget
        (temporalVisitEventAt recognition visit) = visit :=
  rfl

@[simp] theorem temporalVisitEventAt_recovers
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (event : ExactTemporalCausalRootEvent
      root.toAuthoritativeRoot.toLedgerRoot) :
    temporalVisitEventAt recognition
        ((temporalVisitObserverAt recognition).forget event) = event := by
  rcases event with ⟨visit, generated⟩
  exact Sigma.ext rfl (heq_of_eq generated.eq_generated.symm)

theorem temporalVisitObserver_forget_injective
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root) :
    Function.Injective (temporalVisitObserverAt recognition).forget := by
  intro left right sameVisit
  calc
    left = temporalVisitEventAt recognition
        ((temporalVisitObserverAt recognition).forget left) :=
      (temporalVisitEventAt_recovers recognition left).symm
    _ = temporalVisitEventAt recognition
        ((temporalVisitObserverAt recognition).forget right) :=
      congrArg (temporalVisitEventAt recognition) sameVisit
    _ = right := temporalVisitEventAt_recovers recognition right

/-- The canonical reconstruction commutes with every admissible automorphism
because both sides lie over the same visit and that fibre has one generated
event. -/
theorem temporalVisitEventAt_natural
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (automorphism : AdmissibleObserverAutomorphism
      (temporalVisitObserverAt recognition).toAuthorityObserver)
    (visit : TemporalVisitVisibleAt recognition) :
    temporalVisitEventAt recognition
        (automorphism.visibleEquiv visit) =
      automorphism.occurrenceEquiv
        (temporalVisitEventAt recognition visit) := by
  apply temporalVisitObserver_forget_injective recognition
  calc
    (temporalVisitObserverAt recognition).forget
        (temporalVisitEventAt recognition
          (automorphism.visibleEquiv visit)) =
        automorphism.visibleEquiv visit := rfl
    _ = automorphism.visibleEquiv
        ((temporalVisitObserverAt recognition).forget
          (temporalVisitEventAt recognition visit)) := rfl
    _ = (temporalVisitObserverAt recognition).forget
        (automorphism.occurrenceEquiv
          (temporalVisitEventAt recognition visit)) :=
      (automorphism.forget_commutes
        (temporalVisitEventAt recognition visit)).symm

/-- Full positive reconstruction generated from the fixed temporal root.
No surrogate section or completeness certificate is an input. -/
def temporalVisitNaturalReconstruction
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root) :
    NaturalAuthorityReconstruction
      (temporalVisitObserverAt recognition).toAuthorityObserver where
  lift := temporalVisitEventAt recognition
  lift_forget := temporalVisitEventAt_forget recognition
  naturality := temporalVisitEventAt_natural recognition
  preservesAuthority := by
    intro automorphism visit
    rw [temporalVisitEventAt_natural recognition automorphism visit]
    exact automorphism.authority_commutes
      (temporalVisitEventAt recognition visit)
  readAuthority := fun visit =>
    (temporalVisitObserverAt recognition).toAuthorityObserver.authorityK
      (temporalVisitEventAt recognition visit)
  preservesActualAuthority := fun event =>
    congrArg
      (temporalVisitObserverAt recognition).toAuthorityObserver.authorityK
      (temporalVisitEventAt_recovers recognition event)
  recoversOccurrence := temporalVisitEventAt_recovers recognition

/-- Actual-scenario authority attempt whose readout is the root's own `K`.
The observer still forgets the generated dependent token to its visit. -/
def temporalVisitAuthorityAttemptAt
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : TemporalVisitVisibleAt recognition) :
    SourceNativeObserverConsumerAttemptAt recognition visit
      recognition.law.vocabulary.actualScenario
      (TemporalVisitVisibleAt recognition)
      (SourceNativeObserverRootAuthorityKAt recognition)
      (SourceNativeObserverRootAuthorityKAt recognition) where
  observer := temporalVisitObserverAt recognition
  readout :=
    { read := sourceNativeObserverRootAuthorityKAt recognition }
  consumer := id

@[simp] theorem temporalVisitAuthorityAttemptAt_consumedReadout
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : TemporalVisitVisibleAt recognition)
    (event : ExactTemporalCausalRootEvent
      root.toAuthoritativeRoot.toLedgerRoot) :
    (temporalVisitAuthorityAttemptAt recognition visit).consumedReadout.read
        event = sourceNativeObserverRootAuthorityKAt recognition event :=
  rfl

/-- Factorization and authority completeness are derived internally from the
source-generated reconstruction. -/
def temporalVisitSourceCertificateAt
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : TemporalVisitVisibleAt recognition) :
    SourceNativeSubmittedEffectCertificateAt
      (temporalVisitAuthorityAttemptAt recognition visit) where
  factorization :=
    { visibleReadout :=
        (temporalVisitNaturalReconstruction recognition).readAuthority
      factorizes := fun event =>
        (temporalVisitNaturalReconstruction recognition
          |>.preservesActualAuthority event).symm }
  complete :=
    { decodeAuthority := id
      readsActualAuthority := fun _event => rfl }

/-- The complete actual submission program closes over only the internally
generated certificate. -/
def temporalVisitCertifiedActualProgramAt
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : TemporalVisitVisibleAt recognition) :=
  certifiedAuthoritySubmissionProgramAt
    (temporalVisitAuthorityAttemptAt recognition visit)
    (temporalVisitSourceCertificateAt recognition visit)

theorem temporalVisitCertifiedActual_isRooted
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : TemporalVisitVisibleAt recognition) :
    (compileSourceNativeObserverConsumerSubmissionAt
      (temporalVisitCertifiedActualProgramAt recognition visit).generate
      ).useDisposition.IsRooted := by
  apply (compile_certified_isRooted_iff_installedActual
    (temporalVisitAuthorityAttemptAt recognition visit)
    (temporalVisitSourceCertificateAt recognition visit)).2
  exact (recognition.installedActualScenario_eq visit).symm

/-- Constructively extract the rooted authority selected by an exact
disposition; impossible presentation/rejection cases carry `False`. -/
def SourceNativeObserverConsumerUseDispositionAt.rootedAuthorityOfIsRooted
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
    (disposition : SourceNativeObserverConsumerUseDispositionAt generated) :
    disposition.IsRooted →
      SourceNativeObserverConsumerRootedAuthorityAt generated := by
  cases disposition with
  | presentation => intro impossible; exact False.elim impossible
  | rooted authority => intro _rooted; exact authority
  | rejected _rejection => intro impossible; exact False.elim impossible

/-- Rooted authority emitted by the compiled source-generated positive
reconstruction. -/
def temporalVisitCertifiedActualRootedAuthority
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : TemporalVisitVisibleAt recognition) :
    SourceNativeObserverConsumerRootedAuthorityAt
      (temporalVisitCertifiedActualProgramAt recognition visit).generate :=
  SourceNativeObserverConsumerUseDispositionAt.rootedAuthorityOfIsRooted
    (compileSourceNativeObserverConsumerSubmissionAt
      (temporalVisitCertifiedActualProgramAt recognition visit).generate
      ).useDisposition
    (temporalVisitCertifiedActual_isRooted recognition visit)

/-- Direct authority consumer: the extracted rooted branch still reads the
root's exact `K` on every temporal event. -/
theorem temporalVisitCertifiedActual_effect_commutes_with_rootK
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : TemporalVisitVisibleAt recognition)
    (event : ExactTemporalCausalRootEvent
      root.toAuthoritativeRoot.toLedgerRoot) :
    (temporalVisitCertifiedActualRootedAuthority recognition visit
      ).certificate.complete.decodeAuthority
        ((temporalVisitAuthorityAttemptAt recognition visit).consumer
          ((temporalVisitAuthorityAttemptAt recognition visit).readout.read
            event)) =
      sourceNativeObserverRootAuthorityKAt recognition event :=
  (temporalVisitCertifiedActualRootedAuthority recognition visit
    ).effect_commutes_with_rootK event

/-- The same rooted authority retains the installed root occurrence, whole
ledger, and generated next. -/
theorem temporalVisitCertifiedActual_rootLedgerAndNext_factorize
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : TemporalVisitVisibleAt recognition) :
    type_of%
      (temporalVisitCertifiedActualRootedAuthority recognition visit
        ).sourceAuthority.rootLedgerAndNext_factorize :=
  (temporalVisitCertifiedActualRootedAuthority recognition visit
    ).sourceAuthority.rootLedgerAndNext_factorize

end

end UniversalRootGrammar
end Society
end ProcessGame
end SaturationMonoid
