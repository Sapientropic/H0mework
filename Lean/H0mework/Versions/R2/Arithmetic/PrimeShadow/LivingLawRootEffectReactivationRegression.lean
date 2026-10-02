import H0mework.Versions.R2.Foundation.Runtime.EffectReactivation
import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawRootEffectDynamicalClosureRegression

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace EffectReactivationDirectSpliceRegression

open ConstructiveRoot
open ConstructiveRoot.OperationalU7RootLedgerRegression
open RootEffectDynamicalClosureRegression
open RootEffectDynamicalClosureRegression.RecursiveNext

def lifecycleEventVocabulary :
    SourceNativeEffectEventVocabulary recursiveLedgerSource where
  Effect := Bool
  Operational := Bool
  effectAt := fun {current} _ => current
  operationalAt := fun {current} _ => current

inductive LifecycleActiveAt : {current : RecursiveV.Current} →
    SourceNativeEffectOccurrenceAt lifecycleEventVocabulary current → Type
  | active (occurrence : SourceNativeEffectOccurrenceAt
      lifecycleEventVocabulary true) : LifecycleActiveAt occurrence

inductive LifecycleInactiveAt : {current : RecursiveV.Current} →
    SourceNativeEffectOccurrenceAt lifecycleEventVocabulary current → Type
  | inactive (occurrence : SourceNativeEffectOccurrenceAt
      lifecycleEventVocabulary false) : LifecycleInactiveAt occurrence

def lifecycleVocabulary :
    SourceNativeEffectDynamicalVocabulary lifecycleEventVocabulary where
  ActiveAt := LifecycleActiveAt
  InactiveAt := LifecycleInactiveAt
  classify := by
    intro current occurrence
    cases current
    · exact .inr (.inactive occurrence)
    · exact .inl (.active occurrence)
  effectEntryAt := fun _ _ => recursiveEntry
  updateEffectAt := fun occurrence _ sourceEffect => !sourceEffect
  updateOperationalAt := fun occurrence _ sourceEffect sourceOperational =>
    !sourceOperational

def lifecycleEffectLaw :
    SourceNativeEffectDynamicalClosureLaw recursiveLedgerSource :=
  .create OperationalSeparationRegression.U7
    RootEffectDynamicalClosureRegression.U7Calculus
    lifecycleEventVocabulary lifecycleVocabulary <| by
      intro current occurrence active
      cases active with
      | active occurrence =>
        rcases occurrence with ⟨lower⟩
        rcases lower with ⟨support, event⟩
        cases support
        · exact nomatch event
        · let successor :=
            (@SourceNativeEffectGeneratedSuccessorAt.ofGenerated?
              RecursiveN RecursiveV recursiveLedgerSource true
              ⟨true, event⟩
              (recursiveLedgerCompiler.compile ⟨true, event⟩)).get (by rfl)
          let row := recursiveGeneratedEntryAt ⟨true, event⟩
          refine .cut row successor () rfl ?_
          have commutes := row.down.commutes_with_world
          rcases commutes with ⟨_, evolution_heq⟩
          cases evolution_heq
          rfl

structure BoolReactivationReceiptAt
    {current : RecursiveV.Current}
    (occurrence : SourceNativeEffectOccurrenceAt lifecycleEventVocabulary current)
    (inactive : lifecycleVocabulary.InactiveAt occurrence)
    {generated : SourceNativeLedgerEvolutionAt recursiveLedgerSource.source
      occurrence.lower}
    (successor : SourceNativeEffectGeneratedSuccessorAt occurrence.lower generated)
    (targetActive : lifecycleVocabulary.ActiveAt
      (lifecycleEventVocabulary.emit successor.targetOccurrence)) : Type where
  sourceEffect_eq_false : occurrence.effect = false
  targetEffect_eq_true :
    (lifecycleEventVocabulary.emit successor.targetOccurrence).effect = true

def lifecycleDormantVocabulary :
    SourceNativeEffectDormantVocabulary lifecycleVocabulary where
  inactiveEntryAt := fun _ _ => recursiveEntry
  ReactivationReceiptAt := BoolReactivationReceiptAt

def lifecycleGenerateInactive
    {current : RecursiveV.Current}
    (occurrence : SourceNativeEffectOccurrenceAt lifecycleEventVocabulary current)
    (inactive : lifecycleVocabulary.InactiveAt occurrence) :
    SourceNativeDormantEffectDispositionAt lifecycleVocabulary
      lifecycleDormantVocabulary
      RootEffectDynamicalClosureRegression.U7Calculus occurrence inactive
      (recursiveLedgerSource.ledgerCompiler.compile occurrence.lower) := by
  cases inactive with
  | inactive occurrence =>
    rcases occurrence with ⟨lower⟩
    rcases lower with ⟨support, event⟩
    cases support
    · exact nomatch event
    · let successor :=
        (@SourceNativeEffectGeneratedSuccessorAt.ofGenerated?
          RecursiveN RecursiveV recursiveLedgerSource false
          ⟨true, event⟩
          (recursiveLedgerCompiler.compile ⟨true, event⟩)).get (by rfl)
      let row := recursiveGeneratedEntryAt ⟨true, event⟩
      have targetActive : lifecycleVocabulary.ActiveAt
          (lifecycleEventVocabulary.emit successor.targetOccurrence) :=
        .active _
      have targetEntry_eq :
          (successor.ledgerEvolution.destination recursiveEntry).1 =
            recursiveEntry :=
        rootEntry_eq _
      have targetClassifyEq : lifecycleVocabulary.classify
          (lifecycleEventVocabulary.emit successor.targetOccurrence) =
          .inl targetActive := by
        change Sum.inl (.active _) = Sum.inl targetActive
        cases targetActive
        rfl
      exact .reactivated row successor targetActive targetClassifyEq
        ⟨targetEntry_eq⟩ ⟨rfl, rfl⟩

def lifecycleLaw :
    SourceNativeEffectReactivationClosureLaw recursiveLedgerSource :=
  .create lifecycleEffectLaw lifecycleDormantVocabulary
    lifecycleGenerateInactive

def lifecycleAuthority : SourceNativeAuthoritySource RecursiveN RecursiveV :=
  lifecycleLaw.toAuthoritySource recursiveBaseAuthority

def lifecycleSource : SourceNativeLivingAuthoritySource RecursiveN RecursiveV where
  base := lifecycleAuthority
  terminalHandoff := lifecycleAuthority.emptyFaithfulTerminalHandoff
    (fun _ => ⟨fun terminal => nomatch terminal⟩)

def lifecycleWorld : SourceNativeLivingRootClosure RecursiveN RecursiveV where
  source := lifecycleSource
  emitted := recursiveEmitted
  compiler_commutes := fun _ => rfl

def lifecycleRecognition :
    SourceNativeEffectReactivationRecognitionAt lifecycleWorld where
  lifecycleLaw := lifecycleLaw
  installation :=
    SourceNativeProjectionLaw.InstallationAt.effectReactivationComponent
      recursiveBaseAuthority lifecycleLaw

def lifecycleVisit : SourceNativeTemporalVisitAt
    lifecycleWorld.toAuthoritativeRoot.toLedgerRoot :=
  .finite lifecycleWorld.toAuthoritativeRoot.toRoot.initialVisit

def lifecycleSourceAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt lifecycleWorld
      lifecycleVisit recursiveEntry :=
  ((SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial?
      lifecycleWorld recursiveEntry .initial).get (by rfl)).2

def rootedDormant : lifecycleRecognition.RootedLifecycleOutcomeAt
    lifecycleVisit :=
  lifecycleRecognition.generatedRootedLifecycleAtVisit lifecycleVisit
    (.inr (.inactive _)) rfl lifecycleSourceAuthority

def DormantDispositionIsReactivated
    {current : RecursiveV.Current}
    {occurrence : SourceNativeEffectOccurrenceAt lifecycleEventVocabulary current}
    {inactive : lifecycleVocabulary.InactiveAt occurrence}
    {generated : SourceNativeLedgerEvolutionAt recursiveLedgerSource.source
      occurrence.lower}
    (disposition : SourceNativeDormantEffectDispositionAt lifecycleVocabulary
      lifecycleDormantVocabulary
      RootEffectDynamicalClosureRegression.U7Calculus occurrence inactive
      generated) : Prop :=
  match disposition with
  | .reactivated .. => True
  | _ => False

theorem dormant_initial_generates_paid_reactivation :
    DormantDispositionIsReactivated
      (lifecycleGenerateInactive
        (lifecycleEventVocabulary.emit (recursiveEmitted false)) (.inactive _)) := by
  change DormantDispositionIsReactivated
    (lifecycleGenerateInactive
      (⟨⟨true, ()⟩⟩ :
        SourceNativeEffectOccurrenceAt lifecycleEventVocabulary false)
      (.inactive _))
  change True
  trivial

/-- The target active fibre cannot be obtained by deleting the generated
reactivation receipt from the exact lifecycle payload. -/
theorem bare_inactive_to_active_is_not_a_lifecycle_constructor : True := by
  let successor :=
    ((@SourceNativeEffectGeneratedSuccessorAt.ofGenerated?
      RecursiveN RecursiveV recursiveLedgerSource false
      (recursiveEmitted false)
      (recursiveLedgerCompiler.compile (recursiveEmitted false))).get (by rfl))
  let targetActive : lifecycleVocabulary.ActiveAt
      (lifecycleEventVocabulary.emit successor.targetOccurrence) := .active _
  have targetClassifyEq : lifecycleVocabulary.classify
      (lifecycleEventVocabulary.emit successor.targetOccurrence) =
      .inl targetActive := by
    change Sum.inl (.active _) = Sum.inl targetActive
    cases targetActive
    rfl
  fail_if_success
    exact SourceNativeDormantEffectDispositionAt.reactivated
      (recursiveGeneratedEntryAt (recursiveEmitted false))
      successor targetActive targetClassifyEq ⟨rootEntry_eq _⟩
  trivial

#print axioms SourceNativeEffectReactivationRecognitionAt.RootedLifecycleOutcomeAt.status_eq_of_same_visit
#print axioms SourceNativeEffectReactivationRecognitionAt.RootedLifecycleOutcomeAt.payload_heq_of_same_visit
#print axioms dormant_initial_generates_paid_reactivation

end EffectReactivationDirectSpliceRegression
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
