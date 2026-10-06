import H0mework.Foundation.Runtime.Activation
import H0mework.Arithmetic.RiemannRuntime.PairedOmegaEffectRowRoot

/-!
# Canonical finite history of the A1c paired-Omega effect row

The installed effect root is organized as one source-fixed living process.
Every finite stage is obtained by the canonical unit-root successor, carries
the same compiler-owned causal row authority, and exposes the installed
paired effect through the pre-emitter projection inventory.  The generic
runtime material history supplies the finite chronology; no caller history,
effect table or future row enters the construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram
namespace IntegralGraphJointAction

open CanonicalUnitArithmeticRoot

noncomputable section

def runtimeEffectVisitAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    SourceNativeTemporalVisitAt
      (runtimeEffectRoot observation nontrivial
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (CanonicalUnitArithmeticRoot.finiteVisit depth)

def runtimeEffectTemporalDepth?
    (current : SourceNativeLivingRootCurrentAt N) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

theorem runtimeEffectVisitAt_depth
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    runtimeEffectTemporalDepth?
        ⟨V, runtimeEffectRoot observation nontrivial,
          runtimeEffectVisitAt observation nontrivial depth⟩ = some depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change
        some (ProductiveFiniteRootHistoryAt.causalDepth
          (CanonicalUnitArithmeticRoot.finiteVisit depth).history + 1) =
            some (depth + 1)
      have priorDepth :
          ProductiveFiniteRootHistoryAt.causalDepth
              (CanonicalUnitArithmeticRoot.finiteVisit depth).history = depth := by
        change some (ProductiveFiniteRootHistoryAt.causalDepth
          (CanonicalUnitArithmeticRoot.finiteVisit depth).history) =
            some depth at inductionHypothesis
        exact Option.some.inj inductionHypothesis
      rw [priorDepth]

/-- The complete installed-effect root process.  Its state is only the
canonical finite depth, which is injectively recoverable from the visit. -/
def runtimeEffectProcess
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRootProcess N where
  State := Nat
  stateAt := fun depth =>
    ⟨V, runtimeEffectRoot observation nontrivial,
      runtimeEffectVisitAt observation nontrivial depth⟩
  stateAt_injective := by
    intro left right equality
    have depthEquality := congrArg runtimeEffectTemporalDepth? equality
    rw [runtimeEffectVisitAt_depth observation nontrivial left,
      runtimeEffectVisitAt_depth observation nontrivial right] at depthEquality
    exact Option.some.inj depthEquality
  initial := 0
  successorAt := fun depth => ⟨depth + 1, rfl, by rfl⟩

def runtimeEffectRuntimeSeed
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    LivingRuntimeState (runtimeEffectProcess observation nontrivial) :=
  .initial _

def runtimeEffectRuntimeAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    LivingRuntimeState (runtimeEffectProcess observation nontrivial) :=
  (runtimeEffectRuntimeSeed observation nontrivial).advance depth

@[simp] theorem runtimeEffectRuntimeAt_state
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeEffectRuntimeAt observation nontrivial depth).state = depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change (runtimeEffectProcess observation nontrivial).successor
          (runtimeEffectRuntimeAt observation nontrivial depth).state =
        depth + 1
      simp only [SourceNativeLivingRootProcess.successor, runtimeEffectProcess]
      exact congrArg (fun value : Nat => value + 1) inductionHypothesis

/-- The generic calculation firewall now carries the installed effect root
through every requested finite compiler prefix. -/
def runtimeEffectFiniteMaterialHistory
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (length : Nat) :
    SourceGeneratedRuntimeMaterialHistoryAt
      (runtimeEffectRuntimeSeed observation nontrivial) length :=
  .generate _ _

theorem runtimeEffectFiniteMaterialStage_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (length : Nat) (stage : Fin length) :
    let materialStage :=
      (runtimeEffectFiniteMaterialHistory observation nontrivial length
        ).stageAt stage
    let runtime :=
      (runtimeEffectRuntimeSeed observation nontrivial).advance stage.1
    (runtimeEffectProcess observation nontrivial).toAnswerNextCausalWorld.emitted
          (ULift.up runtime.state) =
        ULift.up materialStage.activated.generated ∧
      materialStage.activated.generated.occurrence =
        runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          runtime.current.visit.current ∧
      HEq materialStage.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      materialStage.next.current = materialStage.activated.nextCurrent := by
  exact (runtimeEffectFiniteMaterialHistory observation nontrivial length
    |>.stageAt stage).factorizes

private def runtimeEffectFiniteCausalAuthorityAtHistory
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (history : (runtimeEffectRoot observation nontrivial
      ).toAuthoritativeRoot.toRoot.ReachableAt current) :
    (runtimeEffectRecognition observation nontrivial).CausalEntryAuthorityAt
      (.finite ⟨current, history⟩) (rootLedgerEntry current) :=
  match history with
  | .initial => runtimeEffectSourceAuthority observation nontrivial
  | .step prior next_eq => by
      let generated :=
        (runtimeEffectFiniteCausalAuthorityAtHistory
          observation nontrivial prior).next next_eq
      have entry_eq := rootLedgerEntry_unique current
        ((runtimeEffectRoot observation nontrivial
          ).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
            next_eq (rootLedgerEntry _))
      exact entry_eq ▸ generated

def runtimeEffectSourceAuthorityAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeEffectRecognition observation nontrivial).CausalEntryAuthorityAt
      (runtimeEffectVisitAt observation nontrivial depth)
      (rootLedgerEntry
        (runtimeEffectVisitAt observation nontrivial depth).current) :=
  runtimeEffectFiniteCausalAuthorityAtHistory observation nontrivial
    (CanonicalUnitArithmeticRoot.finiteVisit depth).history

def runtimeEffectRootedActiveAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeEffectRecognition observation nontrivial).RootedActiveOutcomeAt
      (runtimeEffectVisitAt observation nontrivial depth) :=
  (runtimeEffectRecognition observation nontrivial
    ).generatedRootedActiveAtVisit
      (runtimeEffectVisitAt observation nontrivial depth) () rfl
      (runtimeEffectSourceAuthorityAt observation nontrivial depth)

theorem installedRuntimeEffectAt_factorizes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    let registered := runtimeEffectRootedActiveAt observation nontrivial depth
    let root := runtimeEffectRoot observation nontrivial
    let visit := runtimeEffectVisitAt observation nontrivial depth
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (evolution.generated.projectionOutcome
          (runtimeEffectRecognition observation nontrivial
            ).rootEffectProjection)
        registered.installedFiber ∧
      evolution.nextCurrent = root.generatedNextCurrentAt visit :=
  (runtimeEffectRootedActiveAt observation nontrivial depth
    ).installedAuthority_factorizes

def installedRuntimeEffectOccurrenceAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :=
  (runtimeEffectLaw observation nontrivial).eventVocabulary.emit
    ((runtimeEffectRoot observation nontrivial).emitted
      (runtimeEffectVisitAt observation nontrivial depth).current)

def installedRuntimeEffectValueAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) : RuntimeEffect :=
  (installedRuntimeEffectOccurrenceAt observation nontrivial depth).effect

@[simp] theorem installedRuntimeEffectValueAt_eq_current
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    installedRuntimeEffectValueAt observation nontrivial depth =
      generateRuntimeEffect observation nontrivial
        (CanonicalUnitArithmeticRoot.finiteVisit depth).current := by
  rfl

theorem finiteVisit_current_cardinalShadow (depth : Nat) :
    (CanonicalUnitArithmeticRoot.finiteVisit depth).current.cardinalShadow =
      depth + 1 := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change Nat.succ
          (CanonicalUnitArithmeticRoot.finiteVisit depth).current.cardinalShadow =
        depth + 1 + 1
      rw [inductionHypothesis]

@[simp] theorem currentEffectStage_finiteVisit (depth : Nat) :
    currentEffectStage
        (CanonicalUnitArithmeticRoot.finiteVisit depth).current = depth := by
  unfold currentEffectStage
  rw [finiteVisit_current_cardinalShadow]
  omega

@[simp] theorem installedRuntimeEffectValueAt_logNorm
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (installedRuntimeEffectValueAt observation nontrivial depth).logNorm =
      omegaLogNormEffect observation nontrivial depth := by
  rw [installedRuntimeEffectValueAt_eq_current]
  simp [generateRuntimeEffect]

theorem installedRuntimeEffectValueAt_conservation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (installedRuntimeEffectValueAt observation nontrivial depth).phase =
      (installedRuntimeEffectValueAt observation nontrivial depth).retained +
        (installedRuntimeEffectValueAt observation nontrivial depth
          ).centeredTrace := by
  rw [installedRuntimeEffectValueAt_eq_current]
  exact generateRuntimeEffect_conservation observation nontrivial _

def runtimeEffectCausalSuccessorAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeEffectRootedActiveAt observation nontrivial depth
      ).CausalSuccessorAt :=
  (runtimeEffectRootedActiveAt observation nontrivial depth
    ).generatedCausalClosure

theorem runtimeEffectCausalSuccessorAt_targetVisit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeEffectCausalSuccessorAt observation nontrivial depth
      ).successor.targetVisit =
      runtimeEffectVisitAt observation nontrivial (depth + 1) := by
  rfl

/-- The causal successor's target authority is re-indexed to the next
canonical finite visit and its unique compiler row. -/
def runtimeEffectTargetAuthorityAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeEffectRecognition observation nontrivial).CausalEntryAuthorityAt
      (runtimeEffectVisitAt observation nontrivial (depth + 1))
      (rootLedgerEntry
        (runtimeEffectVisitAt observation nontrivial (depth + 1)).current) := by
  let causal := runtimeEffectCausalSuccessorAt observation nontrivial depth
  have visit_eq := runtimeEffectCausalSuccessorAt_targetVisit
    observation nontrivial depth
  cases visit_eq
  have entry_eq := rootLedgerEntry_unique
    (runtimeEffectVisitAt observation nontrivial (depth + 1)).current
    causal.successor.targetEntry
  exact entry_eq ▸ causal.targetAuthority

/-- Direct all-stage q-rich consumer of the compiler-generated installed
effect history. -/
theorem branchNormalizedSeparator_eq_installedRuntimeEffectAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (effectStage qRichStage : Nat)
    (row : CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.FactorRow
      CanonicalUnitArithmeticFactorizationEulerDependentDiagram.seedOccurrence.root
      qRichStage) :
    InverseZeroFibre.branchNormalizedQRichSeparator
        (InverseZeroFibre.mathlibLeftRegressionComponent observation)
        qRichStage row =
      -(CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.quotientCoefficient
          row : ℂ) *
        ((installedRuntimeEffectValueAt observation nontrivial effectStage
          ).logNorm : ℂ) := by
  rw [installedRuntimeEffectValueAt_logNorm]
  exact branchNormalizedSeparator_eq_pairedOmegaRootEffect
    observation nontrivial effectStage qRichStage row

end

end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
