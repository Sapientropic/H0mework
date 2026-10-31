import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.EmploymentIndependentExit
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.RootInstallation.MoneyRootInstallationRegression

/-!
# M14 UBI exit-capacity fixture

One existing M3 purchasing-power renewal and one fixed M1 occurrence generate
two distinct relation lineages: employment and role-independent exit.  The
actual controller removes the sole employment continuation.  The uncaptured
fixture preserves a target exit; the captured fixture points the same code to
the exact open settlement and removes all exit capacity.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14UBIExitCapacityFixture

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Lifecycle.Universal.FixedAdapter
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M8MoneyRootInstallationRegression
open M8PurchasingPowerStandingRegression

inductive ExitRelationSeed where
  | employment
  | independentExit
  | newJob
  deriving DecidableEq, Repr

inductive ExitRole where
  | employed
  | released
  | independent
  deriving DecidableEq, Repr

inductive ExitFutureCode where
  | idle
  | work
  | leave
  deriving DecidableEq, Repr

def exitRelationSeedAt (_source : Unit) (state : Lifecycle.EventState)
    (_seed : ExitRelationSeed) : Prop :=
  state = .after

def exitRelationCompiler : SourceOwnedRelationRoleCompiler
    Lifecycle.actualEventOccurrenceOf Lifecycle.actualEventGame targetFace where
  RelationSeed := ExitRelationSeed
  RelationLineage := fun _ => ExitRelationSeed
  relationSeedAt := exitRelationSeedAt
  relationLineageOf := fun _ seed => seed.1
  beneficiaryActorSeed := fun _ => .t0
  beneficiaryActor_active := by
    intro _source _state _seed admitted
    exact admitted
  Role := fun _ => ExitRole
  Phase := fun _ => Int
  sourceRoleOf := fun _ lineage =>
    match lineage with
    | .employment => .employed
    | .independentExit => .independent
    | .newJob => .employed
  phaseStepOf := fun _ lineage =>
    match lineage with
    | .employment => 1
    | .independentExit => 0
    | .newJob => 0
  advanceRole := fun _ phase role =>
    if phase = 0 then role else .released
  FutureCode := ExitFutureCode
  futureCodeDecidableEq := inferInstance
  futureCodeCarrier := {.idle, .work, .leave}
  futureIdle := fun code => code = .idle
  FutureContinuationAt := fun lineage side code =>
    match lineage, side, code with
    | .employment, .source, .work => PUnit
    | .independentExit, .target, .leave => PUnit
    | .newJob, .target, .work => PUnit
    | _, _, _ => PEmpty
  futureBoundaryState := fun _ side =>
    match side with
    | .source => .before
    | .target => .after
  futureBoundaryState_mem := by
    intro _lineage side
    cases side <;>
      change _ ∈ [Lifecycle.EventState.before, Lifecycle.EventState.after] <;>
      simp
  FutureContinuationWitnessAt := fun _ _ _ _ => True
  futureContinuation_witnessed := by
    intro _ _ _ _
    trivial

def exactRelationSeed (seed : ExitRelationSeed) :
    exitRelationCompiler.ExactRelationSeed :=
  ⟨seed, .after, by
    change Lifecycle.EventState.after ∈
      [Lifecycle.EventState.before, Lifecycle.EventState.after]
    simp, rfl⟩

def worker : exitRelationCompiler.Actor :=
  (exactRelationSeed .employment).actor exitRelationCompiler

def employmentRelation : exitRelationCompiler.GeneratedRelation :=
  exitRelationCompiler.relationOf (exactRelationSeed .employment)

def independentExitRelation : exitRelationCompiler.GeneratedRelation :=
  exitRelationCompiler.relationOf (exactRelationSeed .independentExit)

def newJobRelation : exitRelationCompiler.GeneratedRelation :=
  exitRelationCompiler.relationOf (exactRelationSeed .newJob)

theorem employmentInterest :
    exitRelationCompiler.GeneratedInterestAt worker employmentRelation :=
  ⟨exactRelationSeed .employment, rfl, rfl⟩

theorem independentExitInterest :
    exitRelationCompiler.GeneratedInterestAt worker independentExitRelation :=
  ⟨exactRelationSeed .independentExit, rfl, rfl⟩

theorem newJobInterest :
    exitRelationCompiler.GeneratedInterestAt worker newJobRelation := by
  refine ⟨exactRelationSeed .newJob, ?_, rfl⟩
  apply Subtype.ext
  rfl

theorem employment_ne_independentExit :
    employmentRelation ≠ independentExitRelation := by
  intro equality
  have lineage_eq := congrArg Subtype.val equality
  exact ExitRelationSeed.noConfusion lineage_eq

inductive EmploymentActionSeed where
  | terminate
  deriving DecidableEq, Repr

def employmentController : SourceOwnedActionControllerCompiler
    Lifecycle.actualEventGame targetFace where
  ActionSeed := EmploymentActionSeed
  actionAdmittedAt := fun _ => True
  actionState := fun _ => .after
  actionState_mem := by
    change Lifecycle.EventState.after ∈
      [Lifecycle.EventState.before, Lifecycle.EventState.after]
    simp
  actorState_mem := by
    change Lifecycle.EventState.after ∈
      [Lifecycle.EventState.before, Lifecycle.EventState.after]
    simp
  actorSeed := fun _ => .t1
  actorSeed_active := by
    intro _action _admitted
    rfl

def exactEmploymentAction : employmentController.ExactActionSeed :=
  ⟨.terminate, .after, by
    change Lifecycle.EventState.after ∈
      [Lifecycle.EventState.before, Lifecycle.EventState.after]
    simp, rfl, trivial⟩

def employer : employmentController.Actor :=
  exactEmploymentAction.actor employmentController

instance exitRelationPhaseZero :
    Zero (exitRelationCompiler.Phase Lifecycle.actualEventGame.source) := by
  change Zero Int
  infer_instance

local instance exitFutureCodeDecidableEq :
    DecidableEq exitRelationCompiler.FutureCode :=
  exitRelationCompiler.futureCodeDecidableEq

theorem work_source_actionable :
    ActionableAt exitRelationCompiler.futureIdle
      (exitRelationCompiler.futureCodesAt employmentRelation .source)
      .work := by
  constructor
  · apply
    (exitRelationCompiler.mem_futureCodesAt_iff employmentRelation .source
        .work).mpr
    exact ⟨by
      change ExitFutureCode.work ∈
        ({.idle, .work, .leave} : Finset ExitFutureCode)
      simp, ⟨PUnit.unit⟩⟩
  · simp [exitRelationCompiler]

theorem work_target_absent :
    ExitFutureCode.work ∉
      exitRelationCompiler.futureCodesAt employmentRelation .target := by
  intro member
  have generated :=
    (exitRelationCompiler.mem_futureCodesAt_iff employmentRelation .target
      .work).mp member
  exact nomatch Classical.choice generated.2

def employmentFreedomLoss : ActionableFreedomChange
    exitRelationCompiler.futureIdle
    (exitRelationCompiler.futureCodesAt employmentRelation .source)
    (exitRelationCompiler.futureCodesAt employmentRelation .target) :=
  .lost .work work_source_actionable work_target_absent

def employmentActionPower : ActionPowerOverAt exitRelationCompiler
    employmentController employer worker employmentRelation where
  action := exactEmploymentAction
  controller_exact := rfl
  constraint := ⟨employmentInterest, by
    change (1 : Int) ≠ 0
    norm_num⟩
  freedomChange := employmentFreedomLoss

def employmentLoss : SourceGeneratedEmploymentLossAt
    (occurrenceOf := Lifecycle.actualEventOccurrenceOf)
    (game := Lifecycle.actualEventGame)
    (core := Lifecycle.Universal.FixedAdapter.core)
    (controllerFace := Lifecycle.Universal.FixedAdapter.targetFace)
    (exitRelationCompiler := exitRelationCompiler)
    (employmentController := employmentController)
    employer worker employmentRelation where
  power := employmentActionPower
  lostCode := .work
  sourceActionable := work_source_actionable
  targetAbsent := work_target_absent
  freedomChange_eq := rfl

theorem leave_target_actionable :
    ActionableAt exitRelationCompiler.futureIdle
      (exitRelationCompiler.futureCodesAt independentExitRelation .target)
      .leave := by
  constructor
  · apply
    (exitRelationCompiler.mem_futureCodesAt_iff independentExitRelation
        .target .leave).mpr
    exact ⟨by
      change ExitFutureCode.leave ∈
        ({.idle, .work, .leave} : Finset ExitFutureCode)
      simp, ⟨PUnit.unit⟩⟩
  · simp [exitRelationCompiler]

theorem newJob_work_target_actionable :
    ActionableAt exitRelationCompiler.futureIdle
      (exitRelationCompiler.futureCodesAt newJobRelation .target)
      .work := by
  constructor
  · apply
      (exitRelationCompiler.mem_futureCodesAt_iff newJobRelation .target
        .work).mpr
    exact ⟨by
      change ExitFutureCode.work ∈
        ({.idle, .work, .leave} : Finset ExitFutureCode)
      simp, ⟨PUnit.unit⟩⟩
  · simp [exitRelationCompiler]

abbrev NewJobGuaranteeStanding := JobGuaranteeStandingAt
    (occurrenceOf := Lifecycle.actualEventOccurrenceOf)
    (game := Lifecycle.actualEventGame)
    (core := Lifecycle.Universal.FixedAdapter.core)
    (exitRelationCompiler := exitRelationCompiler)
    worker newJobRelation
      (exitRelationCompiler.roleAt newJobRelation .target)

def jobGuaranteeStanding : NewJobGuaranteeStanding where
  roleAuthority := ⟨newJobInterest, rfl⟩
  workCode := .work
  workActionable := newJob_work_target_actionable

def noCapture : SourceOwnedPriceCaptureCompilerAt exitRelationCompiler
    (OpenSettlementAt settlementCompiler openOccurrence)
    (exactOpenSettlement exactResidualActivation) where
  Captures := fun _ => False
  capturesDecidable := fun _ => inferInstance
  captureSettlement := fun _ captured => nomatch captured
  captureSettlement_eq := fun _ captured => nomatch captured

def fullCapture : SourceOwnedPriceCaptureCompilerAt exitRelationCompiler
    (OpenSettlementAt settlementCompiler openOccurrence)
    (exactOpenSettlement exactResidualActivation) where
  Captures := fun code => code = .leave
  capturesDecidable := fun code =>
    exitFutureCodeDecidableEq code ExitFutureCode.leave
  captureSettlement := fun _ _ => exactOpenSettlement exactResidualActivation
  captureSettlement_eq := fun _ _ => rfl

def exitCapacityProgram : ExitCapacityProgramAt exactResidualActivation
    (rootPriceObserver exactResidualActivation) employer worker
    employmentRelation independentExitRelation noCapture :=
  ExitCapacityProgramAt.generate rootPurchasingPowerStep employmentLoss
    independentExitInterest employment_ne_independentExit

def capturedProgram : ExitCapacityProgramAt exactResidualActivation
    (rootPriceObserver exactResidualActivation) employer worker
    employmentRelation independentExitRelation fullCapture :=
  ExitCapacityProgramAt.generate rootPurchasingPowerStep employmentLoss
    independentExitInterest employment_ne_independentExit

def actionableExit : exitCapacityProgram.exitCone.ActionableExitAt :=
  ⟨.leave,
    (SourceOwnedPriceCaptureCompilerAt.mem_survivingExitCodes_iff
      noCapture independentExitRelation .leave).mpr
      ⟨by
        change ExitFutureCode.leave ∈
          ({.idle, .work, .leave} : Finset ExitFutureCode)
        simp, ⟨PUnit.unit⟩,
        by simp [exitRelationCompiler], by simp [noCapture]⟩⟩

def exitCapacityRenewal : ExitCapacityRenewalAt exitCapacityProgram :=
  ExitCapacityRenewalAt.generate actionableExit

theorem capturedProgram_fullPriceCapture :
    capturedProgram.exitCone.FullPriceCaptureAt := by
  intro code actionable
  have generated :=
    (exitRelationCompiler.mem_futureCodesAt_iff independentExitRelation
      .target code).mp actionable.1
  cases code with
  | idle => exact False.elim (actionable.2 rfl)
  | work => exact nomatch Classical.choice generated.2
  | leave => rfl

theorem nominalTransfer : NominalTransferReadoutAt capturedProgram :=
  NominalTransferReadoutAt.generate capturedProgram_fullPriceCapture

theorem employment_target_future_empty :
    exitRelationCompiler.futureCodesAt employmentRelation .target = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro code member
  have generated :=
    (exitRelationCompiler.mem_futureCodesAt_iff employmentRelation .target
      code).mp member
  exact nomatch Classical.choice generated.2

end
end M14UBIExitCapacityFixture
end Society
end ProcessGame
end SaturationMonoid
