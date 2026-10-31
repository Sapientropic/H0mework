import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.ExitCapacityRenewalRegression
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.UBIPeriodicActualServiceCapacity

/-!
# M14 employment outside-option power geometry

The existing employment action removes the exact work continuation while the
worker actor survives.  At every generated temporal visit, the independent
UBI relation nevertheless has one payment/route/actual-service exit under no
capture and no such exit under full capture.

This is an exact capture counterfactual, not a utility or bargaining-score
oracle.  Payment, purchasing-power standing, employment loss, exit lineage,
receipt families, phase, route compiler, debited run, service compiler, and
actual settlement remain fixed; only the capture compiler changes.

Job Guarantee remains a separate role-conditioned axis: the old employment
role can be empty while UBI exit survives, a new-job standing can survive
while captured UBI is empty, and the two can coexist.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14EmploymentOutsideOptionGeometryRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Renewal Capacity Space CrossingCost
open Settlement Price Money UBI
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open Lifecycle.Universal.FixedAdapter
open M14UBIExitCapacityFixture
open M14ExitCapacityRenewalRegression
open M14UBIPeriodicActualServiceCapacity
open _root_.SaturationMonoid.ProcessGame.Regression.Society.Lifecycle.Universal

/-! ## Exact capture counterfactual -/

@[simp] theorem captured_counterfactual_same_payment :
    capturedProgram.payment = exitCapacityProgram.payment :=
  rfl

@[simp] theorem captured_counterfactual_same_purchasingPowerStanding :
    capturedProgram.purchasingPowerStanding =
      exitCapacityProgram.purchasingPowerStanding :=
  rfl

@[simp] theorem captured_counterfactual_same_employmentLoss :
    capturedProgram.employmentLoss = exitCapacityProgram.employmentLoss :=
  rfl

@[simp] theorem captured_counterfactual_same_exitInterest :
    capturedProgram.exitInterest = exitCapacityProgram.exitInterest :=
  rfl

theorem captured_counterfactual_same_payment_receipt_family
    (depth : Nat) (code : exitRelationCompiler.FutureCode) :
    (capturedGeometryCompilerAt depth).PaysForAt
        capturedProgram.purchasingPowerStanding code =
      (geometryCompilerAt depth).PaysForAt
        exitCapacityProgram.purchasingPowerStanding code :=
  rfl

theorem captured_counterfactual_same_route_receipt_family
    (depth : Nat) (code : exitRelationCompiler.FutureCode)
    (crossing : (crossingCompilerAt depth).ExactCrossing) :
    (capturedGeometryCompilerAt depth).RoutesAt code crossing =
      (geometryCompilerAt depth).RoutesAt code crossing :=
  rfl

/-! ## The outside-option geometry -/

theorem employment_power_removes_work_but_not_worker :
    employmentLoss.power.freedomChange.kind = .lost ∧
      exitRelationCompiler.futureCodesAt employmentRelation .target = ∅ ∧
      worker = targetActor .t0 ∧
      law.SurviveAt (sourceActor .s0) worker ∧
      employmentRelation ≠ independentExitRelation :=
  ⟨employmentLoss.changeKind_eq_lost,
    employment_target_future_empty,
    worker_is_surviving_target_actor.1,
    worker_is_surviving_target_actor.2,
    employment_ne_independentExit⟩

theorem uncaptured_actual_outside_option_at (depth : Nat) :
    Nonempty
      (geometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt :=
  ⟨actionableExitRenewalAt depth⟩

theorem captured_actual_outside_option_is_empty_at (depth : Nat) :
    IsEmpty
      (capturedGeometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt := by
  constructor
  intro renewal
  have positive :
      0 < (capturedGeometryCompilerAt depth).actionableExitCapacity :=
    (capturedGeometryCompilerAt depth)
      |>.capacity_positive_iff_actionableExitRenewal.mpr ⟨renewal⟩
  rw [captured_nominal_capacity_eq_zero_at depth] at positive
  omega

/-- Exact single-axis intervention: all source program data and both receipt
families are preserved, while full capture changes actual outside-option
capacity from one to zero and makes the renewal type empty. -/
theorem price_capture_collapses_the_same_outside_option_at (depth : Nat) :
    capturedProgram.payment = exitCapacityProgram.payment ∧
      capturedProgram.purchasingPowerStanding =
        exitCapacityProgram.purchasingPowerStanding ∧
      capturedProgram.employmentLoss = exitCapacityProgram.employmentLoss ∧
      capturedProgram.exitInterest = exitCapacityProgram.exitInterest ∧
      (∀ code,
        (capturedGeometryCompilerAt depth).PaysForAt
            capturedProgram.purchasingPowerStanding code =
          (geometryCompilerAt depth).PaysForAt
            exitCapacityProgram.purchasingPowerStanding code) ∧
      (∀ code crossing,
        (capturedGeometryCompilerAt depth).RoutesAt code crossing =
          (geometryCompilerAt depth).RoutesAt code crossing) ∧
      (geometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (capturedGeometryCompilerAt depth).actionableExitCapacity = 0 ∧
      Nonempty
        (geometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt ∧
      IsEmpty
        (capturedGeometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt :=
  ⟨captured_counterfactual_same_payment,
    captured_counterfactual_same_purchasingPowerStanding,
    captured_counterfactual_same_employmentLoss,
    captured_counterfactual_same_exitInterest,
    captured_counterfactual_same_payment_receipt_family depth,
    captured_counterfactual_same_route_receipt_family depth,
    actionableExitCapacity_eq_one_at depth,
    captured_nominal_capacity_eq_zero_at depth,
    uncaptured_actual_outside_option_at depth,
    captured_actual_outside_option_is_empty_at depth⟩

/-- Employment power has already removed the role-owned work future, but it
has not removed the worker or the independent, actually serviced exit. -/
theorem employment_loss_with_actionable_outside_option_at (depth : Nat) :
    employmentLoss.power.freedomChange.kind = .lost ∧
      exitRelationCompiler.futureCodesAt employmentRelation .target = ∅ ∧
      law.SurviveAt (sourceActor .s0) worker ∧
      employmentRelation ≠ independentExitRelation ∧
      Nonempty
        (geometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt :=
  ⟨employment_power_removes_work_but_not_worker.1,
    employment_power_removes_work_but_not_worker.2.1,
    employment_power_removes_work_but_not_worker.2.2.2.1,
    employment_power_removes_work_but_not_worker.2.2.2.2,
    uncaptured_actual_outside_option_at depth⟩

/-! ## Job Guarantee is an independent axis -/

theorem outside_option_without_old_employment_role_at (depth : Nat) :
    IsEmpty (JobGuaranteeStandingAt
      (occurrenceOf := Lifecycle.actualEventOccurrenceOf)
      (game := Lifecycle.actualEventGame)
      (core := Lifecycle.Universal.FixedAdapter.core)
      (exitRelationCompiler := exitRelationCompiler)
      worker employmentRelation
      (exitRelationCompiler.roleAt employmentRelation .target)) ∧
      Nonempty
        (geometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt :=
  ⟨jobGuarantee_empty_while_ubi_exit_survives.1,
    uncaptured_actual_outside_option_at depth⟩

theorem new_job_without_captured_outside_option_at (depth : Nat) :
    Nonempty NewJobGuaranteeStanding ∧
      IsEmpty
        (capturedGeometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt :=
  ⟨⟨jobGuaranteeStanding⟩,
    captured_actual_outside_option_is_empty_at depth⟩

theorem outside_option_and_new_job_can_coexist_at (depth : Nat) :
    Nonempty
        (geometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt ∧
      Nonempty NewJobGuaranteeStanding :=
  ⟨uncaptured_actual_outside_option_at depth, ⟨jobGuaranteeStanding⟩⟩

/-- Strong fixed-instance consumer.  It quantifies generated finite visits
only through propositions, so it does not install a completed future table. -/
structure EmploymentOutsideOptionPowerGeometryCertificate : Prop where
  employmentPowerLostWork :
    employmentLoss.power.freedomChange.kind = .lost
  employmentTargetEmpty :
    exitRelationCompiler.futureCodesAt employmentRelation .target = ∅
  workerSurvives : law.SurviveAt (sourceActor .s0) worker
  independentExitLineage : employmentRelation ≠ independentExitRelation
  samePayment : capturedProgram.payment = exitCapacityProgram.payment
  samePurchasingPowerStanding :
    capturedProgram.purchasingPowerStanding =
      exitCapacityProgram.purchasingPowerStanding
  sameEmploymentLoss :
    capturedProgram.employmentLoss = exitCapacityProgram.employmentLoss
  sameExitInterest :
    capturedProgram.exitInterest = exitCapacityProgram.exitInterest
  everyDepthSingleAxisCollapse : ∀ depth : Nat,
    (∀ code,
      (capturedGeometryCompilerAt depth).PaysForAt
          capturedProgram.purchasingPowerStanding code =
        (geometryCompilerAt depth).PaysForAt
          exitCapacityProgram.purchasingPowerStanding code) ∧
    (∀ code crossing,
      (capturedGeometryCompilerAt depth).RoutesAt code crossing =
        (geometryCompilerAt depth).RoutesAt code crossing) ∧
    (geometryCompilerAt depth).actionableExitCapacity = 1 ∧
    (capturedGeometryCompilerAt depth).actionableExitCapacity = 0 ∧
    Nonempty
      (geometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt ∧
    IsEmpty
      (capturedGeometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt
  withoutOldEmploymentRole : ∀ depth : Nat,
    IsEmpty (JobGuaranteeStandingAt
      (occurrenceOf := Lifecycle.actualEventOccurrenceOf)
      (game := Lifecycle.actualEventGame)
      (core := Lifecycle.Universal.FixedAdapter.core)
      (exitRelationCompiler := exitRelationCompiler)
      worker employmentRelation
      (exitRelationCompiler.roleAt employmentRelation .target)) ∧
      Nonempty
        (geometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt
  alternativeNewJob : ∀ depth : Nat,
    Nonempty NewJobGuaranteeStanding ∧
      IsEmpty
        (capturedGeometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt
  coexistence : ∀ depth : Nat,
    Nonempty
        (geometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt ∧
      Nonempty NewJobGuaranteeStanding

theorem employmentOutsideOptionPowerGeometryDirectConsumer :
    EmploymentOutsideOptionPowerGeometryCertificate where
  employmentPowerLostWork :=
    employment_power_removes_work_but_not_worker.1
  employmentTargetEmpty :=
    employment_power_removes_work_but_not_worker.2.1
  workerSurvives :=
    employment_power_removes_work_but_not_worker.2.2.2.1
  independentExitLineage :=
    employment_power_removes_work_but_not_worker.2.2.2.2
  samePayment := captured_counterfactual_same_payment
  samePurchasingPowerStanding :=
    captured_counterfactual_same_purchasingPowerStanding
  sameEmploymentLoss := captured_counterfactual_same_employmentLoss
  sameExitInterest := captured_counterfactual_same_exitInterest
  everyDepthSingleAxisCollapse := fun depth =>
    (price_capture_collapses_the_same_outside_option_at depth).2.2.2.2
  withoutOldEmploymentRole := outside_option_without_old_employment_role_at
  alternativeNewJob := new_job_without_captured_outside_option_at
  coexistence := outside_option_and_new_job_can_coexist_at

end
end M14EmploymentOutsideOptionGeometryRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14EmploymentOutsideOptionGeometryRegression.price_capture_collapses_the_same_outside_option_at
#print axioms SaturationMonoid.ProcessGame.Society.M14EmploymentOutsideOptionGeometryRegression.employmentOutsideOptionPowerGeometryDirectConsumer
