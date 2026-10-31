import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Money.PurchasingPowerStanding
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Power.GeneratedPower
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.ExitCapacityCone

/-!
# UBI as employment-independent exit-capacity renewal

The payment, employment loss, target exit relation, capture classifier, and
surviving continuation below are all dependent on one fixed ProcessGame
occurrence.  The UBI judgement is therefore stronger than a transfer readout:
it requires source-backed purchasing power and an actionable continuation
which remains after an exact employment-power loss and is not swallowed by
the current open-settlement capture fibre.

Job Guarantee is represented separately.  It renews standing through an
actionable code of the employment relation itself; UBI keeps an actionable
code in a distinct generated relation after the employment code is lost.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace UBI

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money Power
open Settlement.SourceOwnedSettlementCompiler

universe u v wa wc x y z q s r e c

variable {Source : Type u} {State : Type v}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {core : SourceOwnedLifecycleCore.{u, v, wa} occurrenceOf game}
variable {V : Vocabulary.{x}}
variable {P : NativeResponsibilityProcess V}
variable {incidence : ActorResponsibilityIncidence core V}
variable
  {exchangeRelationCompiler : SourceOwnedRelationRoleCompiler.{u, v, wa, y}
    occurrenceOf game core.targetFace}
variable
  {exchangeLaw : SourceOwnedExchangeLaw.{u, v, wa, x, y, z}
    core V P incidence exchangeRelationCompiler}
variable
  {settlementCompiler : SourceOwnedSettlementCompiler.{u, v, wa, x, y, z, q}
    exchangeLaw}
variable
  {activationCompiler :
    SourceOwnedResidualConsumerCompiler.{u, v, wa, x, y, z, q, s}
      settlementCompiler}

variable {controllerFace : M0BoundaryFace.{u, v, wc} occurrenceOf}
variable
  {exitRelationCompiler : SourceOwnedRelationRoleCompiler.{u, v, wa, e}
    occurrenceOf game core.targetFace}
variable
  {employmentController : SourceOwnedActionControllerCompiler.{u, v, wc, c}
    game controllerFace}
variable [Zero (exitRelationCompiler.Phase game.source)]

/-- Exact exercise of employment power whose genuine freedom change is the
loss of one generated employment continuation. -/
structure SourceGeneratedEmploymentLossAt
    (employer : employmentController.Actor)
    (worker : exitRelationCompiler.Actor)
    (employment : exitRelationCompiler.GeneratedRelation) : Type (max e c) where
  power : ActionPowerOverAt exitRelationCompiler employmentController
    employer worker employment
  lostCode : exitRelationCompiler.FutureCode
  sourceActionable : ActionableAt exitRelationCompiler.futureIdle
    (exitRelationCompiler.futureCodesAt employment .source) lostCode
  targetAbsent : lostCode ∉
    exitRelationCompiler.futureCodesAt employment .target
  freedomChange_eq : power.freedomChange =
    .lost lostCode sourceActionable targetAbsent

namespace SourceGeneratedEmploymentLossAt

variable {employer : employmentController.Actor}
variable {worker : exitRelationCompiler.Actor}
variable {employment : exitRelationCompiler.GeneratedRelation}

variable (loss : SourceGeneratedEmploymentLossAt
  employer worker employment)

@[simp] theorem changeKind_eq_lost : loss.power.freedomChange.kind = .lost := by
  rw [loss.freedomChange_eq]
  rfl

theorem employment_target_rejects_lostCode :
    loss.lostCode ∉ exitRelationCompiler.futureCodesAt employment .target :=
  loss.targetAbsent

theorem exact_worker_relation_provenance
    (loss : SourceGeneratedEmploymentLossAt employer worker employment) :
    ∃ seed : exitRelationCompiler.ExactRelationSeed,
      (∃ state ∈ game.occurrence.trace,
        state = core.targetFace.state game.source ∧
        exitRelationCompiler.relationSeedAt game.source state seed.1 ∧
        core.targetFace.SeedAt game.source state
          (exitRelationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor exitRelationCompiler = worker ∧
      exitRelationCompiler.relationOf seed = employment := by
  rcases loss with ⟨power, _lostCode, _sourceActionable, _targetAbsent,
    _freedomChange_eq⟩
  exact
    SourceOwnedRelationRoleCompiler.GeneratedInterestAt.exact_state_provenance
      exitRelationCompiler power.constraint.interest

theorem exact_controller_provenance :
    ∃ state ∈ game.occurrence.trace,
      state = employmentController.actionState game.source ∧
        employmentController.actionAdmittedAt loss.power.action.1 :=
  employmentController.controller_provenance loss.power.controller_exact

end SourceGeneratedEmploymentLossAt

/-- All source-generated data needed to ask whether a payment is genuine UBI.

The record contains an actual purchasing-power renewal step, an exact
employment-power loss, and a distinct relation-owned exit cone.  It does not
contain the final UBI/nominal verdict. -/
structure ExitCapacityProgramAt
    (paymentSeed : activationCompiler.ExactActivationSeed)
    {PriceValue : Type r}
    (observer : ExchangePriceObserverAt
      (settlementCompiler := settlementCompiler)
      (paymentSeed.occurrence activationCompiler) PriceValue)
    (employer : employmentController.Actor)
    (worker : exitRelationCompiler.Actor)
    (employment exitRelation : exitRelationCompiler.GeneratedRelation)
    (capture : SourceOwnedPriceCaptureCompilerAt exitRelationCompiler
      (OpenSettlementAt settlementCompiler
        (paymentSeed.occurrence activationCompiler))
      (exactOpenSettlement paymentSeed)) : Type (max x z e c r) where
  private mk ::
  payment : PurchasingPowerRenewalStepAt paymentSeed observer
  employmentLoss : SourceGeneratedEmploymentLossAt
    employer worker employment
  exitInterest : exitRelationCompiler.GeneratedInterestAt worker exitRelation
  employment_ne_exitRelation : employment ≠ exitRelation

namespace ExitCapacityProgramAt

variable {paymentSeed : activationCompiler.ExactActivationSeed}
variable {PriceValue : Type r}
variable {observer : ExchangePriceObserverAt
  (settlementCompiler := settlementCompiler)
  (paymentSeed.occurrence activationCompiler) PriceValue}
variable {employer : employmentController.Actor}
variable {worker : exitRelationCompiler.Actor}
variable {employment exitRelation : exitRelationCompiler.GeneratedRelation}
variable {capture : SourceOwnedPriceCaptureCompilerAt exitRelationCompiler
  (OpenSettlementAt settlementCompiler
    (paymentSeed.occurrence activationCompiler))
  (exactOpenSettlement paymentSeed)}

/-- The program is generated before the final UBI/nominal classification. -/
def generate
    (payment : PurchasingPowerRenewalStepAt paymentSeed observer)
    (employmentLoss : SourceGeneratedEmploymentLossAt
      employer worker employment)
    (exitInterest :
      exitRelationCompiler.GeneratedInterestAt worker exitRelation)
    (employment_ne_exitRelation : employment ≠ exitRelation) :
    ExitCapacityProgramAt paymentSeed observer employer worker employment
      exitRelation capture :=
  ⟨payment, employmentLoss, exitInterest, employment_ne_exitRelation⟩

variable (program : ExitCapacityProgramAt paymentSeed observer employer worker
  employment exitRelation capture)

/-- The source-backed purchasing-power standing carried by the current
renewal occurrence. -/
def purchasingPowerStanding : PurchasingPowerStandingAt paymentSeed observer :=
  program.payment.standing

def exitCone : CaptureAdjustedExitConeAt exitRelationCompiler worker
    exitRelation capture :=
  CaptureAdjustedExitConeAt.generate program.exitInterest

theorem payment_event_mem_source_trace :
    ∃ state ∈ game.occurrence.trace,
      activationCompiler.activationSeedAt game.source state
        (PurchasingPowerStandingAt.renewalEvent
          program.purchasingPowerStanding) :=
  PurchasingPowerStandingAt.event_mem_source_trace
    program.purchasingPowerStanding

theorem payment_next_is_exact_generated :
    program.payment.nextGenerated =
      PurchasingPowerStandingAt.nextGeneratedState
        program.purchasingPowerStanding :=
  program.payment.next_eq

end ExitCapacityProgramAt

/-- Strong UBI verdict: the exact payment program has at least one surviving
target-side actionable exit. -/
structure ExitCapacityRenewalAt
    {paymentSeed : activationCompiler.ExactActivationSeed}
    {PriceValue : Type r}
    {observer : ExchangePriceObserverAt
      (settlementCompiler := settlementCompiler)
      (paymentSeed.occurrence activationCompiler) PriceValue}
    {employer : employmentController.Actor}
    {worker : exitRelationCompiler.Actor}
    {employment exitRelation : exitRelationCompiler.GeneratedRelation}
    {capture : SourceOwnedPriceCaptureCompilerAt exitRelationCompiler
      (OpenSettlementAt settlementCompiler
        (paymentSeed.occurrence activationCompiler))
      (exactOpenSettlement paymentSeed)}
    (program : ExitCapacityProgramAt paymentSeed observer employer worker
      employment exitRelation capture) : Type e where
  private mk ::
  exit : program.exitCone.ActionableExitAt

namespace ExitCapacityRenewalAt

variable {paymentSeed : activationCompiler.ExactActivationSeed}
variable {PriceValue : Type r}
variable {observer : ExchangePriceObserverAt
  (settlementCompiler := settlementCompiler)
  (paymentSeed.occurrence activationCompiler) PriceValue}
variable {employer : employmentController.Actor}
variable {worker : exitRelationCompiler.Actor}
variable {employment exitRelation : exitRelationCompiler.GeneratedRelation}
variable {capture : SourceOwnedPriceCaptureCompilerAt exitRelationCompiler
  (OpenSettlementAt settlementCompiler
    (paymentSeed.occurrence activationCompiler))
  (exactOpenSettlement paymentSeed)}
variable {program : ExitCapacityProgramAt paymentSeed observer employer worker
  employment exitRelation capture}

def generate (exit : program.exitCone.ActionableExitAt) :
    ExitCapacityRenewalAt program :=
  ⟨exit⟩

/-- Strong iff: the final verdict exists exactly when a source-generated,
non-idle target continuation survives the exact settlement capture fibre.
Source-backed payment, employment loss, and relation independence are not
premises here: they are already immutable indices of `program`. -/
theorem nonempty_iff_sourceGeneratedUncapturedContinuation :
    Nonempty (ExitCapacityRenewalAt program) ↔
      ∃ code,
        code ∈ exitRelationCompiler.futureCodeCarrier ∧
        Nonempty (exitRelationCompiler.FutureContinuationAt
          exitRelation.1 .target code) ∧
        ¬ exitRelationCompiler.futureIdle code ∧
        ¬ capture.Captures code := by
  constructor
  · rintro ⟨renewal⟩
    exact program.exitCone.actionableExit_nonempty_iff.mp ⟨renewal.exit⟩
  · intro surviving
    rcases program.exitCone.actionableExit_nonempty_iff.mpr surviving with
      ⟨exit⟩
    exact ⟨generate exit⟩

theorem preserves_actionable_continuation_after_employment_loss
    (renewal : ExitCapacityRenewalAt program) :
    program.employmentLoss.lostCode ∉
        exitRelationCompiler.futureCodesAt employment .target ∧
      Nonempty (exitRelationCompiler.FutureContinuationAt
        exitRelation.1 .target renewal.exit.1) ∧
      ¬ exitRelationCompiler.futureIdle renewal.exit.1 ∧
      ¬ capture.Captures renewal.exit.1 := by
  have generated :=
    (SourceOwnedPriceCaptureCompilerAt.mem_survivingExitCodes_iff
      capture exitRelation renewal.exit.1).mp renewal.exit.2
  exact ⟨program.employmentLoss.targetAbsent,
    generated.2.1, generated.2.2.1, generated.2.2.2⟩

end ExitCapacityRenewalAt

/-- A nominal transfer is an actual source-backed payment whose distinct
exit relation has been completely captured.  The word "nominal" therefore
does not mean fake payment; it means that the payment fails to generate an
actionable outside option. -/
structure NominalTransferReadoutAt
    {paymentSeed : activationCompiler.ExactActivationSeed}
    {PriceValue : Type r}
    {observer : ExchangePriceObserverAt
      (settlementCompiler := settlementCompiler)
      (paymentSeed.occurrence activationCompiler) PriceValue}
    {employer : employmentController.Actor}
    {worker : exitRelationCompiler.Actor}
    {employment exitRelation : exitRelationCompiler.GeneratedRelation}
    {capture : SourceOwnedPriceCaptureCompilerAt exitRelationCompiler
      (OpenSettlementAt settlementCompiler
        (paymentSeed.occurrence activationCompiler))
      (exactOpenSettlement paymentSeed)}
    (program : ExitCapacityProgramAt paymentSeed observer employer worker
      employment exitRelation capture) : Prop where
  private mk ::
  fullCapture : program.exitCone.FullPriceCaptureAt

namespace NominalTransferReadoutAt

variable {paymentSeed : activationCompiler.ExactActivationSeed}
variable {PriceValue : Type r}
variable {observer : ExchangePriceObserverAt
  (settlementCompiler := settlementCompiler)
  (paymentSeed.occurrence activationCompiler) PriceValue}
variable {employer : employmentController.Actor}
variable {worker : exitRelationCompiler.Actor}
variable {employment exitRelation : exitRelationCompiler.GeneratedRelation}
variable {capture : SourceOwnedPriceCaptureCompilerAt exitRelationCompiler
  (OpenSettlementAt settlementCompiler
    (paymentSeed.occurrence activationCompiler))
  (exactOpenSettlement paymentSeed)}
variable {program : ExitCapacityProgramAt paymentSeed observer employer worker
  employment exitRelation capture}

theorem generate (fullCapture : program.exitCone.FullPriceCaptureAt) :
    NominalTransferReadoutAt program :=
  ⟨fullCapture⟩

theorem excludes_exitCapacityRenewal
    (nominal : NominalTransferReadoutAt program) :
    IsEmpty (ExitCapacityRenewalAt program) := by
  have noExit : IsEmpty program.exitCone.ActionableExitAt :=
    program.exitCone.isEmpty_actionableExit_iff_fullPriceCapture.mpr
      nominal.fullCapture
  exact ⟨fun renewal => noExit.false renewal.exit⟩

end NominalTransferReadoutAt

/-- The actual source program has a total, mutually exclusive disposition:
either an uncaptured actionable exit exists, or the exact payment is only a
nominal transfer readout. -/
theorem exitCapacityRenewal_or_nominalTransfer
    {paymentSeed : activationCompiler.ExactActivationSeed}
    {PriceValue : Type r}
    {observer : ExchangePriceObserverAt
      (settlementCompiler := settlementCompiler)
      (paymentSeed.occurrence activationCompiler) PriceValue}
    {employer : employmentController.Actor}
    {worker : exitRelationCompiler.Actor}
    {employment exitRelation : exitRelationCompiler.GeneratedRelation}
    {capture : SourceOwnedPriceCaptureCompilerAt exitRelationCompiler
      (OpenSettlementAt settlementCompiler
        (paymentSeed.occurrence activationCompiler))
      (exactOpenSettlement paymentSeed)}
    (program : ExitCapacityProgramAt paymentSeed observer employer worker
      employment exitRelation capture) :
    Nonempty (ExitCapacityRenewalAt program) ∨
      Nonempty (NominalTransferReadoutAt program) := by
  classical
  by_cases survives : Nonempty program.exitCone.ActionableExitAt
  · exact Or.inl ⟨ExitCapacityRenewalAt.generate (Classical.choice survives)⟩
  · have noExit : IsEmpty program.exitCone.ActionableExitAt :=
      ⟨fun exit => survives ⟨exit⟩⟩
    have fullCapture :=
      program.exitCone.isEmpty_actionableExit_iff_fullPriceCapture.mp noExit
    exact Or.inr ⟨NominalTransferReadoutAt.generate fullCapture⟩

/-! ## Job Guarantee separation -/

/-- Job Guarantee renews standing through the employment relation itself:
it requires an exact target role and an actionable target employment code. -/
structure JobGuaranteeStandingAt
    (worker : exitRelationCompiler.Actor)
    (employment : exitRelationCompiler.GeneratedRelation)
    (role : exitRelationCompiler.Role game.source) : Type e where
  roleAuthority : exitRelationCompiler.RelationRoleAt
    worker employment .target role
  workCode : exitRelationCompiler.FutureCode
  workActionable : ActionableAt exitRelationCompiler.futureIdle
    (exitRelationCompiler.futureCodesAt employment .target) workCode

omit [Zero (exitRelationCompiler.Phase game.source)] in
/-- If employment has no target continuation, role-conditioned Job Guarantee
standing is impossible.  A distinct UBI exit relation may remain inhabited. -/
theorem noEmploymentTargetFuture_noJobGuarantee
    (worker : exitRelationCompiler.Actor)
    (employment : exitRelationCompiler.GeneratedRelation)
    (role : exitRelationCompiler.Role game.source)
    (empty : exitRelationCompiler.futureCodesAt employment .target = ∅) :
    IsEmpty (JobGuaranteeStandingAt worker employment role) :=
  ⟨fun standing => by
    have member := standing.workActionable.1
    rw [empty] at member
    simp at member⟩

end UBI
end Society
end ProcessGame
end SaturationMonoid
