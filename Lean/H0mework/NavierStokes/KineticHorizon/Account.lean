import H0mework.NavierStokes.WholeReceipt.KineticDecay
import H0mework.NavierStokes.ClockAccount.FullKineticResolution

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.KineticSelectionHorizon

open Set
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock

noncomputable section

def contactKinetic (stage : Nat) : Real :=
  puncturedWholeVorticityKineticMass (run concreteCounterexampleInitial stage).contact.physicalState

def rawKinetic : Real := puncturedWholeVorticityKineticMass concreteCounterexampleInitial.initialState

def decayRate : Real := 2 * concreteCounterexampleViscosity.coeff * (2 * Real.pi) ^ 2

theorem decayRate_pos : 0 < decayRate := by
  unfold decayRate
  exact mul_pos (mul_pos (by norm_num) concreteCounterexampleViscosity.coeff_pos) (by positivity)

theorem contactKinetic_nonneg (stage : Nat) : 0 ≤ contactKinetic stage :=
  puncturedWholeVorticityKineticMass_nonneg _

theorem rawKinetic_nonneg : 0 ≤ rawKinetic := puncturedWholeVorticityKineticMass_nonneg _

theorem contactKinetic_le_exp (stage : Nat) : contactKinetic stage ≤
    rawKinetic * Real.exp (-decayRate * elapsedTime concreteCounterexampleInitial (stage + 1)) := by
  let terminal : Icc (0 : Real) (WholePrefixState.duration concreteCounterexampleInitial stage) :=
    ⟨_, (WholePrefixState.duration_pos concreteCounterexampleInitial stage).le, le_rfl⟩
  have source := WholeKineticDecay.fixed_prefix_kinetic_le_exp stage terminal
  have endpoint : (WholePrefixReceipt.receipt concreteCounterexampleInitial stage).wholePath terminal =
      (run concreteCounterexampleInitial stage).contact.physicalState := by
    rw [WholePrefixReceipt.receipt_path]
    exact (wholeRestartPrefixPhysicalTrajectory_endpoint concreteCounterexampleInitial (stage + 1)).trans
      (run_succ_initialState concreteCounterexampleInitial stage)
  rw [endpoint] at source
  simpa only [contactKinetic, rawKinetic, decayRate, neg_mul, terminal, WholePrefixState.duration] using source

theorem nextContact_time_le_one (stage : Nat) :
    (run concreteCounterexampleInitial (stage + 1)).contact.time.1 ≤ 1 := by
  change (run concreteCounterexampleInitial stage).nextContact.time.1 ≤ 1
  exact (run concreteCounterexampleInitial stage).nextContact.time.2.2.trans
    (wholeRestartDuration_lt_one (run concreteCounterexampleInitial stage)).le

/-- The same paid kinetic reserve and elapsed physical time form one decreasing account. -/
def account (stage : Nat) : Real := elapsedTime concreteCounterexampleInitial (stage + 1) +
  contactKinetic stage / SelectionHorizon.paymentRate

theorem elapsed_le_account (stage : Nat) : elapsedTime concreteCounterexampleInitial (stage + 1) ≤ account stage := by
  exact le_add_of_nonneg_right (div_nonneg (contactKinetic_nonneg stage) SelectionHorizon.paymentRate_pos.le)

theorem account_antitone
    (bounded : BddAbove (range (elapsedTime concreteCounterexampleInitial))) : Antitone account := by
  apply antitone_nat_of_succ_le
  intro stage
  have high : WindowMassCoefficient.halfCriticalMass < wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial (stage + 1)).contact.physicalState :=
    lt_of_not_ge fun low => SmallBranch.lowContact_originalRun_unbounded (stage + 1) low bounded
  have payment := SelectionHorizon.contact_time_le_payment_of_high stage high
  have ledger := run_contact_kineticDissipation_succ_le concreteCounterexampleInitial stage
  have total : (run concreteCounterexampleInitial stage).nextContact.time.1 * SelectionHorizon.paymentRate +
      contactKinetic (stage + 1) ≤ contactKinetic stage := by
    change _ ≤ puncturedWholeVorticityKineticMass (run concreteCounterexampleInitial stage).contact.physicalState
    change _ + wholeRestartNextKineticDissipationPayment concreteCounterexampleInitial stage ≤ _ at ledger
    dsimp only [contactKinetic]
    linarith
  have clock : (run concreteCounterexampleInitial stage).nextContact.time.1 +
      contactKinetic (stage + 1) / SelectionHorizon.paymentRate ≤ contactKinetic stage / SelectionHorizon.paymentRate := by
    apply (le_div_iff₀ SelectionHorizon.paymentRate_pos).mpr
    rw [add_mul, div_mul_cancel₀ _ SelectionHorizon.paymentRate_pos.ne']
    exact total
  unfold account
  rw [elapsedTime_succ concreteCounterexampleInitial (stage + 1)]
  change _ + (run concreteCounterexampleInitial stage).nextContact.time.1 + _ ≤ _
  linarith

end
end SaturationMonoid.NavierStokes.KineticSelectionHorizon
