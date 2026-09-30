import H0mework.Versions.X.NavierStokes.ClockAccount.FullSmallBranch

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SelectionHorizon

open scoped BigOperators
open Set
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientWholeRestartBlockKineticLedger
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCompleteSerrinLanding
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open WindowMassCoefficient

noncomputable section

def paymentRate : Real := concreteCounterexampleViscosity.coeff * halfCriticalMass

theorem paymentRate_pos : 0 < paymentRate := by
  unfold paymentRate halfCriticalMass
  exact mul_pos concreteCounterexampleViscosity.coeff_pos
    (div_pos (mul_pos (sq_pos_of_pos RationalVorticityEvaluator.butterflyGainViscosity.coeff_pos)
      (by positivity))
      (mul_pos (by norm_num) criticalEnstrophyLatticeConstant_pos))

/-- A fixed physical horizon computed from the original contact's kinetic reserve. -/
def sourceHorizon : Real := concreteCounterexampleInitial.contact.time.1 +
  puncturedWholeVorticityKineticMass concreteCounterexampleInitial.contact.physicalState /
    paymentRate

theorem sourceHorizon_nonneg : 0 ≤ sourceHorizon :=
  add_nonneg concreteCounterexampleInitial.contact.time_pos.le
    (div_nonneg (puncturedWholeVorticityKineticMass_nonneg _) paymentRate_pos.le)

theorem contact_time_le_payment_of_high
    (stage : Nat)
    (high : halfCriticalMass < wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial (stage + 1)).contact.physicalState) :
    (run concreteCounterexampleInitial stage).nextContact.time.1 * paymentRate ≤
      wholeRestartNextKineticDissipationPayment concreteCounterexampleInitial stage := by
  let current := run concreteCounterexampleInitial stage
  have rectangle := LowMassBranch.nextContact_terminalMass_rectangle current
  have terminalHigh : halfCriticalMass < wholeVorticityEuclideanMass
      current.nextContact.physicalState := by
    change halfCriticalMass < wholeVorticityEuclideanMass
      current.nextContact.physicalState at high
    exact high
  have errorLe := epsilon_le_halfCriticalMass_half
  change wholeRestartCubicFourthCoefficient concreteCounterexampleViscosity /
    concreteCounterexampleViscosity.coeff ≤ halfCriticalMass / 2 at errorLe
  have density : current.nextContact.time.1 * (halfCriticalMass / 2) ≤
      wholePrefixVorticityMass current.nextContact.time current.nextReceipt.stateLimit := by
    apply le_trans _ rectangle
    apply mul_le_mul_of_nonneg_left _ current.nextContact.time_pos.le
    linarith
  have scaled := mul_le_mul_of_nonneg_left density
    (mul_nonneg (by norm_num : (0 : Real) ≤ 2) concreteCounterexampleViscosity.coeff_pos.le)
  change current.nextContact.time.1 * paymentRate ≤
    2 * concreteCounterexampleViscosity.coeff *
      wholePrefixVorticityMass current.nextContact.time current.nextReceipt.stateLimit
  unfold paymentRate
  nlinarith [scaled]

/-- A finite prefix that has not entered the absorbing region spends only its
original kinetic reserve. No condition on future contacts enters this bound. -/
theorem elapsed_le_horizon_of_prefix_high
    (length : Nat)
    (high : ∀ stage < length, halfCriticalMass < wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial (stage + 1)).contact.physicalState) :
    elapsedTime concreteCounterexampleInitial (length + 1) ≤ sourceHorizon := by
  have summed := Finset.sum_le_sum fun stage (mem : stage ∈ Finset.range length) =>
    contact_time_le_payment_of_high stage (high stage (Finset.mem_range.mp mem))
  rw [← Finset.sum_mul] at summed
  change wholeRestartSelectedPrefixTimeSum concreteCounterexampleInitial length * paymentRate ≤
    wholeRestartAccumulatedKineticDissipationPayment concreteCounterexampleInitial length at summed
  have bound := summed.trans
    (wholeRestartAccumulatedKineticDissipationPayment_le_initial concreteCounterexampleInitial length)
  have divided := (le_div_iff₀ paymentRate_pos).mpr bound
  rw [wholeRestartSelectedPrefixTimeSum_eq_elapsedTime_sub_initial] at divided
  unfold sourceHorizon
  linarith

/-- Crossing the source-computed horizon supplies a finite original low contact. -/
theorem beyond_horizon_generates_lowContact
    (length : Nat)
    (beyond : sourceHorizon < elapsedTime concreteCounterexampleInitial (length + 1)) :
    ∃ stage < length, wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial (stage + 1)).contact.physicalState ≤ halfCriticalMass := by
  by_contra none
  have high : ∀ stage < length, halfCriticalMass < wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial (stage + 1)).contact.physicalState := by
    intro stage before
    exact lt_of_not_ge fun low => none ⟨stage, before, low⟩
  exact (not_lt_of_ge (elapsed_le_horizon_of_prefix_high length high)) beyond

/-- Every finite-time accumulation occurs before the same explicit horizon. -/
theorem bounded_elapsed_le_horizon
    (bounded : BddAbove (range (elapsedTime concreteCounterexampleInitial)))
    (length : Nat) : elapsedTime concreteCounterexampleInitial length ≤ sourceHorizon := by
  cases length with
  | zero => exact sourceHorizon_nonneg
  | succ length =>
      apply elapsed_le_horizon_of_prefix_high length
      intro stage _before
      exact lt_of_not_ge fun low =>
        SmallBranch.lowContact_originalRun_unbounded (stage + 1) low bounded

/-- The old branch has a finite witness beyond a source-computed time, so
its selection needs no completed future recurrence table. -/
theorem unbounded_iff_beyond_horizon :
    (¬ BddAbove (range (elapsedTime concreteCounterexampleInitial))) ↔
      ∃ length : Nat, sourceHorizon < elapsedTime concreteCounterexampleInitial length := by
  constructor
  · intro unbounded
    rcases not_bddAbove_iff.mp unbounded sourceHorizon with ⟨time, ⟨length, rfl⟩, after⟩
    exact ⟨length, after⟩
  · rintro ⟨length, after⟩ bounded
    exact (not_lt_of_ge (bounded_elapsed_le_horizon bounded length)) after

theorem bounded_iff_all_elapsed_le_horizon :
    BddAbove (range (elapsedTime concreteCounterexampleInitial)) ↔
      ∀ length : Nat, elapsedTime concreteCounterexampleInitial length ≤ sourceHorizon := by
  constructor
  · exact bounded_elapsed_le_horizon
  · intro bounded
    exact ⟨sourceHorizon, fun _time ⟨length, equality⟩ => equality ▸ bounded length⟩

/-- One standard receipt beyond the explicit kinetic horizon selects the old
global branch. The requested horizon is computed before any boundary answer. -/
theorem receipt_beyond_horizon_forces_unbounded
    (receipt : WholeContinuousMildSerrinReceipt concreteCounterexampleViscosity
      concreteCounterexampleInitial.initialState (sourceHorizon + 1)) :
    ¬ BddAbove (range (elapsedTime concreteCounterexampleInitial)) := by
  intro bounded
  have accumulationLe : wholeRestartVelocityAccumulationTime concreteCounterexampleInitial ≤
      sourceHorizon := ciSup_le (bounded_elapsed_le_horizon bounded)
  have shorter : completeSerrinAccumulationHorizon concreteCounterexampleInitial ≤
      sourceHorizon + 1 := by
    unfold completeSerrinAccumulationHorizon
    linarith
  exact (completeSerrinAccumulationHorizon_receipt_isEmpty
    concreteCounterexampleInitial bounded).false
      (restrictWholeContinuousMildSerrinReceipt
        (completeSerrinAccumulationHorizon_pos concreteCounterexampleInitial bounded)
        shorter receipt)

end
end SaturationMonoid.NavierStokes.SelectionHorizon
