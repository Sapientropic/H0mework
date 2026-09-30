import H0mework.NavierStokes.EvenLattice.Barrier
import H0mework.NavierStokes.EvenLattice.Critical
import H0mework.NavierStokes.Crossing.TangentPaymentCascade

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open Set
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open RationalVorticityEvaluator

noncomputable section

theorem source_successor_mass_le_of_strictCritical (stage : ℕ)
    (small : wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial stage).contact.physicalState < 8 / 630000) :
    wholeVorticityEuclideanMass (run concreteCounterexampleInitial (stage + 1)).contact.physicalState ≤
      wholeVorticityEuclideanMass (run concreteCounterexampleInitial stage).contact.physicalState := by
  let current := run concreteCounterexampleInitial stage
  have bound := receipt_mass_le_initial_of_local_nonpos current.nextContact.prefixReceipt small
    (receipt_even_netPower_nonpos_below_ae current.nextContact.prefixReceipt
      (SourceEvenFrequency.source_contact_even stage))
  have terminal := bound ⟨current.nextContact.time.1, current.nextContact.time_pos.le, le_rfl⟩
  rw [current.nextContact.prefixReceipt_terminal] at terminal
  exact terminal

theorem source_tail_mass_le_of_strictCritical (stage : ℕ)
    (small : wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial stage).contact.physicalState < 8 / 630000) :
    ∀ offset : ℕ, wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial (stage + offset)).contact.physicalState ≤
        wholeVorticityEuclideanMass (run concreteCounterexampleInitial stage).contact.physicalState := by
  intro offset
  induction offset with
  | zero => simp
  | succ offset earlier =>
    have next := source_successor_mass_le_of_strictCritical (stage + offset) (earlier.trans_lt small)
    rw [show stage + (offset + 1) = stage + offset + 1 by omega]
    exact next.trans earlier

theorem source_time_unbounded_of_strictCritical (stage : ℕ)
    (small : wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial stage).contact.physicalState < 8 / 630000) :
    ¬ BddAbove (range (elapsedTime concreteCounterexampleInitial)) := by
  intro bounded
  have tailBounded := elapsedTime_run_bddAbove concreteCounterexampleInitial bounded stage
  apply elapsedTime_bddAbove_forces_physicalVorticityMass_unbounded
    (run concreteCounterexampleInitial stage) tailBounded
  refine ⟨wholeVorticityEuclideanMass
    (run concreteCounterexampleInitial stage).contact.physicalState, ?_⟩
  rintro _ ⟨offset, rfl⟩
  rw [restartPhysicalVorticityMass, run_run]
  exact source_tail_mass_le_of_strictCritical stage small offset

theorem source_time_unbounded_of_lowContact (stage : ℕ)
    (low : wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial stage).contact.physicalState < 1 / 79000) :
    ¬ BddAbove (range (elapsedTime concreteCounterexampleInitial)) :=
  source_time_unbounded_of_strictCritical stage (low.trans (by norm_num))

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
