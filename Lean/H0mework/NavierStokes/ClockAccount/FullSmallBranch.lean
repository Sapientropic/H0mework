import H0mework.NavierStokes.ClockAccount.FullLowMassBranch

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SmallBranch

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalDualSquareReduction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryDisposition
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open WindowMassCoefficient

noncomputable section

theorem lowContact_tail_unbounded
    (stage : Nat)
    (low : wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial stage).contact.physicalState ≤ halfCriticalMass) :
    ¬ BddAbove (range (elapsedTime (run concreteCounterexampleInitial stage))) := by
  apply elapsedTime_not_bddAbove_of_initial_halfCriticalMargin
  unfold halfCriticalMass at low
  have paid := (le_div_iff₀ (mul_pos (by norm_num : (0 : Real) < 2)
    criticalEnstrophyLatticeConstant_pos)).mp low
  change wholeVorticityEuclideanMass
    (run concreteCounterexampleInitial stage).contact.physicalState *
      (2 * criticalEnstrophyLatticeConstant) ≤
        concreteCounterexampleViscosity.coeff ^ 2 * (2 * Real.pi) ^ 2 at paid
  linarith

/-- The tail is the original run after its actual finite prefix. -/
theorem lowContact_originalRun_unbounded
    (stage : Nat)
    (low : wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial stage).contact.physicalState ≤ halfCriticalMass) :
    ¬ BddAbove (range (elapsedTime concreteCounterexampleInitial)) := by
  intro bounded
  exact lowContact_tail_unbounded stage low
    (elapsedTime_run_bddAbove concreteCounterexampleInitial bounded stage)

/-- Actual low contact generates the complete original global path. -/
def lowContact_globalTrajectory
    (stage : Nat)
    (low : wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial stage).contact.physicalState ≤ halfCriticalMass) :
    GeneratedWholeGlobalPhysicalTrajectory concreteCounterexampleInitial :=
  generatedWholeGlobalPhysicalTrajectory_of_unbounded concreteCounterexampleInitial
    (lowContact_originalRun_unbounded stage low)

/-- The same source's finite half-critical contact is an exact old-time
selection criterion, not an assumed global trajectory or a replacement run. -/
theorem originalRun_unbounded_iff_halfCritical_contact :
    (¬ BddAbove (range (elapsedTime concreteCounterexampleInitial))) ↔
      ∃ stage : Nat, wholeVorticityEuclideanMass
        (run concreteCounterexampleInitial (stage + 1)).contact.physicalState ≤
          halfCriticalMass := by
  constructor
  · intro unbounded
    exact (sourceGeneratedBoundaryInquiryOutcome concreteCounterexampleInitial).fold
      (fun oldInquiry => LowMassBranch.oldInquiry_generates_halfCritical_contact oldInquiry)
      (fun revisedInquiry => False.elim (unbounded revisedInquiry.elapsedBounded))
  · rintro ⟨stage, low⟩
    exact lowContact_originalRun_unbounded (stage + 1) low

end
end SaturationMonoid.NavierStokes.SmallBranch
