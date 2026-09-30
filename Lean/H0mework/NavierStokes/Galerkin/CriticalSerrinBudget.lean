import H0mework.NavierStokes.GeneratedPaths.CriticalAbsorption
import H0mework.NavierStokes.GeneratedPaths.CriticalTimeConsumer

/-!
# A cutoff-independent critical Serrin budget on every actual Galerkin interval

This is the target-side continuation budget.  It does not generate a local
trajectory from a source; instead it applies to every actual physical
Galerkin trajectory on every finite interval.  A strict initial critical
margin propagates, absorbs the complete vorticity-gradient mass, and pays
the full Fourier velocity majorant:

```text
Aθ ∫ Z ≤ H(a) - H(b),
Aθ ∫ M² ≤ K₃ (H(a) - H(b)),
∫ M² ≤ K₃ H(a) / Aθ.
```

All constants are independent of the Galerkin inventory.  Consequently the
same bound is available on every finite prefix of a maximal finite-mode
solution.  The remaining infinite-dimensional gate is to consume it through
parabolic mild continuation or a compactness/weak-limit theorem.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalSerrinBudget

open scoped BigOperators Topology ENNReal

open Set
open MeasureTheory
open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalTimeConsumer
open ThreeDimensionalVorticityCoefficientGeneratedPathStretchingBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption

noncomputable section

/-- A strict critical margin generates the complete `L²_t L∞_x`
Fourier-majorant budget on every actual finite Galerkin interval.

The trajectory and its physical laws are the target model being consumed;
no integral budget, velocity norm, terminal state, cutoff bound, maximum
frequency, or continuation witness is assumed. -/
theorem finiteStateVorticity_criticalSerrinBudget_on_Icc
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : Viscosity)
    (θ : ℝ)
    (θLtOne : θ < 1)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (hab : a ≤ b)
    (evolves :
      ∀ t ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν.coeff (trajectory t)) t)
    (reality :
      ∀ t ∈ Icc a b,
        FiniteStateFourierReality (trajectory t))
    (transverse :
      ∀ t ∈ Icc a b,
        ∀ wave ∈ modes,
          complexWavevector wave ⬝ᵥ trajectory t wave = 0)
    (initialMargin :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            modes (trajectory a) ≤
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    (∀ t ∈ Icc a b,
      finiteStateVorticityHalfEnstrophy
          modes (trajectory t) ≤
          finiteStateVorticityHalfEnstrophy
            modes (trajectory a) ∧
        finiteStateVorticityStretchingWork modes (trajectory t) -
            ν.coeff * (2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass
                modes (trajectory t) ≤
          -criticalEnstrophyAbsorptionCoefficient θ ν *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t)) ∧
      criticalEnstrophyAbsorptionCoefficient θ ν *
            (∫ t in a..b,
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) ≤
          finiteStateVorticityHalfEnstrophy
              modes (trajectory a) -
            finiteStateVorticityHalfEnstrophy
              modes (trajectory b) ∧
      criticalEnstrophyAbsorptionCoefficient θ ν *
            (∫ t in a..b,
              finiteStateVelocityMajorant
                modes (trajectory t) ^ 2) ≤
          criticalEnstrophyLatticeConstant *
            (finiteStateVorticityHalfEnstrophy
                modes (trajectory a) -
              finiteStateVorticityHalfEnstrophy
                modes (trajectory b)) ∧
      (∫ t in a..b,
          finiteStateVelocityMajorant
            modes (trajectory t) ^ 2) ≤
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityHalfEnstrophy
              modes (trajectory a) /
          criticalEnstrophyAbsorptionCoefficient θ ν := by
  have θLeOne : θ ≤ 1 := θLtOne.le
  have thresholdNonneg :
      0 ≤ ν.coeff ^ 2 * (2 * Real.pi) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have criticalInitialSmall :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            modes (trajectory a) ≤
        ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
    have θThresholdLe :
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 ≤
          ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
      simpa only [mul_assoc] using
        (mul_le_of_le_one_left thresholdNonneg θLeOne)
    exact initialMargin.trans θThresholdLe
  have barrierConclusion :=
    finiteStateVorticityHalfEnstrophy_le_initial_of_criticalSmall
      modes negClosed ν.coeff ν.coeff_pos trajectory
      a b evolves reality transverse criticalInitialSmall
  have pointwiseConclusion :
      ∀ t ∈ Icc a b,
        finiteStateVorticityHalfEnstrophy
            modes (trajectory t) ≤
            finiteStateVorticityHalfEnstrophy
              modes (trajectory a) ∧
          finiteStateVorticityStretchingWork modes (trajectory t) -
              ν.coeff * (2 * Real.pi) ^ 2 *
                finiteStateVorticityEnstrophyMass
                  modes (trajectory t) ≤
            -criticalEnstrophyAbsorptionCoefficient θ ν *
              finiteStateVorticityEnstrophyMass
                modes (trajectory t) := by
    intro t tMem
    have halfLeInitial := (barrierConclusion t tMem).1
    have enstrophyLeInitial :
        finiteStateVorticityCoefficientEnstrophy
              modes (trajectory t) ≤
          finiteStateVorticityCoefficientEnstrophy
            modes (trajectory a) := by
      unfold finiteStateVorticityHalfEnstrophy at halfLeInitial
      linarith
    have currentMargin :
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              modes (trajectory t) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
      exact
        (mul_le_mul_of_nonneg_left enstrophyLeInitial
          criticalEnstrophyLatticeConstant_nonneg).trans
          initialMargin
    exact
      ⟨halfLeInitial,
        finiteStateVorticity_rate_le_criticalAbsorption
          modes negClosed ν θ trajectory t
          (evolves t tMem) (reality t tMem)
          (transverse t tMem) currentMargin⟩
  have enstrophyContinuousOn :
      ContinuousOn
        (fun t =>
          finiteStateVorticityEnstrophyMass modes (trajectory t))
        (Icc a b) := by
    intro t tMem
    exact
      (finiteStateVorticityEnstrophyMass_continuousAt_of_hasDerivAt
        modes trajectory t
        (finiteStateVorticityGenerator
          modes ν.coeff (trajectory t))
        (evolves t tMem)).continuousWithinAt
  have nonlinearContinuousOn :
      ContinuousOn
        (fun t =>
          finiteStateVorticityNonlinearWork modes (trajectory t))
        (Icc a b) := by
    intro t tMem
    exact
      (finiteStateVorticityNonlinearWork_continuousAt_of_hasDerivAt
        modes trajectory t
        (finiteStateVorticityGenerator
          modes ν.coeff (trajectory t))
        (evolves t tMem)).continuousWithinAt
  have stretchingContinuousOn :
      ContinuousOn
        (fun t =>
          finiteStateVorticityStretchingWork modes (trajectory t))
        (Icc a b) := by
    apply nonlinearContinuousOn.congr
    intro t tMem
    exact
      (finiteStateVorticityNonlinearWork_eq_stretchingWork
        modes negClosed (trajectory t) (reality t tMem)).symm
  have majorantContinuousOn :
      ContinuousOn
        (fun t =>
          finiteStateVelocityMajorant modes (trajectory t) ^ 2)
        (Icc a b) := by
    intro t tMem
    exact
      ((finiteStateVelocityMajorant_continuousAt_of_hasDerivAt
        modes trajectory t
        (finiteStateVorticityGenerator
          modes ν.coeff (trajectory t))
        (evolves t tMem)).pow 2).continuousWithinAt
  have enstrophyIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVorticityEnstrophyMass modes (trajectory t))
        volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab enstrophyContinuousOn
  have stretchingIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVorticityStretchingWork modes (trajectory t))
        volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab stretchingContinuousOn
  have majorantIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVelocityMajorant modes (trajectory t) ^ 2)
        volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab majorantContinuousOn
  have viscousIntegrable :
      IntervalIntegrable
        (fun t =>
          ν.coeff * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes (trajectory t))
        volume a b :=
    enstrophyIntegrable.const_mul
      (ν.coeff * (2 * Real.pi) ^ 2)
  have absorptionIntegrable :
      IntervalIntegrable
        (fun t =>
          -criticalEnstrophyAbsorptionCoefficient θ ν *
            finiteStateVorticityEnstrophyMass modes (trajectory t))
        volume a b :=
    enstrophyIntegrable.const_mul
      (-criticalEnstrophyAbsorptionCoefficient θ ν)
  have integralRateBound :=
    intervalIntegral.integral_mono_on
      hab (stretchingIntegrable.sub viscousIntegrable)
      absorptionIntegrable
      (fun t tMem => (pointwiseConclusion t tMem).2)
  rw [intervalIntegral.integral_sub
      stretchingIntegrable viscousIntegrable,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at integralRateBound
  have exactEnstrophyLedger :=
    finiteStateVorticityHalfEnstrophy_integral_stretchingWork
      modes negClosed ν.coeff trajectory a b hab evolves reality
  rw [intervalIntegral.integral_sub
      stretchingIntegrable viscousIntegrable,
    intervalIntegral.integral_const_mul] at exactEnstrophyLedger
  have integratedAbsorption :
      criticalEnstrophyAbsorptionCoefficient θ ν *
            (∫ t in a..b,
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) ≤
          finiteStateVorticityHalfEnstrophy
              modes (trajectory a) -
            finiteStateVorticityHalfEnstrophy
              modes (trajectory b) := by
    linarith
  have latticeScaledEnstrophyIntegrable :
      IntervalIntegrable
        (fun t =>
          criticalEnstrophyLatticeConstant *
            finiteStateVorticityEnstrophyMass modes (trajectory t))
        volume a b :=
    enstrophyIntegrable.const_mul criticalEnstrophyLatticeConstant
  have majorantIntegralUpper :
      (∫ t in a..b,
          finiteStateVelocityMajorant modes (trajectory t) ^ 2) ≤
        criticalEnstrophyLatticeConstant *
          ∫ t in a..b,
            finiteStateVorticityEnstrophyMass modes (trajectory t) := by
    have integrated :=
      intervalIntegral.integral_mono_on
        hab majorantIntegrable latticeScaledEnstrophyIntegrable
        (fun t _ =>
          finiteStateVelocityMajorant_sq_le_criticalGlobal
            modes (trajectory t))
    simpa [criticalEnstrophyLatticeConstant,
      intervalIntegral.integral_const_mul] using integrated
  have absorptionCoefficientPos :
      0 < criticalEnstrophyAbsorptionCoefficient θ ν :=
    criticalEnstrophyAbsorptionCoefficient_pos θ θLtOne ν
  have serrinAbsorption :
      criticalEnstrophyAbsorptionCoefficient θ ν *
            (∫ t in a..b,
              finiteStateVelocityMajorant
                modes (trajectory t) ^ 2) ≤
          criticalEnstrophyLatticeConstant *
            (finiteStateVorticityHalfEnstrophy
                modes (trajectory a) -
              finiteStateVorticityHalfEnstrophy
                modes (trajectory b)) := by
    calc
      criticalEnstrophyAbsorptionCoefficient θ ν *
            (∫ t in a..b,
              finiteStateVelocityMajorant
                modes (trajectory t) ^ 2) ≤
          criticalEnstrophyAbsorptionCoefficient θ ν *
            (criticalEnstrophyLatticeConstant *
              ∫ t in a..b,
                finiteStateVorticityEnstrophyMass
                  modes (trajectory t)) :=
        mul_le_mul_of_nonneg_left
          majorantIntegralUpper absorptionCoefficientPos.le
      _ = criticalEnstrophyLatticeConstant *
            (criticalEnstrophyAbsorptionCoefficient θ ν *
              ∫ t in a..b,
                finiteStateVorticityEnstrophyMass
                  modes (trajectory t)) := by
        ring
      _ ≤ criticalEnstrophyLatticeConstant *
            (finiteStateVorticityHalfEnstrophy
                modes (trajectory a) -
              finiteStateVorticityHalfEnstrophy
                modes (trajectory b)) :=
        mul_le_mul_of_nonneg_left integratedAbsorption
          criticalEnstrophyLatticeConstant_nonneg
  have terminalHalfEnstrophyNonneg :
      0 ≤
        finiteStateVorticityHalfEnstrophy
          modes (trajectory b) :=
    finiteStateVorticityHalfEnstrophy_nonneg modes _
  have serrinAbsorptionWithoutTerminal :
      criticalEnstrophyAbsorptionCoefficient θ ν *
            (∫ t in a..b,
              finiteStateVelocityMajorant
                modes (trajectory t) ^ 2) ≤
          criticalEnstrophyLatticeConstant *
            finiteStateVorticityHalfEnstrophy
              modes (trajectory a) := by
    exact serrinAbsorption.trans
      (mul_le_mul_of_nonneg_left
        (sub_le_self _ terminalHalfEnstrophyNonneg)
        criticalEnstrophyLatticeConstant_nonneg)
  have criticalNormBound :
      (∫ t in a..b,
          finiteStateVelocityMajorant
            modes (trajectory t) ^ 2) ≤
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityHalfEnstrophy
              modes (trajectory a) /
          criticalEnstrophyAbsorptionCoefficient θ ν := by
    exact
      (le_div_iff₀ absorptionCoefficientPos).2 (by
        simpa [mul_comm] using serrinAbsorptionWithoutTerminal)
  exact
    ⟨pointwiseConclusion, integratedAbsorption,
      serrinAbsorption, criticalNormBound⟩

end

end ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalSerrinBudget
end NavierStokes
end SaturationMonoid
