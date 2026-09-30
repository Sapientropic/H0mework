import H0mework.NavierStokes.Galerkin.CriticalEnstrophyBarrier
import H0mework.NavierStokes.GeneratedPaths.StretchingBudget

/-!
# Critical viscous absorption along arbitrary generated scale paths

An arbitrary source-generated finite scale path already produces one actual
Galerkin trajectory and one cumulative weighted trace.  A strict
cutoff-independent enstrophy margin now changes the responsibility ledger:

```text
K₃ Y(0) ≤ θ ν² (2π)²,     0 ≤ θ < 1

⇒  Y(t) ≤ Y(0)
⇒  d(Y/2)/dt ≤ -(1-θ)(ν/2)(2π)² Z(t)
⇒  (1-θ)(ν/2)(2π)² ∫ Z ≤ Y(0)/2 - Y(T)/2
⇒  (1-θ)(ν/2)(2π)² T (weightedTrace/2) ≤ Y(0)/2.
```

Thus frequency growth, occupancy time, cumulative path trace, and viscous
dissipation are forced into one cutoff-independent inequality.  The factor
`1/2` in the absorption coefficient is the exact factor supplied by the
Young splitting in the complete-table stretching estimate.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption

open scoped BigOperators Topology ENNReal

open Set
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyRate
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathStretchingBudget

noncomputable section

/-- The positive fraction of viscous enstrophy dissipation left after the
critical stretching term is absorbed under a strict margin `θ < 1`. -/
def criticalEnstrophyAbsorptionCoefficient
    (θ : ℝ)
    (ν : Viscosity) : ℝ :=
  (1 - θ) * (ν.coeff / 2) * (2 * Real.pi) ^ 2

theorem criticalEnstrophyAbsorptionCoefficient_pos
    (θ : ℝ)
    (θLtOne : θ < 1)
    (ν : Viscosity) :
    0 < criticalEnstrophyAbsorptionCoefficient θ ν := by
  unfold criticalEnstrophyAbsorptionCoefficient
  exact mul_pos
    (mul_pos (sub_pos.mpr θLtOne)
      (div_pos ν.coeff_pos (by norm_num)))
    (sq_pos_of_pos (by positivity))

/-- The cutoff-independent critical rate becomes a genuinely negative
viscous rate whenever the current enstrophy has a strict margin `θ < 1`. -/
theorem finiteStateVorticity_rate_le_criticalAbsorption
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : Viscosity)
    (θ : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (evolves :
      HasDerivAt trajectory
        (finiteStateVorticityGenerator
          modes ν.coeff (trajectory t)) t)
    (reality : FiniteStateFourierReality (trajectory t))
    (transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ trajectory t wave = 0)
    (currentMargin :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            modes (trajectory t) ≤
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    finiteStateVorticityStretchingWork modes (trajectory t) -
          ν.coeff * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t) ≤
      -criticalEnstrophyAbsorptionCoefficient θ ν *
        finiteStateVorticityEnstrophyMass
          modes (trajectory t) := by
  have pointwise :=
    finiteStateVorticityHalfEnstrophy_hasDerivAt_and_le_globalCriticalRate
      modes negClosed ν.coeff ν.coeff_pos trajectory t
      evolves reality transverse
  have multiplierNonneg :
      0 ≤
        (ν.coeff⁻¹ / 2) *
          finiteStateVorticityEnstrophyMass
            modes (trajectory t) := by
    exact mul_nonneg
      (div_nonneg (inv_nonneg.mpr ν.coeff_pos.le) (by norm_num))
      (finiteStateVorticityEnstrophyMass_nonneg
        modes (trajectory t))
  have marginTerm :
      (ν.coeff⁻¹ / 2) *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t) *
          (criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              modes (trajectory t)) ≤
        (ν.coeff⁻¹ / 2) *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t) *
          (θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :=
    mul_le_mul_of_nonneg_left currentMargin multiplierNonneg
  calc
    finiteStateVorticityStretchingWork modes (trajectory t) -
          ν.coeff * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t) ≤
      -(ν.coeff / 2) *
          ((2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t)) +
        (ν.coeff⁻¹ / 2) *
          (criticalEnstrophyLatticeConstant *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t)) *
          finiteStateVorticityCoefficientEnstrophy
            modes (trajectory t) :=
      pointwise.2
    _ =
      -(ν.coeff / 2) *
          ((2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t)) +
        (ν.coeff⁻¹ / 2) *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t) *
          (criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              modes (trajectory t)) := by
      ring
    _ ≤
      -(ν.coeff / 2) *
          ((2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t)) +
        (ν.coeff⁻¹ / 2) *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t) *
          (θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :=
      add_le_add_right marginTerm _
    _ =
      -criticalEnstrophyAbsorptionCoefficient θ ν *
        finiteStateVorticityEnstrophyMass
          modes (trajectory t) := by
      unfold criticalEnstrophyAbsorptionCoefficient
      field_simp [ne_of_gt ν.coeff_pos]
      ring

/-- Every generated finite scale path whose endpoint source lies inside a
strict critical margin produces one actual absorbing trajectory.  The
weighted path trace must be paid by the initial half-enstrophy through a
cutoff-independent coefficient.

No trajectory, occupancy time, dissipation budget, cutoff, maximum shell,
or terminal target is a premise. -/
theorem generatedIntegerShellReachable_drives_criticalAbsorption
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (ν : Viscosity)
    (θ : ℝ)
    (θLtOne : θ < 1)
    (initialMargin :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            (generatedSupport current)
            (generatedComplexVorticityState current
              (generatedSupport current)) ≤
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    ∃ (trajectory : ℝ → ComplexVorticityHilbertState)
        (occupancyTime : ℝ),
      0 < occupancyTime ∧
        trajectory 0 =
          generatedComplexVorticityState current
            (generatedSupport current) ∧
        (∀ t ∈ Icc (0 : ℝ) occupancyTime,
          HasDerivAt trajectory
              (finiteStateVorticityGenerator
                (generatedSupport current) ν.coeff (trajectory t)) t ∧
            (∀ wave,
              wave ∉ generatedSupport current →
                trajectory t wave = 0) ∧
            (∀ wave,
              complexWavevector wave ⬝ᵥ trajectory t wave = 0) ∧
            FiniteStateFourierReality (trajectory t)) ∧
        (∀ t ∈ Icc (0 : ℝ) occupancyTime,
          finiteStateVorticityHalfEnstrophy
              (generatedSupport current) (trajectory t) ≤
              finiteStateVorticityHalfEnstrophy
                (generatedSupport current) (trajectory 0) ∧
            finiteStateVorticityStretchingWork
                  (generatedSupport current) (trajectory t) -
                ν.coeff * (2 * Real.pi) ^ 2 *
                  finiteStateVorticityEnstrophyMass
                    (generatedSupport current) (trajectory t) ≤
              -criticalEnstrophyAbsorptionCoefficient θ ν *
                finiteStateVorticityEnstrophyMass
                  (generatedSupport current) (trajectory t)) ∧
        criticalEnstrophyAbsorptionCoefficient θ ν *
              (∫ t in (0 : ℝ)..occupancyTime,
                finiteStateVorticityEnstrophyMass
                  (generatedSupport current) (trajectory t)) ≤
            finiteStateVorticityHalfEnstrophy
                (generatedSupport current) (trajectory 0) -
              finiteStateVorticityHalfEnstrophy
                (generatedSupport current)
                (trajectory occupancyTime) ∧
        criticalEnstrophyAbsorptionCoefficient θ ν *
              (occupancyTime *
                (integerShellWeightedNormSq
                    (generatedIntegerShellCumulativeTrace arrival) /
                  2)) ≤
            finiteStateVorticityHalfEnstrophy
              (generatedSupport current) (trajectory 0) := by
  obtain
      ⟨trajectory, occupancyTime, occupancyTimePos, initial,
        physicalProperties, exactStretchingBudget,
        pathStretchingBudget, pathStretchingBudgetWithoutTerminal⟩ :=
    generatedIntegerShellReachable_drives_stretchingBudget arrival ν
  let modes := generatedSupport current
  have negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes := by
    intro wave waveMem
    exact generatedSupport_waveNeg_mem current waveMem
  have evolves :
      ∀ t ∈ Icc (0 : ℝ) occupancyTime,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν.coeff (trajectory t)) t := by
    intro t tMem
    exact (physicalProperties t tMem).1
  have reality :
      ∀ t ∈ Icc (0 : ℝ) occupancyTime,
        FiniteStateFourierReality (trajectory t) := by
    intro t tMem
    exact (physicalProperties t tMem).2.2.2
  have transverse :
      ∀ t ∈ Icc (0 : ℝ) occupancyTime,
        ∀ wave ∈ modes,
          complexWavevector wave ⬝ᵥ trajectory t wave = 0 := by
    intro t tMem wave waveMem
    exact (physicalProperties t tMem).2.2.1 wave
  have initialMarginActual :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            modes (trajectory 0) ≤
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
    rw [initial]
    exact initialMargin
  have θLeOne : θ ≤ 1 :=
    θLtOne.le
  have thresholdNonneg :
      0 ≤ ν.coeff ^ 2 * (2 * Real.pi) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have criticalInitialSmall :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            modes (trajectory 0) ≤
        ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
    have θThresholdLe :
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 ≤
          ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
      simpa only [mul_assoc] using
        (mul_le_of_le_one_left thresholdNonneg θLeOne)
    exact initialMarginActual.trans θThresholdLe
  have barrierConclusion :=
    finiteStateVorticityHalfEnstrophy_le_initial_of_criticalSmall
      modes negClosed ν.coeff ν.coeff_pos trajectory
      0 occupancyTime evolves reality transverse criticalInitialSmall
  have pointwiseConclusion :
      ∀ t ∈ Icc (0 : ℝ) occupancyTime,
        finiteStateVorticityHalfEnstrophy modes (trajectory t) ≤
            finiteStateVorticityHalfEnstrophy modes (trajectory 0) ∧
          finiteStateVorticityStretchingWork modes (trajectory t) -
              ν.coeff * (2 * Real.pi) ^ 2 *
                finiteStateVorticityEnstrophyMass
                  modes (trajectory t) ≤
            -criticalEnstrophyAbsorptionCoefficient θ ν *
              finiteStateVorticityEnstrophyMass
                modes (trajectory t) := by
    intro t tMem
    have halfLeInitial :=
      (barrierConclusion t tMem).1
    have enstrophyLeInitial :
        finiteStateVorticityCoefficientEnstrophy
              modes (trajectory t) ≤
          finiteStateVorticityCoefficientEnstrophy
            modes (trajectory 0) := by
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
          initialMarginActual
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
        (Icc (0 : ℝ) occupancyTime) := by
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
        (Icc (0 : ℝ) occupancyTime) := by
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
        (Icc (0 : ℝ) occupancyTime) := by
    apply nonlinearContinuousOn.congr
    intro t tMem
    exact
      (finiteStateVorticityNonlinearWork_eq_stretchingWork
        modes negClosed (trajectory t) (reality t tMem)).symm
  have enstrophyIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVorticityEnstrophyMass modes (trajectory t))
        volume 0 occupancyTime :=
    ContinuousOn.intervalIntegrable_of_Icc
      occupancyTimePos.le enstrophyContinuousOn
  have stretchingIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVorticityStretchingWork modes (trajectory t))
        volume 0 occupancyTime :=
    ContinuousOn.intervalIntegrable_of_Icc
      occupancyTimePos.le stretchingContinuousOn
  have viscousIntegrable :
      IntervalIntegrable
        (fun t =>
          ν.coeff * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes (trajectory t))
        volume 0 occupancyTime :=
    enstrophyIntegrable.const_mul
      (ν.coeff * (2 * Real.pi) ^ 2)
  have absorptionIntegrable :
      IntervalIntegrable
        (fun t =>
          -criticalEnstrophyAbsorptionCoefficient θ ν *
            finiteStateVorticityEnstrophyMass modes (trajectory t))
        volume 0 occupancyTime :=
    enstrophyIntegrable.const_mul
      (-criticalEnstrophyAbsorptionCoefficient θ ν)
  have integralRateBound :=
    intervalIntegral.integral_mono_on
      occupancyTimePos.le
      (stretchingIntegrable.sub viscousIntegrable)
      absorptionIntegrable
      (fun t tMem => (pointwiseConclusion t tMem).2)
  rw [intervalIntegral.integral_sub
      stretchingIntegrable viscousIntegrable,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at integralRateBound
  have integratedAbsorption :
      criticalEnstrophyAbsorptionCoefficient θ ν *
            (∫ t in (0 : ℝ)..occupancyTime,
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) ≤
          finiteStateVorticityHalfEnstrophy
              modes (trajectory 0) -
            finiteStateVorticityHalfEnstrophy
              modes (trajectory occupancyTime) := by
    linarith
  have terminalNonneg :
      0 ≤
        finiteStateVorticityHalfEnstrophy
          modes (trajectory occupancyTime) :=
    finiteStateVorticityHalfEnstrophy_nonneg modes _
  have integratedAbsorptionWithoutTerminal :
      criticalEnstrophyAbsorptionCoefficient θ ν *
            (∫ t in (0 : ℝ)..occupancyTime,
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) ≤
          finiteStateVorticityHalfEnstrophy
            modes (trajectory 0) := by
    linarith
  have viscousFactorPos :
      0 < ν.coeff * (2 * Real.pi) ^ 2 :=
    mul_pos ν.coeff_pos (sq_pos_of_pos (by positivity))
  have pathChargeLeViscousIntegral :
      ν.coeff * (2 * Real.pi) ^ 2 *
            (occupancyTime *
              (integerShellWeightedNormSq
                  (generatedIntegerShellCumulativeTrace arrival) /
                2)) ≤
          ν.coeff * (2 * Real.pi) ^ 2 *
            (∫ t in (0 : ℝ)..occupancyTime,
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) := by
    calc
      ν.coeff * (2 * Real.pi) ^ 2 *
            (occupancyTime *
              (integerShellWeightedNormSq
                  (generatedIntegerShellCumulativeTrace arrival) /
                2)) ≤
          (∫ t in (0 : ℝ)..occupancyTime,
            finiteStateVorticityStretchingWork
              modes (trajectory t)) +
            finiteStateVorticityHalfEnstrophy
              modes (trajectory 0) -
            finiteStateVorticityHalfEnstrophy
              modes (trajectory occupancyTime) :=
        pathStretchingBudget
      _ =
          ν.coeff * (2 * Real.pi) ^ 2 *
            (∫ t in (0 : ℝ)..occupancyTime,
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) :=
        exactStretchingBudget.symm
  have pathChargeLeIntegral :
      occupancyTime *
            (integerShellWeightedNormSq
                (generatedIntegerShellCumulativeTrace arrival) /
              2) ≤
        ∫ t in (0 : ℝ)..occupancyTime,
          finiteStateVorticityEnstrophyMass
            modes (trajectory t) :=
    (mul_le_mul_iff_of_pos_left viscousFactorPos).mp
      pathChargeLeViscousIntegral
  have pathAbsorption :
      criticalEnstrophyAbsorptionCoefficient θ ν *
            (occupancyTime *
              (integerShellWeightedNormSq
                  (generatedIntegerShellCumulativeTrace arrival) /
                2)) ≤
          finiteStateVorticityHalfEnstrophy
            modes (trajectory 0) :=
    (mul_le_mul_of_nonneg_left pathChargeLeIntegral
      (criticalEnstrophyAbsorptionCoefficient_pos
        θ θLtOne ν).le).trans
      integratedAbsorptionWithoutTerminal
  exact
    ⟨trajectory, occupancyTime, occupancyTimePos, initial,
      physicalProperties, pointwiseConclusion,
      integratedAbsorption, pathAbsorption⟩

/-- With the fixed margin `θ = 1/2`, every generated finite scale path has
a source-owned disposition: either its endpoint initial load is already
supercritical for that margin, or the source produces an actual absorbing
trajectory and pays the cumulative path trace from initial enstrophy.

This is a generated obstruction/consumer dichotomy.  It does not assert
arbitrary-data continuation. -/
theorem generatedIntegerShellReachable_halfMargin_disposition
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (ν : Viscosity) :
    (1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 <
        criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            (generatedSupport current)
            (generatedComplexVorticityState current
              (generatedSupport current)) ∨
      ∃ (trajectory : ℝ → ComplexVorticityHilbertState)
          (occupancyTime : ℝ),
        0 < occupancyTime ∧
          trajectory 0 =
            generatedComplexVorticityState current
              (generatedSupport current) ∧
          (∀ t ∈ Icc (0 : ℝ) occupancyTime,
            HasDerivAt trajectory
                (finiteStateVorticityGenerator
                  (generatedSupport current) ν.coeff (trajectory t)) t ∧
              (∀ wave,
                wave ∉ generatedSupport current →
                  trajectory t wave = 0) ∧
              (∀ wave,
                complexWavevector wave ⬝ᵥ trajectory t wave = 0) ∧
              FiniteStateFourierReality (trajectory t)) ∧
          criticalEnstrophyAbsorptionCoefficient (1 / 2) ν *
                (occupancyTime *
                  (integerShellWeightedNormSq
                      (generatedIntegerShellCumulativeTrace arrival) /
                    2)) ≤
              finiteStateVorticityHalfEnstrophy
                (generatedSupport current) (trajectory 0) := by
  by_cases supercritical :
      (1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 <
        criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            (generatedSupport current)
            (generatedComplexVorticityState current
              (generatedSupport current))
  · exact Or.inl supercritical
  · right
    have halfMargin :
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport current)
              (generatedComplexVorticityState current
                (generatedSupport current)) ≤
          (1 / 2 : ℝ) * ν.coeff ^ 2 *
            (2 * Real.pi) ^ 2 := by
      exact not_lt.mp supercritical
    obtain
        ⟨trajectory, occupancyTime, occupancyTimePos, initial,
          physicalProperties, pointwiseConclusion,
          integratedAbsorption, pathAbsorption⟩ :=
      generatedIntegerShellReachable_drives_criticalAbsorption
        arrival ν (1 / 2) (by norm_num)
        halfMargin
    exact
      ⟨trajectory, occupancyTime, occupancyTimePos,
        initial, physicalProperties, pathAbsorption⟩

end

end ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
end NavierStokes
end SaturationMonoid
