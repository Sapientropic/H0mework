import Mathlib.Analysis.ODE.Gronwall
import H0mework.NavierStokes.Galerkin.CriticalEnstrophyRate

/-!
# Cutoff-independent critical Grönwall consumer

Mathlib currently provides local Picard--Lindelöf existence and
constant-coefficient Grönwall bounds, but no maximal-solution/blow-up
alternative and no variable-coefficient integral Grönwall theorem.

This module closes the latter gap and applies it directly to the actual
finite Galerkin critical enstrophy rate.  For

```text
y(t) = one-half * sum_k |omega_k(t)|^2,
z(t) = sum_k |k|^2 |omega_k(t)|^2,
```

the result is the cutoff-independent estimate

```text
y(t) <= y(a) * exp (nu⁻¹ * K₃ * integral_a^t z(s) ds).
```

No maximum frequency, mode cardinality, inverse inequality, continuation
certificate, or preselected budget enters the theorem mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalGronwall

open scoped BigOperators Topology Interval

open Set
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyRate

noncomputable section

/-! ## Variable-coefficient integral Grönwall -/

/--
Integral Grönwall inequality for a differentiable scalar path and a
continuous variable coefficient.

This is the integrating-factor form missing from
`Mathlib.Analysis.ODE.Gronwall`: the exponential contains the actual
coefficient integral rather than a supplied uniform supremum.
-/
theorem le_initial_mul_exp_integral_of_hasDerivAt_le_mul
    {f f' coefficient : ℝ → ℝ}
    {a b : ℝ}
    (evolves :
      ∀ t ∈ Icc a b,
        HasDerivAt f (f' t) t)
    (coefficientContinuous :
      ContinuousOn coefficient (Icc a b))
    (rate :
      ∀ t ∈ Icc a b,
        f' t ≤ coefficient t * f t) :
    ∀ t ∈ Icc a b,
      f t ≤
        f a *
          Real.exp
            (∫ s in a..t, coefficient s) := by
  intro t timeMem
  let primitive : ℝ → ℝ := fun x =>
    ∫ s in a..x, coefficient s
  let weighted : ℝ → ℝ := fun x =>
    Real.exp (-primitive x) * f x
  have intervalSubset :
      Icc a t ⊆ Icc a b :=
    Icc_subset_Icc le_rfl timeMem.2
  have coefficientContinuousAt :
      ContinuousOn coefficient (Icc a t) :=
    coefficientContinuous.mono intervalSubset
  have coefficientIntegrableOn :
      IntegrableOn coefficient (Icc a t) volume :=
    coefficientContinuousAt.integrableOn_Icc
  have coefficientIntegrableOnU :
      IntegrableOn coefficient (uIcc a t) volume := by
    simpa [uIcc_of_le timeMem.1] using
      coefficientIntegrableOn
  have primitiveContinuous :
      ContinuousOn primitive (Icc a t) := by
    have primitiveContinuousRaw :
        ContinuousOn
          (fun x => ∫ s in a..x, coefficient s)
          (uIcc a t) :=
      intervalIntegral.continuousOn_primitive_interval
        (μ := volume)
        coefficientIntegrableOnU
    simpa only [primitive, uIcc_of_le timeMem.1] using
      primitiveContinuousRaw
  have fContinuous :
      ContinuousOn f (Icc a t) := by
    apply HasDerivAt.continuousOn
    intro x xMem
    exact evolves x (intervalSubset xMem)
  have weightedContinuous :
      ContinuousOn weighted (Icc a t) := by
    exact
      (Real.continuous_exp.comp_continuousOn
          primitiveContinuous.neg).mul fContinuous
  have weightedDerivative :
      ∀ x ∈ Ioo a t,
        HasDerivAt weighted
          (Real.exp (-primitive x) *
            (f' x - coefficient x * f x)) x := by
    intro x xMem
    have xMemFull : x ∈ Icc a b :=
      intervalSubset ⟨xMem.1.le, xMem.2.le⟩
    have coefficientContinuousAtX :
        ContinuousAt coefficient x := by
      exact
        (coefficientContinuous x xMemFull).continuousAt
          (Icc_mem_nhds xMem.1
            (xMem.2.trans_le timeMem.2))
    have coefficientIntegrable :
        IntervalIntegrable coefficient volume a x := by
      apply
        ContinuousOn.intervalIntegrable_of_Icc xMem.1.le
      exact
        coefficientContinuous.mono
          (Icc_subset_Icc le_rfl
            (xMem.2.le.trans timeMem.2))
    have coefficientStronglyMeasurable :
        StronglyMeasurableAtFilter coefficient (𝓝 x) volume := by
      exact
        AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
          coefficientIntegrableOn.aestronglyMeasurable
          (Icc_mem_nhds xMem.1 xMem.2)
    have primitiveDerivative :
        HasDerivAt primitive (coefficient x) x := by
      simpa [primitive] using
        intervalIntegral.integral_hasDerivAt_right
          coefficientIntegrable
          coefficientStronglyMeasurable
          coefficientContinuousAtX
    have exponentialDerivative :=
      primitiveDerivative.neg.exp
    have productDerivative :=
      exponentialDerivative.mul (evolves x xMemFull)
    change
      HasDerivAt weighted
        ((Real.exp (-primitive x) * -coefficient x) * f x +
          Real.exp (-primitive x) * f' x) x at productDerivative
    convert productDerivative using 1
    ring
  have weightedAntitone :
      AntitoneOn weighted (Icc a t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a t)
      weightedContinuous
    · rw [interior_Icc]
      intro x xMem
      exact
        (weightedDerivative x xMem).differentiableAt
          |>.differentiableWithinAt
    · rw [interior_Icc]
      intro x xMem
      rw [(weightedDerivative x xMem).deriv]
      exact
        mul_nonpos_of_nonneg_of_nonpos
          (Real.exp_nonneg _)
          (sub_nonpos.mpr
            (rate x
              (intervalSubset
                ⟨xMem.1.le, xMem.2.le⟩)))
  have weightedUpper :
      weighted t ≤ weighted a :=
    weightedAntitone
      ⟨le_rfl, timeMem.1⟩
      ⟨timeMem.1, le_rfl⟩
      timeMem.1
  have integratingFactorUpper :
      Real.exp (-primitive t) * f t ≤ f a := by
    simpa [weighted, primitive] using weightedUpper
  calc
    f t =
        Real.exp (primitive t) *
          (Real.exp (-primitive t) * f t) := by
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    _ ≤
        Real.exp (primitive t) * f a :=
      mul_le_mul_of_nonneg_left integratingFactorUpper
        (Real.exp_nonneg _)
    _ =
        f a *
          Real.exp
            (∫ s in a..t, coefficient s) := by
      simp [primitive, mul_comm]

/-! ## Critical finite Galerkin consumer -/

/--
The cutoff-independent coefficient multiplying half-enstrophy after the
negative viscous half of the critical rate is discarded.
-/
def finiteStateVorticityIntegratedGradientGronwallCoefficient
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ν⁻¹ *
    (biotSavartSerrinConstant *
      (∑' wave : IntegerWavevector,
        integerWaveCriticalKernel wave)) *
    finiteStateVorticityEnstrophyMass modes state

/--
The actual finite Galerkin half-enstrophy is bounded by its initial value
times the exponential of the integrated, cutoff-independent gradient mass.

The pointwise rate is generated by the original Galerkin update and the
physical transverse/reality invariants.  The theorem does not accept a
frequency cutoff, inverse inequality, continuation witness, upper budget, or
terminal norm as a premise.
-/
theorem finiteStateVorticityHalfEnstrophy_le_exp_integratedGradientMass
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : ℝ)
    (ν_pos : 0 < ν)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (evolves :
      ∀ t ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory t)) t)
    (reality :
      ∀ t ∈ Icc a b,
        FiniteStateFourierReality (trajectory t))
    (transverse :
      ∀ t ∈ Icc a b,
        ∀ wave ∈ modes,
          complexWavevector wave ⬝ᵥ
            trajectory t wave = 0) :
    ∀ t ∈ Icc a b,
      finiteStateVorticityHalfEnstrophy
          modes (trajectory t) ≤
        finiteStateVorticityHalfEnstrophy
            modes (trajectory a) *
          Real.exp
            (ν⁻¹ *
              (biotSavartSerrinConstant *
                (∑' wave : IntegerWavevector,
                  integerWaveCriticalKernel wave)) *
              (∫ s in a..t,
                finiteStateVorticityEnstrophyMass
                  modes (trajectory s))) := by
  let energy : ℝ → ℝ := fun t =>
    finiteStateVorticityHalfEnstrophy modes (trajectory t)
  let energyRate : ℝ → ℝ := fun t =>
    finiteStateVorticityStretchingWork modes (trajectory t) -
      ν * (2 * Real.pi) ^ 2 *
        finiteStateVorticityEnstrophyMass modes (trajectory t)
  let coefficient : ℝ → ℝ := fun t =>
    finiteStateVorticityIntegratedGradientGronwallCoefficient
      modes ν (trajectory t)
  have energyDerivative :
      ∀ t ∈ Icc a b,
        HasDerivAt energy (energyRate t) t := by
    intro t timeMem
    exact
      (finiteStateVorticityHalfEnstrophy_hasDerivAt_and_le_globalCriticalRate
        modes negClosed ν ν_pos trajectory t
        (evolves t timeMem)
        (reality t timeMem)
        (transverse t timeMem)).1
  have coefficientContinuous :
      ContinuousOn coefficient (Icc a b) := by
    intro t timeMem
    have massContinuous :=
      finiteStateVorticityEnstrophyMass_continuousAt_of_hasDerivAt
        modes trajectory t
        (finiteStateVorticityGenerator
          modes ν (trajectory t))
        (evolves t timeMem)
    exact
      (massContinuous.const_mul
        (ν⁻¹ *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave))))
        |>.continuousWithinAt
  have energyRateLe :
      ∀ t ∈ Icc a b,
        energyRate t ≤ coefficient t * energy t := by
    intro t timeMem
    have criticalUpper :=
      (finiteStateVorticityHalfEnstrophy_hasDerivAt_and_le_globalCriticalRate
        modes negClosed ν ν_pos trajectory t
        (evolves t timeMem)
        (reality t timeMem)
        (transverse t timeMem)).2
    have gradientMassNonneg :
        0 ≤ finiteStateVorticityEnstrophyMass
          modes (trajectory t) :=
      finiteStateVorticityEnstrophyMass_nonneg
        modes (trajectory t)
    have dissipativeHalfNonneg :
        0 ≤
          (ν / 2) *
            ((2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) := by
      exact mul_nonneg
        (div_nonneg ν_pos.le (by norm_num))
        (mul_nonneg (sq_nonneg _)
          gradientMassNonneg)
    calc
      energyRate t ≤
          -(ν / 2) *
              ((2 * Real.pi) ^ 2 *
                finiteStateVorticityEnstrophyMass
                  modes (trajectory t)) +
            (ν⁻¹ / 2) *
              (biotSavartSerrinConstant *
                (∑' wave : IntegerWavevector,
                  integerWaveCriticalKernel wave) *
                finiteStateVorticityEnstrophyMass
                  modes (trajectory t)) *
              finiteStateVorticityCoefficientEnstrophy
                modes (trajectory t) := by
        exact criticalUpper
      _ =
          -(ν / 2) *
              ((2 * Real.pi) ^ 2 *
                finiteStateVorticityEnstrophyMass
                  modes (trajectory t)) +
            coefficient t * energy t := by
        unfold coefficient
          finiteStateVorticityIntegratedGradientGronwallCoefficient
          energy finiteStateVorticityHalfEnstrophy
        ring
      _ ≤ coefficient t * energy t := by
        linarith
  have gronwall :=
    le_initial_mul_exp_integral_of_hasDerivAt_le_mul
      energyDerivative coefficientContinuous energyRateLe
  intro t timeMem
  have bound := gronwall t timeMem
  simp only [coefficient,
    finiteStateVorticityIntegratedGradientGronwallCoefficient] at bound
  rw [intervalIntegral.integral_const_mul] at bound
  simpa [energy, mul_assoc] using bound

end

end ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalGronwall
end NavierStokes
end SaturationMonoid
