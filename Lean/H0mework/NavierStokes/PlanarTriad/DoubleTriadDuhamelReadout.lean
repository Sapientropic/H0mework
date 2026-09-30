import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import H0mework.NavierStokes.PlanarTriad.DoubleTriadFilteredPropagationCarrier

/-!
# Duhamel readouts for the middle-cutoff propagation carrier

This module contains the analytic readouts and finite-time consumers for
already generated full and filtered trajectories.  It does not generate
either path.
-/

namespace SaturationMonoid.NavierStokes
namespace TwoDimensionalVorticityDoubleTriadDuhamelPropagationResidual

noncomputable section

open scoped Interval

open Set
open TwoDimensionalVorticityDoubleTriadRealScalarExtension

/-! ## Duhamel and filtered-carrier readouts -/

/-- General Duhamel readout for two already generated actual paths.  The
evolution laws and aligned initial state are consumed explicitly; the
propagation residual is not discarded. -/
theorem realDoubleTriad_middleDuhamel_identity
    (full filtered : ℝ → RealDoubleTriadState) (T : ℝ)
    (TPos : 0 < T)
    (fullEvolves :
      ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivAt full
          (realDoubleTriadNavierStokesGalerkinGenerator
            (1 / 100) (full t)) t)
    (filteredEvolves :
      ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivAt filtered
          (realDoubleTriadMiddleFilteredGenerator
            (1 / 100) (filtered t)) t)
    (initialAligned :
      realDoubleTriadMiddlePass (full 0) = filtered 0) :
    realDoubleTriadMiddlePass (full T) - filtered T =
      (∫ t in 0..T,
          realDoubleTriadUpperTrace
            (1 / 100) (full t)) +
        ∫ t in 0..T,
          realDoubleTriadMiddlePropagationResidual
            (1 / 100) (full t) (filtered t) := by
  have fullContinuous :
      ContinuousOn full (Icc (0 : ℝ) T) := by
    intro t membership
    exact
      (fullEvolves t membership).continuousAt.continuousWithinAt
  have filteredContinuous :
      ContinuousOn filtered (Icc (0 : ℝ) T) := by
    intro t membership
    exact
      (filteredEvolves t membership).continuousAt.continuousWithinAt
  have upperTraceContinuous :
      ContinuousOn
        (fun t =>
          realDoubleTriadUpperTrace
            (1 / 100) (full t))
        (Icc (0 : ℝ) T) :=
    (realDoubleTriadUpperTrace_continuous
      (1 / 100)).continuousOn.comp
        fullContinuous
        (fun _ _ => Set.mem_univ _)
  have propagationContinuous :
      ContinuousOn
        (fun t =>
          realDoubleTriadMiddlePropagationResidual
            (1 / 100) (full t) (filtered t))
        (Icc (0 : ℝ) T) :=
    realDoubleTriadMiddlePropagationResidual_continuousOn
      (1 / 100) fullContinuous filteredContinuous
  have upperTraceIntegrable :
      IntervalIntegrable
        (fun t =>
          realDoubleTriadUpperTrace
            (1 / 100) (full t))
        MeasureTheory.volume 0 T :=
    upperTraceContinuous.intervalIntegrable_of_Icc
      (le_of_lt TPos)
  have propagationIntegrable :
      IntervalIntegrable
        (fun t =>
          realDoubleTriadMiddlePropagationResidual
            (1 / 100) (full t) (filtered t))
        MeasureTheory.volume 0 T :=
    propagationContinuous.intervalIntegrable_of_Icc
      (le_of_lt TPos)
  have endpointFTC :
      (∫ t in 0..T,
          (realDoubleTriadUpperTrace
              (1 / 100) (full t) +
            realDoubleTriadMiddlePropagationResidual
              (1 / 100) (full t) (filtered t))) =
        (realDoubleTriadMiddlePass (full T) - filtered T) -
          (realDoubleTriadMiddlePass (full 0) -
            filtered 0) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f :=
        fun time =>
          realDoubleTriadMiddlePass (full time) -
            filtered time)
      (f' :=
        fun time =>
          realDoubleTriadUpperTrace
              (1 / 100) (full time) +
            realDoubleTriadMiddlePropagationResidual
              (1 / 100) (full time) (filtered time))
      ?_
      (upperTraceIntegrable.add propagationIntegrable)
    intro t membership
    have membershipIcc :
        t ∈ Icc (0 : ℝ) T := by
      simpa [uIcc_of_le (le_of_lt TPos)] using membership
    exact realDoubleTriad_middleDefect_hasDerivAt
      full filtered t
        (fullEvolves t membershipIcc)
        (filteredEvolves t membershipIcc)
  have initialDefect :
      realDoubleTriadMiddlePass (full 0) - filtered 0 = 0 := by
    rw [initialAligned, sub_self]
  rw [← intervalIntegral.integral_add
    upperTraceIntegrable propagationIntegrable]
  rw [endpointFTC, initialDefect, sub_zero]

/-- The ambient filtered ODE is genuinely confined to the `P₅` carrier.
Range membership is generated from the native vector field and aligned
initial state, rather than supplied as a trajectory premise. -/
theorem realDoubleTriad_middleFilteredTrajectory_middlePass
    (filtered : ℝ → RealDoubleTriadState) (T : ℝ)
    (filteredEvolves :
      ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivAt filtered
          (realDoubleTriadMiddleFilteredGenerator
            (1 / 100) (filtered t)) t)
    (initialFiltered :
      realDoubleTriadMiddlePass (filtered 0) = filtered 0) :
    ∀ t ∈ Icc (0 : ℝ) T,
      realDoubleTriadMiddlePass (filtered t) = filtered t := by
  intro t membership
  have derivativeZero :
      ∀ s ∈ uIcc (0 : ℝ) t,
        HasDerivAt
          (fun time =>
            realDoubleTriadMiddlePass (filtered time) -
              filtered time)
          0 s := by
    intro s sMembership
    have sMembershipIccZeroT :
        s ∈ Icc (0 : ℝ) T := by
      have sMembershipIccZeroT' :
          s ∈ Icc (0 : ℝ) t := by
        simpa [uIcc_of_le membership.1] using sMembership
      exact
        ⟨sMembershipIccZeroT'.1,
          le_trans sMembershipIccZeroT'.2 membership.2⟩
    have evolvesAtS :=
      filteredEvolves s sMembershipIccZeroT
    have projectedDerivative :
        HasDerivAt
          (fun time =>
            realDoubleTriadMiddlePass (filtered time))
          (realDoubleTriadMiddlePass
            (realDoubleTriadMiddleFilteredGenerator
              (1 / 100) (filtered s))) s := by
      simpa [realDoubleTriadMiddlePassCLM] using
        ((hasDerivAt_const s
          realDoubleTriadMiddlePassCLM).clm_apply evolvesAtS)
    change HasDerivAt
      ((fun time =>
        realDoubleTriadMiddlePass (filtered time)) - filtered)
      0 s
    simpa using projectedDerivative.sub evolvesAtS
  have zeroIntegrable :
      IntervalIntegrable
        (fun _ : ℝ => (0 : RealDoubleTriadState))
        MeasureTheory.volume 0 t :=
    intervalIntegrable_const
  have zeroFTC :
      (∫ _ in 0..t, (0 : RealDoubleTriadState)) =
        (realDoubleTriadMiddlePass (filtered t) - filtered t) -
          (realDoubleTriadMiddlePass (filtered 0) -
            filtered 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      derivativeZero zeroIntegrable
  have initialDefect :
      realDoubleTriadMiddlePass (filtered 0) - filtered 0 = 0 :=
    sub_eq_zero.mpr initialFiltered
  have terminalDefect :
      realDoubleTriadMiddlePass (filtered t) - filtered t = 0 := by
    simpa [initialDefect] using zeroFTC.symm
  exact sub_eq_zero.mp terminalDefect

/-! ## Scalar finite-time consumers -/

/-- Actual path laws make the scalar defect rate interval-integrable. -/
theorem realDoubleTriad_middleDefectRateTwo_intervalIntegrable
    (full filtered : ℝ → RealDoubleTriadState) (T : ℝ)
    (TNonneg : 0 ≤ T)
    (evolves :
      ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivAt full
            (realDoubleTriadNavierStokesGalerkinGenerator
              (1 / 100) (full t)) t ∧
          HasDerivAt filtered
            (realDoubleTriadMiddleFilteredGenerator
              (1 / 100) (filtered t)) t) :
    IntervalIntegrable
      (fun t =>
        realDoubleTriadMiddleDefectRateTwo
          (1 / 100) (full t) (filtered t))
      MeasureTheory.volume 0 T := by
  have fullContinuous :
      ContinuousOn full (Icc (0 : ℝ) T) := by
    intro t membership
    exact
      (evolves t membership).1.continuousAt.continuousWithinAt
  have filteredContinuous :
      ContinuousOn filtered (Icc (0 : ℝ) T) := by
    intro t membership
    exact
      (evolves t membership).2.continuousAt.continuousWithinAt
  have rateContinuous :
      ContinuousOn
        (fun t =>
          realDoubleTriadMiddleDefectRateTwo
            (1 / 100) (full t) (filtered t))
        (Icc (0 : ℝ) T) := by
    simpa [Function.comp_def] using
      realDoubleTriadMiddleDefectRateTwo_continuous.comp_continuousOn
        (fullContinuous.prodMk filteredContinuous)
  exact rateContinuous.intervalIntegrable_of_Icc TNonneg

/-- A generated pointwise gap gives a strictly positive defect-rate
integral. -/
theorem realDoubleTriad_middleDefectRateTwo_integral_pos
    (full filtered : ℝ → RealDoubleTriadState) (T : ℝ)
    (TPos : 0 < T)
    (rateIntegrable :
      IntervalIntegrable
        (fun t =>
          realDoubleTriadMiddleDefectRateTwo
            (1 / 100) (full t) (filtered t))
        MeasureTheory.volume 0 T)
    (rateGap :
      ∀ t ∈ Icc (0 : ℝ) T,
        9 / 40 <
          realDoubleTriadMiddleDefectRateTwo
            (1 / 100) (full t) (filtered t)) :
    0 <
      ∫ t in 0..T,
        realDoubleTriadMiddleDefectRateTwo
          (1 / 100) (full t) (filtered t) := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    rateIntegrable
  · intro t membership
    have gap :=
      rateGap t ⟨membership.1.le, membership.2.le⟩
    linarith
  · exact TPos

/-- Scalar FTC couples the defect rate back to the actual endpoint
difference. -/
theorem realDoubleTriad_middleDefectRateTwo_FTC
    (full filtered : ℝ → RealDoubleTriadState) (T : ℝ)
    (TNonneg : 0 ≤ T)
    (evolves :
      ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivAt full
            (realDoubleTriadNavierStokesGalerkinGenerator
              (1 / 100) (full t)) t ∧
          HasDerivAt filtered
            (realDoubleTriadMiddleFilteredGenerator
              (1 / 100) (filtered t)) t)
    (rateIntegrable :
      IntervalIntegrable
        (fun t =>
          realDoubleTriadMiddleDefectRateTwo
            (1 / 100) (full t) (filtered t))
        MeasureTheory.volume 0 T) :
    (∫ t in 0..T,
        realDoubleTriadMiddleDefectRateTwo
          (1 / 100) (full t) (filtered t)) =
      (realDoubleTriadMiddlePass (full T) -
          filtered T) 2 -
        (realDoubleTriadMiddlePass (full 0) -
          filtered 0) 2 := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f :=
      fun time =>
        (realDoubleTriadMiddlePass (full time) -
          filtered time) 2)
    (f' :=
      fun time =>
        realDoubleTriadMiddleDefectRateTwo
          (1 / 100) (full time) (filtered time))
    ?_ rateIntegrable
  intro t membership
  have membershipIcc :
      t ∈ Icc (0 : ℝ) T := by
    simpa [uIcc_of_le TNonneg] using membership
  have vectorDerivative :=
    realDoubleTriad_middleDefect_hasDerivAt
      full filtered t
        (evolves t membershipIcc).1
        (evolves t membershipIcc).2
  simpa [realDoubleTriadMiddleDefectRateTwo] using
    ((hasDerivAt_const t
      (ContinuousLinearMap.proj
        (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2)).clm_apply
          vectorDerivative)

/-- FTC consumes an already generated positive defect-rate gap and excludes
the zero endpoint defect.  This is the independent finite-time consumer;
the following corollary supplies all of its hypotheses from the source. -/
theorem realDoubleTriad_middleDefectRateGap_forces_endpointKernelEscape
    (full filtered : ℝ → RealDoubleTriadState) (T : ℝ)
    (TPos : 0 < T)
    (initialAligned :
      realDoubleTriadMiddlePass (full 0) = filtered 0)
    (evolves :
      ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivAt full
            (realDoubleTriadNavierStokesGalerkinGenerator
              (1 / 100) (full t)) t ∧
          HasDerivAt filtered
            (realDoubleTriadMiddleFilteredGenerator
              (1 / 100) (filtered t)) t)
    (rateGap :
      ∀ t ∈ Icc (0 : ℝ) T,
        9 / 40 <
          realDoubleTriadMiddleDefectRateTwo
            (1 / 100) (full t) (filtered t)) :
    0 <
      (realDoubleTriadMiddlePass (full T) -
        filtered T) 2 := by
  have rateIntegrable :=
    realDoubleTriad_middleDefectRateTwo_intervalIntegrable
      full filtered T (le_of_lt TPos) evolves
  have rateIntegralPositive :=
    realDoubleTriad_middleDefectRateTwo_integral_pos
      full filtered T TPos rateIntegrable rateGap
  have defectTwoFTC :=
    realDoubleTriad_middleDefectRateTwo_FTC
      full filtered T (le_of_lt TPos) evolves rateIntegrable
  have initialDefectTwo :
      (realDoubleTriadMiddlePass (full 0) -
        filtered 0) 2 = 0 := by
    rw [initialAligned, sub_self]
    rfl
  rw [initialDefectTwo, sub_zero] at defectTwoFTC
  linarith

end

end TwoDimensionalVorticityDoubleTriadDuhamelPropagationResidual
end SaturationMonoid.NavierStokes
