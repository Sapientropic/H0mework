import H0mework.NavierStokes.Galerkin.CriticalGronwall

/-!
# Cutoff-independent critical enstrophy barrier

The global three-dimensional lattice kernel turns the finite Galerkin
enstrophy inequality into an invariant-region statement.  The transported
residual is

```text
h(t) = K₃ * Y(t) - ν² * (2π)²,
```

and the actual Galerkin update satisfies

```text
h'(t) ≤ (K₃ / ν) * Z(t) * h(t).
```

The variable-coefficient integrating factor transports this defect with the
actual accumulated gradient mass.  Since its exponential is positive, a
nonpositive initial residual cannot cross zero.  Once the barrier is
preserved, the original half-enstrophy derivative is nonpositive.

No mode count, maximum frequency, target shell, path coverage, or
pre-supplied derivative bound occurs in the theorem mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier

open scoped BigOperators Topology ENNReal

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyRate
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalGronwall

noncomputable section

/-- The cutoff-independent three-dimensional constant carried by the
Biot--Savart estimate and the summable integer lattice kernel. -/
def criticalEnstrophyLatticeConstant : ℝ :=
  biotSavartSerrinConstant *
    (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave)

theorem criticalEnstrophyLatticeConstant_nonneg :
    0 ≤ criticalEnstrophyLatticeConstant := by
  exact
    mul_nonneg biotSavartSerrinConstant_nonneg
      integerWaveCriticalKernel_tsum_nonneg

theorem criticalEnstrophyLatticeConstant_pos :
    0 < criticalEnstrophyLatticeConstant := by
  have kernelPositive :
      0 <
        ∑' wave : IntegerWavevector,
          integerWaveCriticalKernel wave := by
    let e0 : IntegerWavevector :=
      fun coordinate => if coordinate = 0 then 1 else 0
    have normEq : integerWaveNormSq e0 = 1 := by
      unfold integerWaveNormSq e0
      simp
    have termPositive :
        0 < integerWaveCriticalKernel e0 := by
      unfold integerWaveCriticalKernel
      rw [normEq]
      norm_num
    exact
      summable_integerWaveCriticalKernel.tsum_pos
        (fun wave => integerWaveCriticalKernel_nonneg wave)
        e0 termPositive
  exact
    mul_pos biotSavartSerrinConstant_pos kernelPositive

/-- The threshold defect whose sign records whether coefficient enstrophy
lies in the cutoff-independent viscous invariant region. -/
def finiteStateVorticityCriticalBarrierDefect
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) : ℝ :=
  criticalEnstrophyLatticeConstant *
      finiteStateVorticityCoefficientEnstrophy modes state -
    ν ^ 2 * (2 * Real.pi) ^ 2

/-- The actual finite Galerkin update transports the critical barrier defect
by a coefficient times the defect itself.  This is the pointwise commuting
law used by the interval barrier below. -/
theorem finiteStateVorticityCriticalBarrierDefect_hasDerivAt_and_rate_le_self
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : ℝ)
    (νPos : 0 < ν)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (evolves :
      HasDerivAt trajectory
        (finiteStateVorticityGenerator modes ν (trajectory t)) t)
    (reality : FiniteStateFourierReality (trajectory t))
    (transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ trajectory t wave = 0) :
    HasDerivAt
        (fun time =>
          finiteStateVorticityCriticalBarrierDefect
            modes ν (trajectory time))
        (2 * criticalEnstrophyLatticeConstant *
          (finiteStateVorticityStretchingWork modes (trajectory t) -
            ν * (2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass
                modes (trajectory t))) t ∧
      2 * criticalEnstrophyLatticeConstant *
          (finiteStateVorticityStretchingWork modes (trajectory t) -
            ν * (2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) ≤
        (criticalEnstrophyLatticeConstant *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t) / ν) *
          finiteStateVorticityCriticalBarrierDefect
            modes ν (trajectory t) := by
  have pointwise :=
    finiteStateVorticityHalfEnstrophy_hasDerivAt_and_le_globalCriticalRate
      modes negClosed ν νPos trajectory t evolves reality transverse
  constructor
  · have scaledDerivative :=
      pointwise.1.const_mul
        (2 * criticalEnstrophyLatticeConstant)
    have functionEq :
        (fun time =>
          finiteStateVorticityCriticalBarrierDefect
            modes ν (trajectory time)) =
        (fun time =>
          2 * criticalEnstrophyLatticeConstant *
              finiteStateVorticityHalfEnstrophy
                modes (trajectory time) -
            ν ^ 2 * (2 * Real.pi) ^ 2) := by
      funext time
      unfold finiteStateVorticityCriticalBarrierDefect
        finiteStateVorticityHalfEnstrophy
      ring
    rw [functionEq]
    exact scaledDerivative.sub_const _
  · have scaleNonneg :
        0 ≤ 2 * criticalEnstrophyLatticeConstant :=
      mul_nonneg (by norm_num)
        criticalEnstrophyLatticeConstant_nonneg
    have scaledRate :=
      mul_le_mul_of_nonneg_left pointwise.2 scaleNonneg
    calc
      2 * criticalEnstrophyLatticeConstant *
          (finiteStateVorticityStretchingWork modes (trajectory t) -
            ν * (2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) ≤
        2 * criticalEnstrophyLatticeConstant *
          (-(ν / 2) *
              ((2 * Real.pi) ^ 2 *
                finiteStateVorticityEnstrophyMass
                  modes (trajectory t)) +
            (ν⁻¹ / 2) *
              (criticalEnstrophyLatticeConstant *
                finiteStateVorticityEnstrophyMass
                  modes (trajectory t)) *
              finiteStateVorticityCoefficientEnstrophy
                modes (trajectory t)) :=
        scaledRate
      _ =
        (criticalEnstrophyLatticeConstant *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t) / ν) *
          finiteStateVorticityCriticalBarrierDefect
            modes ν (trajectory t) := by
        unfold finiteStateVorticityCriticalBarrierDefect
        field_simp [ne_of_gt νPos]
        ring

/-- On any compact interval of an actual reality-preserving, transverse
finite Galerkin solution, subcritical initial enstrophy cannot cross the
cutoff-independent critical threshold. -/
theorem finiteStateVorticityCriticalBarrierDefect_nonposOn
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : ℝ)
    (νPos : 0 < ν)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (evolves :
      ∀ t ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator modes ν (trajectory t)) t)
    (reality :
      ∀ t ∈ Icc a b,
        FiniteStateFourierReality (trajectory t))
    (transverse :
      ∀ t ∈ Icc a b,
        ∀ wave ∈ modes,
          complexWavevector wave ⬝ᵥ trajectory t wave = 0)
    (initialSmall :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            modes (trajectory a) ≤
        ν ^ 2 * (2 * Real.pi) ^ 2) :
    ∀ t ∈ Icc a b,
      finiteStateVorticityCriticalBarrierDefect
        modes ν (trajectory t) ≤ 0 := by
  let defect : ℝ → ℝ :=
    fun time =>
      finiteStateVorticityCriticalBarrierDefect
        modes ν (trajectory time)
  let exactRate : ℝ → ℝ :=
    fun time =>
      2 * criticalEnstrophyLatticeConstant *
        (finiteStateVorticityStretchingWork modes (trajectory time) -
          ν * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass
              modes (trajectory time))
  let coefficient : ℝ → ℝ :=
    fun time =>
      criticalEnstrophyLatticeConstant *
        finiteStateVorticityEnstrophyMass
          modes (trajectory time) / ν
  have defectDerivative :
      ∀ t ∈ Icc a b,
        HasDerivAt defect (exactRate t) t := by
    intro t tMem
    exact
      (finiteStateVorticityCriticalBarrierDefect_hasDerivAt_and_rate_le_self
        modes negClosed ν νPos trajectory t
        (evolves t tMem) (reality t tMem)
        (transverse t tMem)).1
  have coefficientContinuous :
      ContinuousOn coefficient (Icc a b) := by
    intro t tMem
    exact
      ((finiteStateVorticityEnstrophyMass_continuousAt_of_hasDerivAt
        modes trajectory t
        (finiteStateVorticityGenerator modes ν (trajectory t))
        (evolves t tMem)).const_mul
          criticalEnstrophyLatticeConstant).div_const ν
        |>.continuousWithinAt
  have initialDefectNonpos : defect a ≤ 0 := by
    dsimp [defect]
    unfold finiteStateVorticityCriticalBarrierDefect
    linarith
  have transportedUpper :=
    le_initial_mul_exp_integral_of_hasDerivAt_le_mul
      defectDerivative coefficientContinuous
      (fun t tMem =>
        (finiteStateVorticityCriticalBarrierDefect_hasDerivAt_and_rate_le_self
          modes negClosed ν νPos trajectory t
          (evolves t tMem) (reality t tMem)
          (transverse t tMem)).2)
  intro t tMem
  exact (transportedUpper t tMem).trans
    (mul_nonpos_of_nonpos_of_nonneg
      initialDefectNonpos (Real.exp_nonneg _))

/-- The invariant-region barrier forces the actual half-enstrophy to be
nonincreasing throughout the same Galerkin existence interval. -/
theorem finiteStateVorticityHalfEnstrophy_le_initial_of_criticalSmall
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : ℝ)
    (νPos : 0 < ν)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (evolves :
      ∀ t ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator modes ν (trajectory t)) t)
    (reality :
      ∀ t ∈ Icc a b,
        FiniteStateFourierReality (trajectory t))
    (transverse :
      ∀ t ∈ Icc a b,
        ∀ wave ∈ modes,
          complexWavevector wave ⬝ᵥ trajectory t wave = 0)
    (initialSmall :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            modes (trajectory a) ≤
        ν ^ 2 * (2 * Real.pi) ^ 2) :
    ∀ t ∈ Icc a b,
      finiteStateVorticityHalfEnstrophy modes (trajectory t) ≤
          finiteStateVorticityHalfEnstrophy modes (trajectory a) ∧
        finiteStateVorticityCriticalBarrierDefect
          modes ν (trajectory t) ≤ 0 := by
  have barrier :=
    finiteStateVorticityCriticalBarrierDefect_nonposOn
      modes negClosed ν νPos trajectory a b
      evolves reality transverse initialSmall
  let halfEnstrophy : ℝ → ℝ :=
    fun time =>
      finiteStateVorticityHalfEnstrophy
        modes (trajectory time)
  let exactRate : ℝ → ℝ :=
    fun time =>
      finiteStateVorticityStretchingWork modes (trajectory time) -
        ν * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass
            modes (trajectory time)
  have halfDerivative :
      ∀ t ∈ Icc a b,
        HasDerivAt halfEnstrophy (exactRate t) t := by
    intro t tMem
    exact
      (finiteStateVorticityHalfEnstrophy_hasDerivAt_and_le_globalCriticalRate
        modes negClosed ν νPos trajectory t
        (evolves t tMem) (reality t tMem)
        (transverse t tMem)).1
  have rateNonpos :
      ∀ t ∈ Ico a b,
        exactRate t ≤ 0 := by
    intro t tMem
    have pointwise :=
      finiteStateVorticityCriticalBarrierDefect_hasDerivAt_and_rate_le_self
        modes negClosed ν νPos trajectory t
        (evolves t (mem_Icc_of_Ico tMem))
        (reality t (mem_Icc_of_Ico tMem))
        (transverse t (mem_Icc_of_Ico tMem))
    have coefficientNonneg :
        0 ≤
          criticalEnstrophyLatticeConstant *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t) / ν := by
      exact div_nonneg
        (mul_nonneg
          criticalEnstrophyLatticeConstant_nonneg
          (finiteStateVorticityEnstrophyMass_nonneg
            modes (trajectory t)))
        νPos.le
    have scaledRateNonpos :
        2 * criticalEnstrophyLatticeConstant *
            exactRate t ≤
          0 := by
      exact pointwise.2.trans
        (mul_nonpos_of_nonneg_of_nonpos
          coefficientNonneg
          (barrier t (mem_Icc_of_Ico tMem)))
    nlinarith [criticalEnstrophyLatticeConstant_pos]
  have halfContinuous :
      ContinuousOn halfEnstrophy (Icc a b) :=
    HasDerivAt.continuousOn halfDerivative
  have halfLeInitial :
      ∀ t ∈ Icc a b,
        halfEnstrophy t ≤ halfEnstrophy a := by
    intro t tMem
    apply image_le_of_deriv_right_le_deriv_boundary
      (B := fun _ => halfEnstrophy a)
      (B' := fun _ => 0)
      halfContinuous
      (fun time timeMem =>
        (halfDerivative time
          (mem_Icc_of_Ico timeMem)).hasDerivWithinAt)
      le_rfl
      continuousOn_const
      (fun time _ =>
        (hasDerivAt_const time
          (halfEnstrophy a)).hasDerivWithinAt)
      rateNonpos
      tMem
  intro t tMem
  exact ⟨halfLeInitial t tMem, barrier t tMem⟩

/-- A raw finite Fourier source whose generated initial state is below the
critical threshold produces an actual positive-time Galerkin trajectory
which preserves the barrier and has nonincreasing half-enstrophy.  The
trajectory, transversality, and Fourier reality are generated internally,
not supplied as certificate fields. -/
theorem generatedSource_criticalBarrier_and_halfEnstrophy_nonincrease
    (source : RawVorticityFourierSource)
    (ν : ℝ)
    (νPos : 0 < ν)
    (initialSmall :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            (generatedSupport source)
            (generatedComplexVorticityState source
              (generatedSupport source)) ≤
        ν ^ 2 * (2 * Real.pi) ^ 2) :
    ∃ (trajectory : ℝ → ComplexVorticityHilbertState)
        (physicalTime : ℝ),
      0 < physicalTime ∧
        trajectory 0 =
          generatedComplexVorticityState source
            (generatedSupport source) ∧
        ∀ t ∈ Icc (0 : ℝ) physicalTime,
          finiteStateVorticityHalfEnstrophy
              (generatedSupport source) (trajectory t) ≤
              finiteStateVorticityHalfEnstrophy
                (generatedSupport source) (trajectory 0) ∧
            finiteStateVorticityCriticalBarrierDefect
              (generatedSupport source) ν (trajectory t) ≤ 0 := by
  obtain
      ⟨trajectory, physicalTime, physicalTimePos,
        initial, generatedLaw⟩ :=
    generatedSource_transverseRealityLocalTrajectory source ν
  have negClosed :
      ∀ wave, wave ∈ generatedSupport source →
        waveNeg wave ∈ generatedSupport source := by
    intro wave waveMem
    exact generatedSupport_waveNeg_mem source waveMem
  have initialSmallActual :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            (generatedSupport source) (trajectory 0) ≤
        ν ^ 2 * (2 * Real.pi) ^ 2 := by
    rw [initial]
    exact initialSmall
  have intervalConclusion :=
    finiteStateVorticityHalfEnstrophy_le_initial_of_criticalSmall
      (generatedSupport source) negClosed ν νPos trajectory
      0 physicalTime
      (fun t tMem => (generatedLaw t tMem).1)
      (fun t tMem => (generatedLaw t tMem).2.2.2)
      (fun t tMem wave _ =>
        (generatedLaw t tMem).2.2.1 wave)
      initialSmallActual
  exact
    ⟨trajectory, physicalTime, physicalTimePos,
      initial, intervalConclusion⟩

end

end ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
end NavierStokes
end SaturationMonoid
