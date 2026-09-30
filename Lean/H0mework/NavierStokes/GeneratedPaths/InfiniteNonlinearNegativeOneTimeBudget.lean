import H0mework.NavierStokes.WholeSpace.InfiniteNonlinearNegativeSobolev
import H0mework.NavierStokes.GeneratedPaths.FiniteObservedCompactness

/-!
# Infinite nonlinear negative-Sobolev budget along generated scale paths

The source-generated common-time trajectory already carries an exact
finite Galerkin evolution, an actual generated support, and the critical
viscous enstrophy absorption ledger.  This module consumes those facts on
the whole integer lattice:

* finite support identifies the full infinite nonlinear row with a finite
  pair-output readout at every time;
* the whole-lattice negative-one nonlinear mass is therefore integrable;
* the static `H⁻¹` nonlinear estimate is paid by the actual viscous
  gradient integral; and
* every generated critical path receives one time-integrated bound whose
  constant is independent of cutoff, path length, and maximal shell.

No target limit, compactness witness, support-coverage premise, or
continuation witness enters the theorem mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget

open scoped BigOperators ENNReal Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathStretchingBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedPathCommonTimeCompactnessBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev

noncomputable section

/-- Finite inventory of every ordered-pair output generated from `modes`. -/
def finiteVorticityPairOutputSupport
    (modes : Finset IntegerWavevector) :
    Finset IntegerWavevector :=
  (modes.product modes).image fun pair => pair.1 + pair.2

theorem finiteStateVorticityNonlinearCoefficientAt_eq_zero_of_not_mem_pairOutput
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector)
    (outputNotMem :
      output ∉ finiteVorticityPairOutputSupport modes) :
    finiteStateVorticityNonlinearCoefficientAt
        modes state output = 0 := by
  unfold finiteStateVorticityNonlinearCoefficientAt
  apply Finset.sum_eq_zero
  intro first firstMem
  apply Finset.sum_eq_zero
  intro second secondMem
  rw [if_neg]
  intro incidence
  apply outputNotMem
  unfold finiteVorticityPairOutputSupport
  apply Finset.mem_image.mpr
  exact
    ⟨(first, second),
      Finset.mem_product.mpr ⟨firstMem, secondMem⟩,
      incidence⟩

theorem wholeStateVorticityNonlinearCoefficientAt_eq_zero_of_supported
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave : IntegerWavevector,
        wave ∉ modes → state wave = 0)
    (output : IntegerWavevector)
    (outputNotMem :
      output ∉ finiteVorticityPairOutputSupport modes) :
    wholeStateVorticityNonlinearCoefficientAt state output = 0 := by
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    modes state supported output]
  exact
    finiteStateVorticityNonlinearCoefficientAt_eq_zero_of_not_mem_pairOutput
      modes state output outputNotMem

theorem summable_wholeStateVorticityGradientDensity_of_supported
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave : IntegerWavevector,
        wave ∉ modes → state wave = 0) :
    Summable fun wave : IntegerWavevector =>
      integerWaveNormSq wave *
        complexCoordinateAmplitudeSq (state wave) := by
  apply summable_of_hasFiniteSupport
  exact modes.finite_toSet.subset fun wave waveSupport => by
    by_contra waveNotMem
    apply waveSupport
    simp [supported wave waveNotMem,
      complexCoordinateAmplitudeSq]

theorem wholeVorticityEuclideanMass_eq_finite_of_supported
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave : IntegerWavevector,
        wave ∉ modes → state wave = 0) :
    wholeVorticityEuclideanMass state =
      finiteStateVorticityCoefficientEnstrophy modes state := by
  unfold wholeVorticityEuclideanMass
  rw [tsum_eq_sum (s := modes)]
  · unfold finiteStateVorticityCoefficientEnstrophy
    apply Finset.sum_congr rfl
    intro wave waveMem
    rw [vorticityRowAmplitude_sq,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  · intro wave waveNotMem
    simp [vorticityRowAmplitude, supported wave waveNotMem,
      complexCoordinateAmplitudeSq]

theorem wholeStateVorticityGradientMass_eq_finite_of_supported
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave : IntegerWavevector,
        wave ∉ modes → state wave = 0) :
    wholeStateVorticityGradientMass state =
      finiteStateVorticityEnstrophyMass modes state := by
  unfold wholeStateVorticityGradientMass
    finiteStateVorticityEnstrophyMass
  rw [tsum_eq_sum (s := modes)]
  intro wave waveNotMem
  simp [supported wave waveNotMem, complexCoordinateAmplitudeSq]

/-- Finite readout of the full nonlinear negative-one mass for a state
supported on `modes`; the output inventory is the actual pair sumset. -/
def finiteSupportWholeNonlinearNegativeOneMass
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑ output ∈ finiteVorticityPairOutputSupport modes,
    if output = 0 then 0
    else
      ‖finiteStateVorticityNonlinearCoefficientAt
          modes state output‖ ^ 2 /
        integerWaveViscousMultiplier output

theorem wholeStateVorticityNonlinearNegativeOneMass_eq_finiteSupport
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave : IntegerWavevector,
        wave ∉ modes → state wave = 0) :
    wholeStateVorticityNonlinearNegativeOneMass state =
      finiteSupportWholeNonlinearNegativeOneMass modes state := by
  unfold wholeStateVorticityNonlinearNegativeOneMass
  rw [tsum_eq_sum (s := finiteVorticityPairOutputSupport modes)]
  · unfold finiteSupportWholeNonlinearNegativeOneMass
    apply Finset.sum_congr rfl
    intro output outputMem
    unfold wholeStateVorticityNonlinearNegativeOneDensity
    by_cases outputZero : output = 0
    · simp [outputZero]
    · rw [if_neg outputZero]
      rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
        modes state supported output]
      simp [outputZero]
  · intro output outputNotMem
    unfold wholeStateVorticityNonlinearNegativeOneDensity
    by_cases outputZero : output = 0
    · simp [outputZero]
    · rw [if_neg outputZero,
        wholeStateVorticityNonlinearCoefficientAt_eq_zero_of_supported
          modes state supported output outputNotMem]
      simp

theorem finiteSupportWholeNonlinearNegativeOneMass_continuous
    (modes : Finset IntegerWavevector) :
    Continuous
      (finiteSupportWholeNonlinearNegativeOneMass modes) := by
  unfold finiteSupportWholeNonlinearNegativeOneMass
  apply continuous_finsetSum
  intro output outputMem
  by_cases outputZero : output = 0
  · simp only [if_pos outputZero]
    exact continuous_const
  · simp only [if_neg outputZero]
    exact
      (((finiteStateVorticityNonlinearCoefficientAt_contDiff
        modes output).continuous.norm.pow 2).div_const
          (integerWaveViscousMultiplier output))

/-! ## Actual common-time dissipation consumer -/

/-- The actual common-time generated trajectory transports viscous
gradient dissipation into a full infinite-nonlinearity `L²_t H⁻¹_x` bound.
The constant contains no cutoff, path length, or maximal shell. -/
theorem
    GeneratedPathCommonTimeCompactnessBudget.wholeNonlinearNegativeOneTimeBudget_le
    {seed current : RawVorticityFourierSource}
    {arrival : GeneratedIntegerShellReachable seed current}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (budget :
      GeneratedPathCommonTimeCompactnessBudget
        arrival ν θ requestedTime)
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime) :
    (∫ t in (0 : ℝ)..requestedTime,
        wholeStateVorticityNonlinearNegativeOneMass
          (budget.trajectory t)) ≤
      2 * criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            (generatedSupport current) (budget.trajectory 0) ^ 2 /
        criticalEnstrophyAbsorptionCoefficient θ ν := by
  let modes := generatedSupport current
  let trajectory := budget.trajectory
  let initialMass :=
    finiteStateVorticityCoefficientEnstrophy modes (trajectory 0)
  let absorption :=
    criticalEnstrophyAbsorptionCoefficient θ ν
  have absorptionPos : 0 < absorption := by
    exact criticalEnstrophyAbsorptionCoefficient_pos θ θLtOne ν
  have trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime) := by
    intro t tMem
    exact
      ((budget.physicalProperties t tMem).1).continuousAt.continuousWithinAt
  have supportLaw :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        ∀ wave : IntegerWavevector,
          wave ∉ modes → trajectory t wave = 0 := by
    intro t tMem wave waveNotMem
    exact (budget.physicalProperties t tMem).2.1 wave waveNotMem
  have transverseLaw :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        WholeStateTransverse (trajectory t) := by
    intro t tMem wave
    exact (budget.physicalProperties t tMem).2.2.1 wave
  have finiteMassContinuous :
      ContinuousOn
        (fun t =>
          finiteSupportWholeNonlinearNegativeOneMass
            modes (trajectory t))
        (Icc (0 : ℝ) requestedTime) :=
    (finiteSupportWholeNonlinearNegativeOneMass_continuous modes)
      |>.comp_continuousOn trajectoryContinuous
  have wholeMassContinuous :
      ContinuousOn
        (fun t =>
          wholeStateVorticityNonlinearNegativeOneMass
            (trajectory t))
        (Icc (0 : ℝ) requestedTime) := by
    exact finiteMassContinuous.congr fun t tMem =>
      wholeStateVorticityNonlinearNegativeOneMass_eq_finiteSupport
        modes (trajectory t) (supportLaw t tMem)
  have wholeMassIntegrable :
      IntervalIntegrable
        (fun t =>
          wholeStateVorticityNonlinearNegativeOneMass
            (trajectory t))
        volume 0 requestedTime :=
    wholeMassContinuous.intervalIntegrable_of_Icc
      requestedTimePos.le
  have gradientContinuous :
      ContinuousOn
        (fun t =>
          finiteStateVorticityEnstrophyMass
            modes (trajectory t))
        (Icc (0 : ℝ) requestedTime) := by
    intro t tMem
    exact
      (finiteStateVorticityEnstrophyMass_continuousAt_of_hasDerivAt
        modes trajectory t
        (finiteStateVorticityGenerator
          modes ν.coeff (trajectory t))
        (budget.physicalProperties t tMem).1).continuousWithinAt
  have gradientIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVorticityEnstrophyMass
            modes (trajectory t))
        volume 0 requestedTime :=
    gradientContinuous.intervalIntegrable_of_Icc
      requestedTimePos.le
  have initialMassNonneg : 0 ≤ initialMass := by
    dsimp [initialMass]
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have pointwise :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        wholeStateVorticityNonlinearNegativeOneMass
            (trajectory t) ≤
          4 * criticalEnstrophyLatticeConstant * initialMass *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t) := by
    intro t tMem
    have supported := supportLaw t tMem
    have gradientSummable :=
      summable_wholeStateVorticityGradientDensity_of_supported
        modes (trajectory t) supported
    have staticBound :=
      wholeStateVorticityNonlinearNegativeOneMass_le
        (trajectory t) (transverseLaw t tMem) gradientSummable
    rw [wholeStateVorticityGradientMass_eq_finite_of_supported
          modes (trajectory t) supported,
        wholeVorticityEuclideanMass_eq_finite_of_supported
          modes (trajectory t) supported,
        show
          biotSavartSerrinConstant *
              (∑' wave : IntegerWavevector,
                integerWaveCriticalKernel wave) =
            criticalEnstrophyLatticeConstant by rfl]
      at staticBound
    have currentMassLe :
        finiteStateVorticityCoefficientEnstrophy
            modes (trajectory t) ≤
          initialMass := by
      have halfLe := (budget.criticalBarrier t tMem).1
      dsimp [modes, trajectory, initialMass] at halfLe ⊢
      unfold finiteStateVorticityHalfEnstrophy at halfLe
      linarith
    have gradientNonneg :
        0 ≤
          finiteStateVorticityEnstrophyMass
            modes (trajectory t) :=
      finiteStateVorticityEnstrophyMass_nonneg modes _
    calc
      wholeStateVorticityNonlinearNegativeOneMass
          (trajectory t) ≤
        4 * criticalEnstrophyLatticeConstant *
          finiteStateVorticityEnstrophyMass modes (trajectory t) *
          finiteStateVorticityCoefficientEnstrophy
            modes (trajectory t) := by
        simpa [mul_assoc] using staticBound
      _ ≤
        4 * criticalEnstrophyLatticeConstant *
          finiteStateVorticityEnstrophyMass modes (trajectory t) *
          initialMass :=
        mul_le_mul_of_nonneg_left currentMassLe
          (mul_nonneg
            (mul_nonneg (by norm_num)
              criticalEnstrophyLatticeConstant_nonneg)
            gradientNonneg)
      _ =
        4 * criticalEnstrophyLatticeConstant * initialMass *
          finiteStateVorticityEnstrophyMass modes (trajectory t) := by
        ring
  have rhsIntegrable :
      IntervalIntegrable
        (fun t =>
          4 * criticalEnstrophyLatticeConstant * initialMass *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t))
        volume 0 requestedTime :=
    gradientIntegrable.const_mul
      (4 * criticalEnstrophyLatticeConstant * initialMass)
  have integratedPointwise :=
    intervalIntegral.integral_mono_on
      requestedTimePos.le wholeMassIntegrable rhsIntegrable pointwise
  rw [intervalIntegral.integral_const_mul] at integratedPointwise
  have terminalHalfNonneg :
      0 ≤
        finiteStateVorticityHalfEnstrophy
          modes (trajectory requestedTime) :=
    finiteStateVorticityHalfEnstrophy_nonneg modes _
  have absorbedWithoutTerminal :
      absorption *
          (∫ t in (0 : ℝ)..requestedTime,
            finiteStateVorticityEnstrophyMass
              modes (trajectory t)) ≤
        finiteStateVorticityHalfEnstrophy
          modes (trajectory 0) := by
    dsimp [absorption, modes, trajectory]
    exact budget.enstrophyAbsorption.trans
      (sub_le_self _ terminalHalfNonneg)
  have gradientIntegralLe :
      (∫ t in (0 : ℝ)..requestedTime,
        finiteStateVorticityEnstrophyMass
          modes (trajectory t)) ≤
        finiteStateVorticityHalfEnstrophy
            modes (trajectory 0) /
          absorption := by
    exact (le_div_iff₀ absorptionPos).2 (by
      simpa [mul_comm] using absorbedWithoutTerminal)
  calc
    (∫ t in (0 : ℝ)..requestedTime,
        wholeStateVorticityNonlinearNegativeOneMass
          (budget.trajectory t)) ≤
      4 * criticalEnstrophyLatticeConstant * initialMass *
        (∫ t in (0 : ℝ)..requestedTime,
          finiteStateVorticityEnstrophyMass
            modes (trajectory t)) := by
      simpa [trajectory] using integratedPointwise
    _ ≤
      4 * criticalEnstrophyLatticeConstant * initialMass *
        (finiteStateVorticityHalfEnstrophy
            modes (trajectory 0) / absorption) :=
      mul_le_mul_of_nonneg_left gradientIntegralLe
        (mul_nonneg
          (mul_nonneg (by norm_num)
            criticalEnstrophyLatticeConstant_nonneg)
          initialMassNonneg)
    _ =
      2 * criticalEnstrophyLatticeConstant * initialMass ^ 2 /
        absorption := by
      unfold finiteStateVorticityHalfEnstrophy
      field_simp [absorptionPos.ne']
      ring
    _ =
      2 * criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            (generatedSupport current) (budget.trajectory 0) ^ 2 /
        criticalEnstrophyAbsorptionCoefficient θ ν := by
      rfl

/-- Uniform family version: every actual source-generated critical path has
the same full infinite-nonlinearity time budget, depending only on the
shared critical margin, viscosity, and requested interval regime. -/
theorem GeneratedCriticalScalePath.wholeNonlinearNegativeOneTimeBudget_le_uniform
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (path : GeneratedCriticalScalePath ν θ) :
    (∫ t in (0 : ℝ)..requestedTime,
        wholeStateVorticityNonlinearNegativeOneMass
          ((path.commonTimeBudget
            θLtOne requestedTimePos).trajectory t)) ≤
      2 * criticalEnstrophyLatticeConstant *
          criticalCoefficientEnstrophyCeiling ν θ ^ 2 /
        criticalEnstrophyAbsorptionCoefficient θ ν := by
  let budget :=
    path.commonTimeBudget θLtOne requestedTimePos
  have base :=
    SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget.GeneratedPathCommonTimeCompactnessBudget.wholeNonlinearNegativeOneTimeBudget_le
      budget θLtOne requestedTimePos
  have initialMassLe :
      finiteStateVorticityCoefficientEnstrophy
          (generatedSupport path.current)
          (budget.trajectory 0) ≤
        criticalCoefficientEnstrophyCeiling ν θ := by
    rw [budget.initial]
    exact path.initialEnstrophy_le_ceiling
  have initialMassNonneg :
      0 ≤
        finiteStateVorticityCoefficientEnstrophy
          (generatedSupport path.current)
          (budget.trajectory 0) := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have squareLe :
      finiteStateVorticityCoefficientEnstrophy
            (generatedSupport path.current)
            (budget.trajectory 0) ^ 2 ≤
        criticalCoefficientEnstrophyCeiling ν θ ^ 2 :=
    (sq_le_sq₀ initialMassNonneg
      (criticalCoefficientEnstrophyCeiling_nonneg ν θ)).2
      initialMassLe
  have absorptionPos :
      0 < criticalEnstrophyAbsorptionCoefficient θ ν :=
    criticalEnstrophyAbsorptionCoefficient_pos θ θLtOne ν
  exact base.trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left squareLe
        (mul_nonneg (by norm_num)
          criticalEnstrophyLatticeConstant_nonneg))
      absorptionPos.le)

end

end ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
end NavierStokes
end SaturationMonoid
