import H0mework.NavierStokes.WholeSpace.InfiniteFixedWaveWeakCarrier

/-!
# Transverse space-time nonlinear Fourier rows

The whole transverse Fourier carrier is installed as a closed complex
subspace, then lifted to its natural time-`L²` carrier.  The actual infinite
quadratic Fourier row maps this carrier continuously into time `L¹`, with a
cutoff-independent local Lipschitz bound.

The inclusion into the ambient space-time carrier is an isometry.  Hence a
strong ambient limit of actual transverse paths lifts to a strong transverse
limit, and every independently constructed nonlinear-row limit is forced by
uniqueness to equal the row evaluated on that same limit.  No target
trajectory, tail-silence certificate, cutoff coverage, or continuation
conclusion is assumed.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow

open scoped ENNReal Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier

noncomputable section

/-- The whole transverse carrier as an actual complex linear subspace. -/
def wholeTransverseVorticitySubmodule :
    Submodule ℂ ComplexVorticityHilbertState where
  carrier := {state | WholeStateTransverse state}
  zero_mem' := by
    intro wave
    simp
  add_mem' := by
    intro left right leftTransverse rightTransverse wave
    simp [dotProduct_add, leftTransverse wave, rightTransverse wave]
  smul_mem' := by
    intro coefficient state stateTransverse wave
    simp [dotProduct_smul, stateTransverse wave]

theorem wholeTransverseVorticitySubmodule_isClosed :
    IsClosed
      (wholeTransverseVorticitySubmodule :
        Set ComplexVorticityHilbertState) := by
  have carrierEq :
      (wholeTransverseVorticitySubmodule :
          Set ComplexVorticityHilbertState) =
        ⋂ wave : IntegerWavevector,
          {state : ComplexVorticityHilbertState |
            complexWavevector wave ⬝ᵥ state wave = 0} := by
    ext state
    simp [wholeTransverseVorticitySubmodule,
      WholeStateTransverse]
  rw [carrierEq]
  apply isClosed_iInter
  intro wave
  exact isClosed_eq
    (continuous_const.dotProduct
      ((lp.evalCLM ℂ
        (fun _ : IntegerWavevector =>
          ComplexCoordinateVector)
        2 wave).continuous))
    continuous_const

instance wholeTransverseVorticitySubmodule.instIsClosed :
    IsClosed
      (wholeTransverseVorticitySubmodule :
        Set ComplexVorticityHilbertState) :=
  wholeTransverseVorticitySubmodule_isClosed

instance wholeTransverseVorticitySubmodule.instCompleteSpace :
    CompleteSpace ↥wholeTransverseVorticitySubmodule :=
  IsClosed.completeSpace_coe

/-- Whole transverse vorticity paths in the natural time-`L²` carrier. -/
abbrev TransverseSpaceTimeState (requestedTime : ℝ) :=
  ↥(MeasureTheory.Lp (↥wholeTransverseVorticitySubmodule) 2
    (commonTimeMeasure requestedTime))

/-- Actual pointwise infinite quadratic Fourier row of a transverse
space-time state. -/
def transverseSpaceTimeNonlinearRowFunction
    {requestedTime : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    ComplexCoordinateVector :=
  wholeStateVorticityNonlinearCoefficientAt
    (state time).1 output

theorem transverseSpaceTimeNonlinearRowFunction_aestronglyMeasurable
    {requestedTime : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (output : IntegerWavevector) :
    AEStronglyMeasurable
      (transverseSpaceTimeNonlinearRowFunction state output)
      (commonTimeMeasure requestedTime) := by
  exact
    (wholeStateVorticityNonlinearCoefficientAt_continuous output)
      |>.comp_aestronglyMeasurable
          (MeasureTheory.Lp.aestronglyMeasurable state)

theorem transverseSpaceTimeNonlinearRowFunction_integrable
    {requestedTime : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (output : IntegerWavevector) :
    Integrable
      (transverseSpaceTimeNonlinearRowFunction state output)
      (commonTimeMeasure requestedTime) := by
  let angular : ℝ :=
    6 * Real.sqrt (integerWaveNormSq output)
  have squareIntegrable :
      Integrable
        (fun time : Icc (0 : ℝ) requestedTime =>
          ‖state time‖ ^ 2)
        (commonTimeMeasure requestedTime) :=
    (MeasureTheory.Lp.memLp state).integrable_norm_pow
      (by norm_num)
  have majorantIntegrable :
      Integrable
        (fun time : Icc (0 : ℝ) requestedTime =>
          angular * ‖state time‖ ^ 2)
        (commonTimeMeasure requestedTime) :=
    squareIntegrable.const_mul angular
  apply Integrable.mono' majorantIntegrable
    (transverseSpaceTimeNonlinearRowFunction_aestronglyMeasurable
      state output)
  apply Eventually.of_forall
  intro time
  simpa [transverseSpaceTimeNonlinearRowFunction,
    ← wholeStateVorticityBilinearCoefficientAt_self,
    angular, pow_two, mul_assoc] using
      wholeStateVorticityBilinearCoefficientAt_norm_le
        (state time).1 (state time).1
        (state time).2 output

/-- Pointwise whole-lattice nonlinear row installed in time `L¹`. -/
def transverseSpaceTimeNonlinearRow
    {requestedTime : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (output : IntegerWavevector) :
    NonlinearRowSpaceTimeState requestedTime :=
  (memLp_one_iff_integrable.mpr
    (transverseSpaceTimeNonlinearRowFunction_integrable
      state output)).toLp
        (transverseSpaceTimeNonlinearRowFunction state output)

theorem transverseSpaceTimeNonlinearRow_coeFn
    {requestedTime : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (output : IntegerWavevector) :
    transverseSpaceTimeNonlinearRow state output =ᵐ[
        commonTimeMeasure requestedTime]
      transverseSpaceTimeNonlinearRowFunction state output := by
  exact
    (memLp_one_iff_integrable.mpr
      (transverseSpaceTimeNonlinearRowFunction_integrable
        state output)).coeFn_toLp

/-! ## Faithful inclusion in the whole state carrier -/

/-- Forget only the proof of transversality, pointwise in time. -/
def transverseSpaceTimeInclusion
    (requestedTime : ℝ) :
    TransverseSpaceTimeState requestedTime →L[ℂ]
      SpaceTimeState requestedTime :=
  wholeTransverseVorticitySubmodule.subtypeL.compLpL
    2 (commonTimeMeasure requestedTime)

theorem transverseSpaceTimeInclusion_coeFn
    (requestedTime : ℝ)
    (state : TransverseSpaceTimeState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      transverseSpaceTimeInclusion requestedTime state time =
        (state time).1 := by
  exact
    wholeTransverseVorticitySubmodule.subtypeL.coeFn_compLpL
      state

theorem transverseSpaceTimeInclusion_norm
    (requestedTime : ℝ)
    (state : TransverseSpaceTimeState requestedTime) :
    ‖transverseSpaceTimeInclusion requestedTime state‖ =
      ‖state‖ := by
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [
    transverseSpaceTimeInclusion_coeFn requestedTime state] with
      time inclusionEq
  rw [inclusionEq]
  rfl

theorem transverseSpaceTime_norm_sq_eq_integral
    (requestedTime : ℝ)
    (state : TransverseSpaceTimeState requestedTime) :
    ‖state‖ ^ 2 =
      ∫ time,
        ‖state time‖ ^ 2 ∂(commonTimeMeasure requestedTime) := by
  rw [MeasureTheory.Lp.norm_def]
  rw [MeasureTheory.toReal_eLpNorm
    (MeasureTheory.Lp.aestronglyMeasurable state)]
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
    (p := (2 : ℝ≥0∞)) (by norm_num) (by simp)
    (MeasureTheory.Lp.aestronglyMeasurable state)]
  norm_num
  have powerIdentity :
      ((∫ time,
          ‖state time‖ ^ 2 ∂(commonTimeMeasure requestedTime)) ^
            ((2 : ℝ)⁻¹)) ^ 2 =
        ∫ time,
          ‖state time‖ ^ 2 ∂(commonTimeMeasure requestedTime) :=
    Real.rpow_inv_natCast_pow (n := 2)
      (integral_nonneg fun _ => sq_nonneg _) (by norm_num)
  convert powerIdentity using 1
  all_goals norm_num

theorem transverseSpaceTime_integral_norm_mul_norm_le
    (requestedTime : ℝ)
    (left right : TransverseSpaceTimeState requestedTime) :
    (∫ time,
        ‖left time‖ * ‖right time‖
          ∂(commonTimeMeasure requestedTime)) ≤
      ‖left‖ * ‖right‖ := by
  have leftMem :
      MemLp (fun time => left time)
        (ENNReal.ofReal (2 : ℝ))
        (commonTimeMeasure requestedTime) := by
    simpa using MeasureTheory.Lp.memLp left
  have rightMem :
      MemLp (fun time => right time)
        (ENNReal.ofReal (2 : ℝ))
        (commonTimeMeasure requestedTime) := by
    simpa using MeasureTheory.Lp.memLp right
  have cauchy :=
    integral_mul_norm_le_Lp_mul_Lq
      Real.HolderConjugate.two_two
      leftMem rightMem
  have leftIntegral :
      (∫ time,
          ‖((left time : ↥wholeTransverseVorticitySubmodule) :
              ComplexVorticityHilbertState)‖ ^ 2
            ∂(commonTimeMeasure requestedTime)) =
        ‖left‖ ^ 2 := by
    simpa using
      (transverseSpaceTime_norm_sq_eq_integral
        requestedTime left).symm
  have rightIntegral :
      (∫ time,
          ‖((right time : ↥wholeTransverseVorticitySubmodule) :
              ComplexVorticityHilbertState)‖ ^ 2
            ∂(commonTimeMeasure requestedTime)) =
        ‖right‖ ^ 2 := by
    simpa using
      (transverseSpaceTime_norm_sq_eq_integral
        requestedTime right).symm
  norm_num [Real.rpow_two] at cauchy
  rw [leftIntegral, rightIntegral] at cauchy
  norm_num [Real.sqrt_eq_rpow] at cauchy ⊢
  have leftRoot :
      (‖left‖ ^ 2) ^ (1 / 2 : ℝ) = ‖left‖ := by
    have rootIdentity :=
      Real.pow_rpow_inv_natCast
        (norm_nonneg left) (by norm_num : (2 : ℕ) ≠ 0)
    norm_num at rootIdentity ⊢
    exact rootIdentity
  have rightRoot :
      (‖right‖ ^ 2) ^ (1 / 2 : ℝ) = ‖right‖ := by
    have rootIdentity :=
      Real.pow_rpow_inv_natCast
        (norm_nonneg right) (by norm_num : (2 : ℕ) ≠ 0)
    norm_num at rootIdentity ⊢
    exact rootIdentity
  simpa only [leftRoot, rightRoot] using cauchy

theorem transverseSpaceTimeNonlinearRow_sub_norm_eq_integral
    {requestedTime : ℝ}
    (left right : TransverseSpaceTimeState requestedTime)
    (output : IntegerWavevector) :
    ‖transverseSpaceTimeNonlinearRow left output -
        transverseSpaceTimeNonlinearRow right output‖ =
      ∫ time,
        ‖wholeStateVorticityNonlinearCoefficientAt
              (left time).1 output -
            wholeStateVorticityNonlinearCoefficientAt
              (right time).1 output‖
        ∂(commonTimeMeasure requestedTime) := by
  rw [nonlinearRowSpaceTimeState_norm_eq_integral]
  have subAE :=
    MeasureTheory.Lp.coeFn_sub
      (transverseSpaceTimeNonlinearRow left output)
      (transverseSpaceTimeNonlinearRow right output)
  apply integral_congr_ae
  filter_upwards [
    subAE,
    transverseSpaceTimeNonlinearRow_coeFn left output,
    transverseSpaceTimeNonlinearRow_coeFn right output] with
      time subEq leftEq rightEq
  rw [subEq]
  change
    ‖transverseSpaceTimeNonlinearRow left output time -
        transverseSpaceTimeNonlinearRow right output time‖ = _
  rw [leftEq, rightEq]
  rfl

theorem transverseSpaceTimeNonlinearRow_sub_norm_le
    {requestedTime : ℝ}
    (left right : TransverseSpaceTimeState requestedTime)
    (output : IntegerWavevector) :
    ‖transverseSpaceTimeNonlinearRow left output -
        transverseSpaceTimeNonlinearRow right output‖ ≤
      6 * Real.sqrt (integerWaveNormSq output) *
        ‖left - right‖ * (‖left‖ + ‖right‖) := by
  rw [transverseSpaceTimeNonlinearRow_sub_norm_eq_integral]
  let angular : ℝ :=
    6 * Real.sqrt (integerWaveNormSq output)
  have differenceLeftIntegrable :
      Integrable
        (fun time =>
          ‖(left - right) time‖ * ‖left time‖)
        (commonTimeMeasure requestedTime) := by
    change
      Integrable
        ((fun time => ‖(left - right) time‖) *
          fun time => ‖left time‖)
        (commonTimeMeasure requestedTime)
    exact
      (MeasureTheory.Lp.memLp (left - right)).norm.integrable_mul
        (MeasureTheory.Lp.memLp left).norm
  have differenceRightIntegrable :
      Integrable
        (fun time =>
          ‖(left - right) time‖ * ‖right time‖)
        (commonTimeMeasure requestedTime) := by
    change
      Integrable
        ((fun time => ‖(left - right) time‖) *
          fun time => ‖right time‖)
        (commonTimeMeasure requestedTime)
    exact
      (MeasureTheory.Lp.memLp (left - right)).norm.integrable_mul
        (MeasureTheory.Lp.memLp right).norm
  have nonlinearDifferenceIntegrable :
      Integrable
        (fun time =>
          ‖wholeStateVorticityNonlinearCoefficientAt
                (left time).1 output -
              wholeStateVorticityNonlinearCoefficientAt
                (right time).1 output‖)
        (commonTimeMeasure requestedTime) :=
    ((transverseSpaceTimeNonlinearRowFunction_integrable
        left output).sub
      (transverseSpaceTimeNonlinearRowFunction_integrable
        right output)).norm
  have differenceAE :=
    MeasureTheory.Lp.coeFn_sub left right
  have pointwise :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        ‖wholeStateVorticityNonlinearCoefficientAt
              (left time).1 output -
            wholeStateVorticityNonlinearCoefficientAt
              (right time).1 output‖ ≤
          angular *
            (‖(left - right) time‖ * ‖left time‖ +
              ‖(left - right) time‖ * ‖right time‖) := by
    filter_upwards [differenceAE] with time differenceEq
    have base :=
      wholeStateVorticityNonlinearCoefficientAt_sub_norm_le
        (left time).1 (right time).1
        (left time).2 (right time).2 output
    have differenceNorm :
        ‖(left - right) time‖ =
          ‖(left time).1 - (right time).1‖ := by
      rw [differenceEq]
      rfl
    rw [differenceNorm]
    simpa [angular, mul_add, mul_assoc] using base
  have angularNonneg : 0 ≤ angular := by
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  calc
    (∫ time,
        ‖wholeStateVorticityNonlinearCoefficientAt
              (left time).1 output -
            wholeStateVorticityNonlinearCoefficientAt
              (right time).1 output‖
        ∂(commonTimeMeasure requestedTime)) ≤
        ∫ time,
          angular *
            (‖(left - right) time‖ * ‖left time‖ +
              ‖(left - right) time‖ * ‖right time‖)
          ∂(commonTimeMeasure requestedTime) := by
      exact integral_mono_ae
        nonlinearDifferenceIntegrable
        ((differenceLeftIntegrable.add
          differenceRightIntegrable).const_mul angular)
        pointwise
    _ =
        angular *
          ((∫ time,
              ‖(left - right) time‖ * ‖left time‖
              ∂(commonTimeMeasure requestedTime)) +
            ∫ time,
              ‖(left - right) time‖ * ‖right time‖
              ∂(commonTimeMeasure requestedTime)) := by
      rw [integral_const_mul, integral_add
        differenceLeftIntegrable differenceRightIntegrable]
    _ ≤
        angular *
          (‖left - right‖ * ‖left‖ +
            ‖left - right‖ * ‖right‖) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add
          (transverseSpaceTime_integral_norm_mul_norm_le
            requestedTime (left - right) left)
          (transverseSpaceTime_integral_norm_mul_norm_le
            requestedTime (left - right) right))
        angularNonneg
    _ =
        6 * Real.sqrt (integerWaveNormSq output) *
          ‖left - right‖ * (‖left‖ + ‖right‖) := by
      simp only [angular]
      ring

theorem tendsto_transverseSpaceTimeNonlinearRow
    {α : Type*}
    {filter : Filter α}
    {requestedTime : ℝ}
    (states : α → TransverseSpaceTimeState requestedTime)
    (limit : TransverseSpaceTimeState requestedTime)
    (statesTendsto : Tendsto states filter (𝓝 limit))
    (output : IntegerWavevector) :
    Tendsto
      (fun index =>
        transverseSpaceTimeNonlinearRow
          (states index) output)
      filter
      (𝓝 (transverseSpaceTimeNonlinearRow limit output)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  let angular : ℝ :=
    6 * Real.sqrt (integerWaveNormSq output)
  have differenceNormTends :
      Tendsto
        (fun index => ‖states index - limit‖)
        filter (𝓝 0) := by
    have differenceTends :
        Tendsto
          (fun index => states index - limit)
          filter (𝓝 (limit - limit)) :=
      statesTendsto.sub
        (tendsto_const_nhds :
          Tendsto
            (fun _ : α => limit) filter (𝓝 limit))
    have normTends :=
      (continuous_norm.tendsto (limit - limit)).comp
        differenceTends
    change
      Tendsto
        (fun index => ‖states index - limit‖)
        filter (𝓝 ‖limit - limit‖) at normTends
    have zeroNorm :
        ‖(0 : TransverseSpaceTimeState requestedTime)‖ = 0 := by
      simp
    simpa only [sub_self, zeroNorm] using normTends
  have stateNormTends :
      Tendsto
        (fun index => ‖states index‖)
        filter (𝓝 ‖limit‖) :=
    (continuous_norm.tendsto limit).comp statesTendsto
  have stateNormSumTends :
      Tendsto
        (fun index => ‖states index‖ + ‖limit‖)
        filter (𝓝 (‖limit‖ + ‖limit‖)) :=
    stateNormTends.add tendsto_const_nhds
  have boundTends :
      Tendsto
        (fun index =>
          angular * ‖states index - limit‖ *
            (‖states index‖ + ‖limit‖))
        filter (𝓝 0) := by
    simpa using
      ((tendsto_const_nhds.mul differenceNormTends).mul
        stateNormSumTends)
  exact squeeze_zero
    (g := fun index =>
      angular * ‖states index - limit‖ *
        (‖states index‖ + ‖limit‖))
    (fun _ => dist_nonneg)
    (fun index => by
      rw [dist_eq_norm]
      simpa [angular] using
        transverseSpaceTimeNonlinearRow_sub_norm_le
          (states index) limit output)
    boundTends

theorem transverseSpaceTimeNonlinearRow_continuous
    {requestedTime : ℝ}
    (output : IntegerWavevector) :
    Continuous
      (fun state : TransverseSpaceTimeState requestedTime =>
        transverseSpaceTimeNonlinearRow state output) := by
  rw [continuous_iff_continuousAt]
  intro state
  exact tendsto_transverseSpaceTimeNonlinearRow
    (fun later : TransverseSpaceTimeState requestedTime => later)
    state continuousAt_id output

def transverseSpaceTimeInclusionIsometry
    (requestedTime : ℝ) :
    TransverseSpaceTimeState requestedTime →ₗᵢ[ℂ]
      SpaceTimeState requestedTime where
  toLinearMap :=
    (transverseSpaceTimeInclusion requestedTime).toLinearMap
  norm_map' :=
    transverseSpaceTimeInclusion_norm requestedTime

theorem transverseSpaceTimeInclusion_dist
    (requestedTime : ℝ)
    (left right : TransverseSpaceTimeState requestedTime) :
    dist
        (transverseSpaceTimeInclusion requestedTime left)
        (transverseSpaceTimeInclusion requestedTime right) =
      dist left right := by
  exact
    (transverseSpaceTimeInclusionIsometry
      requestedTime).isometry.dist_eq left right

theorem transverseSpaceTime_limit_of_inclusion_tendsto
    (requestedTime : ℝ)
    (states : ℕ → TransverseSpaceTimeState requestedTime)
    (stateLimit : SpaceTimeState requestedTime)
    (statesTendsto :
      Tendsto
        (fun index =>
          transverseSpaceTimeInclusion requestedTime
            (states index))
        atTop (𝓝 stateLimit)) :
    ∃ transverseLimit : TransverseSpaceTimeState requestedTime,
      Tendsto states atTop (𝓝 transverseLimit) ∧
        transverseSpaceTimeInclusion requestedTime
            transverseLimit =
          stateLimit := by
  have includedCauchy :
      CauchySeq
        (fun index =>
          transverseSpaceTimeInclusion requestedTime
            (states index)) :=
    statesTendsto.cauchySeq
  have transverseCauchy : CauchySeq states := by
    rw [Metric.cauchySeq_iff] at includedCauchy ⊢
    intro ε εPos
    obtain ⟨index, later⟩ :=
      includedCauchy ε εPos
    refine ⟨index, ?_⟩
    intro left leftLater right rightLater
    rw [← transverseSpaceTimeInclusion_dist
      requestedTime (states left) (states right)]
    exact later left leftLater right rightLater
  obtain ⟨transverseLimit, transverseTendsto⟩ :=
    cauchySeq_tendsto_of_complete transverseCauchy
  have includedLimitTendsto :
      Tendsto
        (fun index =>
          transverseSpaceTimeInclusion requestedTime
            (states index))
        atTop
        (𝓝
          (transverseSpaceTimeInclusion requestedTime
            transverseLimit)) :=
    ((transverseSpaceTimeInclusion requestedTime).continuous.tendsto
      transverseLimit).comp transverseTendsto
  exact
    ⟨transverseLimit, transverseTendsto,
      tendsto_nhds_unique includedLimitTendsto statesTendsto⟩

theorem transverseSpaceTimeNonlinearRow_limit_identification
    (requestedTime : ℝ)
    (states : ℕ → TransverseSpaceTimeState requestedTime)
    (stateLimit : SpaceTimeState requestedTime)
    (nonlinearLimit :
      NonlinearRowSpaceTimeState requestedTime)
    (output : IntegerWavevector)
    (statesTendsto :
      Tendsto
        (fun index =>
          transverseSpaceTimeInclusion requestedTime
            (states index))
        atTop (𝓝 stateLimit))
    (nonlinearTendsto :
      Tendsto
        (fun index =>
          transverseSpaceTimeNonlinearRow
            (states index) output)
        atTop (𝓝 nonlinearLimit)) :
    ∃ transverseLimit : TransverseSpaceTimeState requestedTime,
      Tendsto states atTop (𝓝 transverseLimit) ∧
        transverseSpaceTimeInclusion requestedTime
            transverseLimit =
          stateLimit ∧
        nonlinearLimit =
          transverseSpaceTimeNonlinearRow
            transverseLimit output := by
  obtain
      ⟨transverseLimit, transverseTendsto,
        inclusionEq⟩ :=
    transverseSpaceTime_limit_of_inclusion_tendsto
      requestedTime states stateLimit statesTendsto
  have generatedNonlinearTendsto :
      Tendsto
        (fun index =>
          transverseSpaceTimeNonlinearRow
            (states index) output)
        atTop
        (𝓝
          (transverseSpaceTimeNonlinearRow
            transverseLimit output)) :=
    tendsto_transverseSpaceTimeNonlinearRow
      states transverseLimit transverseTendsto output
  exact
    ⟨transverseLimit, transverseTendsto, inclusionEq,
      tendsto_nhds_unique nonlinearTendsto
        generatedNonlinearTendsto⟩

/-! ## Actual transverse trajectory realization -/

def wholeTransverseTrajectoryBoundedPath
    (requestedTime : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime))
    (trajectoryTransverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        WholeStateTransverse (trajectory t)) :
    BoundedContinuousFunction
      (Icc (0 : ℝ) requestedTime)
      (↥wholeTransverseVorticitySubmodule) :=
  BoundedContinuousFunction.mkOfCompact
    ⟨wholeTransverseTrajectory
        requestedTime trajectory trajectoryTransverse,
      wholeTransverseTrajectory_continuous
        requestedTime trajectory trajectoryContinuous
        trajectoryTransverse⟩

def wholeTransverseTrajectorySpaceTimePath
    (requestedTime : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime))
    (trajectoryTransverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        WholeStateTransverse (trajectory t)) :
    TransverseSpaceTimeState requestedTime :=
  BoundedContinuousFunction.toLp 2
    (commonTimeMeasure requestedTime) ℂ
    (wholeTransverseTrajectoryBoundedPath requestedTime
      trajectory trajectoryContinuous trajectoryTransverse)

theorem transverseSpaceTimeInclusion_wholeTransverseTrajectory
    (requestedTime : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime))
    (trajectoryTransverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        WholeStateTransverse (trajectory t)) :
    transverseSpaceTimeInclusion requestedTime
        (wholeTransverseTrajectorySpaceTimePath requestedTime
          trajectory trajectoryContinuous trajectoryTransverse) =
      wholeTrajectorySpaceTimePath requestedTime
        trajectory trajectoryContinuous := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    transverseSpaceTimeInclusion_coeFn requestedTime
      (wholeTransverseTrajectorySpaceTimePath requestedTime
        trajectory trajectoryContinuous trajectoryTransverse),
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime) ℂ
      (wholeTransverseTrajectoryBoundedPath requestedTime
        trajectory trajectoryContinuous trajectoryTransverse),
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime) ℂ
      (wholeTrajectoryBoundedPath requestedTime
        trajectory trajectoryContinuous)] with
      time inclusionEq transverseEq wholeEq
  calc
    transverseSpaceTimeInclusion requestedTime
          (wholeTransverseTrajectorySpaceTimePath requestedTime
            trajectory trajectoryContinuous trajectoryTransverse) time =
        (wholeTransverseTrajectorySpaceTimePath requestedTime
          trajectory trajectoryContinuous trajectoryTransverse time).1 :=
      inclusionEq
    _ = trajectory time.1 := by
      have transversePoint :
          wholeTransverseTrajectorySpaceTimePath requestedTime
              trajectory trajectoryContinuous trajectoryTransverse time =
            wholeTransverseTrajectoryBoundedPath requestedTime
              trajectory trajectoryContinuous trajectoryTransverse time := by
        simpa [wholeTransverseTrajectorySpaceTimePath] using transverseEq
      have transverseEqBase :=
        congrArg
          (fun value : ↥wholeTransverseVorticitySubmodule =>
            (value : ComplexVorticityHilbertState))
          transversePoint
      exact transverseEqBase.trans rfl
    _ =
        wholeTrajectorySpaceTimePath requestedTime
          trajectory trajectoryContinuous time := by
      symm
      have wholePoint :
          wholeTrajectorySpaceTimePath requestedTime
              trajectory trajectoryContinuous time =
            wholeTrajectoryBoundedPath requestedTime
              trajectory trajectoryContinuous time := by
        simpa [wholeTrajectorySpaceTimePath] using wholeEq
      exact wholePoint.trans rfl

theorem transverseSpaceTimeNonlinearRow_wholeTransverseTrajectory
    (requestedTime : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime))
    (trajectoryTransverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        WholeStateTransverse (trajectory t))
    (output : IntegerWavevector) :
    transverseSpaceTimeNonlinearRow
        (wholeTransverseTrajectorySpaceTimePath requestedTime
          trajectory trajectoryContinuous trajectoryTransverse)
        output =
      wholeNonlinearRowSpaceTimePath requestedTime
        trajectory trajectoryContinuous trajectoryTransverse output := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    transverseSpaceTimeNonlinearRow_coeFn
      (wholeTransverseTrajectorySpaceTimePath requestedTime
        trajectory trajectoryContinuous trajectoryTransverse)
      output,
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime) ℂ
      (wholeTransverseTrajectoryBoundedPath requestedTime
        trajectory trajectoryContinuous trajectoryTransverse),
    BoundedContinuousFunction.coeFn_toLp
      (p := (1 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime) ℂ
      (wholeNonlinearRowBoundedPath requestedTime
        trajectory trajectoryContinuous trajectoryTransverse output)] with
      time nonlinearEq transverseEq wholeNonlinearEq
  calc
    transverseSpaceTimeNonlinearRow
          (wholeTransverseTrajectorySpaceTimePath requestedTime
            trajectory trajectoryContinuous trajectoryTransverse)
          output time =
        transverseSpaceTimeNonlinearRowFunction
          (wholeTransverseTrajectorySpaceTimePath requestedTime
            trajectory trajectoryContinuous trajectoryTransverse)
          output time :=
      nonlinearEq
    _ =
        wholeStateVorticityNonlinearCoefficientAt
          (trajectory time.1) output := by
      have transverseEqBase :=
        congrArg
          (fun value : ↥wholeTransverseVorticitySubmodule =>
            (value : ComplexVorticityHilbertState))
          transverseEq
      rw [transverseSpaceTimeNonlinearRowFunction]
      congr 1
    _ =
        wholeNonlinearRowSpaceTimePath requestedTime
          trajectory trajectoryContinuous trajectoryTransverse output
          time := by
      symm
      have wholeNonlinearPoint :
          wholeNonlinearRowSpaceTimePath requestedTime trajectory
              trajectoryContinuous trajectoryTransverse output time =
            wholeNonlinearRowBoundedPath requestedTime trajectory
              trajectoryContinuous trajectoryTransverse output time := by
        simpa [wholeNonlinearRowSpaceTimePath] using wholeNonlinearEq
      exact wholeNonlinearPoint.trans rfl

end

end ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
end NavierStokes
end SaturationMonoid
