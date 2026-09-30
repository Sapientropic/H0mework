import H0mework.Physics.DiracEvolution.SafeCanonicalAffineTailEnergyActionLaw

/-!
# Canonical affine essential energy bound

The source-owned uniform energy estimate is transported through the complete
history's closed convex tail core.  The resulting total canonical affine
output is therefore an essentially bounded time family of physical spatial
`L²` states.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineEssentialBound

open Filter MeasureTheory Set
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyActionLaw
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyCenter
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineUniformEnergy
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracMatterSpatialEnergyBalance
open scoped BoundedContinuousFunction

noncomputable section

set_option autoImplicit false

private def lpAlmostEverywhereNormBound
    {X E : Type*}
    [MeasurableSpace X]
    [NormedAddCommGroup E]
    (μ : Measure X)
    (R : ℝ) :
    Set (Lp E 2 μ) :=
  {f | ∀ᵐ x ∂μ, ‖f x‖ ≤ R}

private def LpHasAlmostEverywhereNormBound
    {X E : Type*}
    [MeasurableSpace X]
    [NormedAddCommGroup E]
    (μ : Measure X)
    (f : Lp E 2 μ) : Prop :=
  ∃ R : ℝ, 0 ≤ R ∧ f ∈ lpAlmostEverywhereNormBound (E := E) μ R

private theorem lpAlmostEverywhereNormBound_isClosed
    {X E : Type*}
    [MeasurableSpace X]
    [NormedAddCommGroup E]
    (μ : Measure X)
    (R : ℝ) :
    IsClosed (lpAlmostEverywhereNormBound (E := E) μ R) := by
  apply IsSeqClosed.isClosed
  intro sequence limit sequenceMem sequenceTendsto
  obtain ⟨subsequence, _subsequenceStrictMono, pointwiseTendsto⟩ :=
    (tendstoInMeasure_of_tendsto_Lp sequenceTendsto).exists_seq_tendsto_ae
  have subsequenceBound :
      ∀ᵐ x ∂μ, ∀ n : ℕ, ‖sequence (subsequence n) x‖ ≤ R :=
    ae_all_iff.2 fun n ↦ sequenceMem (subsequence n)
  filter_upwards [pointwiseTendsto, subsequenceBound] with x hx hbound
  exact le_of_tendsto hx.norm (Eventually.of_forall hbound)

private theorem lpAlmostEverywhereNormBound_convex
    {X E : Type*}
    [MeasurableSpace X]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (μ : Measure X)
    (R : ℝ) :
    Convex ℝ (lpAlmostEverywhereNormBound (E := E) μ R) := by
  rw [convex_iff_add_mem]
  intro first firstBound second secondBound firstWeight secondWeight
    firstWeightNonnegative secondWeightNonnegative weightsSum
  filter_upwards [
      firstBound,
      secondBound,
      Lp.coeFn_add (firstWeight • first) (secondWeight • second),
      Lp.coeFn_smul firstWeight first,
      Lp.coeFn_smul secondWeight second] with
      x hfirst hsecond hadd hfirstSmul hsecondSmul
  rw [hadd, Pi.add_apply, hfirstSmul, hsecondSmul, Pi.smul_apply,
    Pi.smul_apply]
  calc
    ‖firstWeight • first x + secondWeight • second x‖ ≤
        ‖firstWeight • first x‖ + ‖secondWeight • second x‖ :=
      norm_add_le _ _
    _ = firstWeight * ‖first x‖ + secondWeight * ‖second x‖ := by
      simp only [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg firstWeightNonnegative,
        abs_of_nonneg secondWeightNonnegative]
    _ ≤ firstWeight * R + secondWeight * R :=
      add_le_add
        (mul_le_mul_of_nonneg_left hfirst firstWeightNonnegative)
        (mul_le_mul_of_nonneg_left hsecond secondWeightNonnegative)
    _ = R := by rw [← add_mul, weightsSum, one_mul]

private theorem boundedContinuousFunction_toLp_mem_aeNormBound
    {X E : Type*}
    [MeasurableSpace X]
    [TopologicalSpace X]
    [BorelSpace X]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [SecondCountableTopologyEither X E]
    (μ : Measure X)
    [IsFiniteMeasure μ]
    (path : X →ᵇ E)
    (R : ℝ)
    (pathBound : ∀ x, ‖path x‖ ≤ R) :
    (BoundedContinuousFunction.toLp 2 μ ℝ) path ∈
      lpAlmostEverywhereNormBound (E := E) μ R := by
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 μ ℝ path] with
      time htime
  rw [htime]
  exact pathBound time

private theorem LpHasAlmostEverywhereNormBound_congr_ae
    {X E : Type*}
    [MeasurableSpace X]
    [NormedAddCommGroup E]
    (μ : Measure X)
    (first second : Lp E 2 μ)
    (firstEqSecond : (first : X → E) =ᵐ[μ] second)
    (secondBounded : LpHasAlmostEverywhereNormBound μ second) :
    LpHasAlmostEverywhereNormBound μ first := by
  change ∃ R : ℝ, 0 ≤ R ∧
    ∀ᵐ x ∂μ, ‖second x‖ ≤ R at secondBounded
  obtain ⟨R, RNonnegative, secondBound⟩ := secondBounded
  refine ⟨R, RNonnegative, ?_⟩
  filter_upwards [firstEqSecond, secondBound] with x heq hbound
  rwa [heq]

private theorem LpHasAlmostEverywhereNormBound_add
    {X E : Type*}
    [MeasurableSpace X]
    [NormedAddCommGroup E]
    (μ : Measure X)
    (first second : Lp E 2 μ)
    (firstBounded : LpHasAlmostEverywhereNormBound μ first)
    (secondBounded : LpHasAlmostEverywhereNormBound μ second) :
    LpHasAlmostEverywhereNormBound μ (first + second) := by
  change ∃ R : ℝ, 0 ≤ R ∧
    ∀ᵐ x ∂μ, ‖first x‖ ≤ R at firstBounded
  change ∃ R : ℝ, 0 ≤ R ∧
    ∀ᵐ x ∂μ, ‖second x‖ ≤ R at secondBounded
  obtain ⟨firstR, firstRNonnegative, firstBound⟩ := firstBounded
  obtain ⟨secondR, secondRNonnegative, secondBound⟩ := secondBounded
  refine ⟨firstR + secondR,
    add_nonneg firstRNonnegative secondRNonnegative, ?_⟩
  filter_upwards [Lp.coeFn_add first second, firstBound, secondBound] with
      x hadd hfirst hsecond
  rw [hadd]
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)

private theorem canonicalAffineCorrectionTimeL2TailEnergyCenter_ae_norm_bound
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    LpHasAlmostEverywhereNormBound
      (X := Icc 0 timeEnd)
      (E := CauchySafeMatterSpatialL2 a b)
      (canonicalAffineTimeMeasure timeEnd)
      (canonicalAffineCorrectionTimeL2TailEnergyCenter
        timeEnd timeNonnegative a b boxOrder) := by
  have sourceBound : ∃ R : ℝ, 0 ≤ R ∧ ∀ testCount : ℕ,
      ∀ time ∈ Icc 0 timeEnd,
        ‖fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount
          (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
            timeEnd timeNonnegative a b testCount time)‖ ≤ R :=
    StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineUniformEnergy.exists_fixedP506L0CauchySafeMatterCanonicalAffineCorrection_uniform_bound
      timeEnd timeNonnegative a b boxOrder
  obtain ⟨R, RNonnegative, correctionBound⟩ := sourceBound
  refine ⟨R, RNonnegative, ?_⟩
  apply canonicalAffineCorrectionTimeL2TailEnergyCenter_mem_of_history_mem
    timeEnd timeNonnegative a b boxOrder
    (lpAlmostEverywhereNormBound
      (E := CauchySafeMatterSpatialL2 a b)
      (canonicalAffineTimeMeasure timeEnd) R)
    (lpAlmostEverywhereNormBound_isClosed
      (E := CauchySafeMatterSpatialL2 a b)
      (canonicalAffineTimeMeasure timeEnd) R)
    (lpAlmostEverywhereNormBound_convex
      (E := CauchySafeMatterSpatialL2 a b)
      (canonicalAffineTimeMeasure timeEnd) R)
  intro testCount
  change (BoundedContinuousFunction.toLp 2
      (canonicalAffineTimeMeasure timeEnd) ℝ)
      (canonicalAffineCorrectionL2BoundedPath
        timeEnd timeNonnegative a b testCount) ∈
    lpAlmostEverywhereNormBound
      (E := CauchySafeMatterSpatialL2 a b)
      (canonicalAffineTimeMeasure timeEnd) R
  apply boundedContinuousFunction_toLp_mem_aeNormBound
  intro time
  exact correctionBound testCount time.1 time.2

private theorem canonicalAffineSourceLiftTimeL2_ae_norm_bound
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    LpHasAlmostEverywhereNormBound
      (X := Icc 0 timeEnd)
      (E := CauchySafeMatterSpatialL2 a b)
      (canonicalAffineTimeMeasure timeEnd)
      (canonicalAffineSourceLiftTimeL2 timeEnd a b) := by
  let sourceValue :=
    fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b
  refine ⟨‖sourceValue‖, norm_nonneg _, ?_⟩
  filter_upwards [canonicalAffineSourceLiftTimeL2_coe_ae
      timeEnd a b] with _time hsource
  rw [hsource]

private theorem canonicalAffinePhysicalTimeL2Output_ae_norm_bound
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    LpHasAlmostEverywhereNormBound
      (X := Icc 0 timeEnd)
      (E := CauchySafeMatterSpatialL2 a b)
      (canonicalAffineTimeMeasure timeEnd)
      (canonicalAffinePhysicalTimeL2Output
        timeEnd timeNonnegative a b boxOrder) := by
  apply LpHasAlmostEverywhereNormBound_congr_ae
    (canonicalAffineTimeMeasure timeEnd)
    (canonicalAffinePhysicalTimeL2Output
      timeEnd timeNonnegative a b boxOrder)
    (canonicalAffineSourceLiftTimeL2 timeEnd a b +
      canonicalAffineCorrectionTimeL2TailEnergyCenter
        timeEnd timeNonnegative a b boxOrder)
    ((canonicalAffinePhysicalTimeL2Output_coe_ae
      timeEnd timeNonnegative a b boxOrder).trans
        (Lp.coeFn_add
          (canonicalAffineSourceLiftTimeL2 timeEnd a b)
          (canonicalAffineCorrectionTimeL2TailEnergyCenter
            timeEnd timeNonnegative a b boxOrder)).symm)
  exact LpHasAlmostEverywhereNormBound_add
    (canonicalAffineTimeMeasure timeEnd)
    (canonicalAffineSourceLiftTimeL2 timeEnd a b)
    (canonicalAffineCorrectionTimeL2TailEnergyCenter
      timeEnd timeNonnegative a b boxOrder)
    (canonicalAffineSourceLiftTimeL2_ae_norm_bound timeEnd a b)
    (canonicalAffineCorrectionTimeL2TailEnergyCenter_ae_norm_bound
      timeEnd timeNonnegative a b boxOrder)

/-- One real bound controls the canonical affine output at almost every
source time. -/
theorem exists_canonicalAffinePhysicalTimeL2Output_ae_norm_bound
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ᵐ time ∂canonicalAffineTimeMeasure timeEnd,
        ‖canonicalAffinePhysicalTimeL2Output
          timeEnd timeNonnegative a b boxOrder time‖ ≤ R := by
  exact canonicalAffinePhysicalTimeL2Output_ae_norm_bound
    timeEnd timeNonnegative a b boxOrder

/-- The unique source-generated affine output is an essentially bounded
time family of physical spatial `L²` states. -/
theorem canonicalAffinePhysicalTimeL2Output_memLp_top
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    MemLp (fun time ↦ canonicalAffinePhysicalTimeL2Output
      timeEnd timeNonnegative a b boxOrder time) ⊤
      (canonicalAffineTimeMeasure timeEnd) := by
  have outputBounded := canonicalAffinePhysicalTimeL2Output_ae_norm_bound
    timeEnd timeNonnegative a b boxOrder
  change ∃ R : ℝ, 0 ≤ R ∧
    ∀ᵐ time ∂canonicalAffineTimeMeasure timeEnd,
      ‖canonicalAffinePhysicalTimeL2Output
        timeEnd timeNonnegative a b boxOrder time‖ ≤ R at outputBounded
  obtain ⟨R, _RNonnegative, outputBound⟩ := outputBounded
  refine ⟨Lp.aestronglyMeasurable _, ?_⟩
  rw [eLpNorm_exponent_top]
  exact (eLpNormEssSup_le_of_ae_bound outputBound).trans_lt
    ENNReal.ofReal_lt_top

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineEssentialBound
