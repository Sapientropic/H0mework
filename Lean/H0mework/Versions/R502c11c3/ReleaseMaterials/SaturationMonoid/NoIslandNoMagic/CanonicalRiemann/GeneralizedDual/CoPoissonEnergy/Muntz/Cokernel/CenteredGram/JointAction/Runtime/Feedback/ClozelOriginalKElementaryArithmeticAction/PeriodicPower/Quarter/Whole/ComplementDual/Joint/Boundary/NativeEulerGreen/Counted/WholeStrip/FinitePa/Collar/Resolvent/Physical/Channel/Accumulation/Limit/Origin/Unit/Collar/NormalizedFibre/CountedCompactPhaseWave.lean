import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedCompactPhaseProfile
import H0mework.Arithmetic.TruncatedFourier.BlockStates

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open FourierTransform
open scoped Topology ENNReal BoundedContinuousFunction FourierTransform InnerProductSpace

local notation "L¹" => Lp ℂ 1 (volume : Measure ℝ)
local notation "q" => (1/4 : ℝ)
local notation "r₀" => (q/2)
local notation "P" => burnolEvenAmbientProjection

private def quarterCutL1 (v : BurnolL2) : L¹ := (splitAtPhysicalCutoff q v).1

private theorem quarter_cut_read (v : BurnolL2) :
    (quarterCutL1 v : ℝ → ℂ) =ᵐ[volume] (originalPhysicalCutoff q v : ℝ → ℂ) :=
  (originalPhysicalCutoff_integrable q v).coeFn_toL1

private theorem quarter_cut_bound (v : BurnolL2) : ‖quarterCutL1 v‖ ≤ ‖v‖ := by
  let window := symmetricInterval q
  let μ := (volume : Measure ℝ).restrict window
  have cut := (quarter_cut_read v).trans (originalPhysicalCutoff_coeFn q v)
  have measurable : MeasurableSet window := measurableSet_symmetricInterval q
  have measured : AEStronglyMeasurable (v : ℝ → ℂ) μ :=
    (Lp.aestronglyMeasurable v).mono_measure Measure.restrict_le_self
  have mass : μ univ ≤ 1 := by
    change volume.restrict (symmetricInterval q) univ ≤ 1
    rw [Measure.restrict_apply_univ, symmetricInterval, Real.volume_Icc]
    exact (ENNReal.ofReal_le_ofReal (show q - -q ≤ 1 by norm_num)).trans_eq ENNReal.ofReal_one
  have holder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) measured
  have exponent : 1/(1 : ℝ≥0∞).toReal - 1/(2 : ℝ≥0∞).toReal = (1/2 : ℝ) := by norm_num
  rw [exponent] at holder
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae cut, eLpNorm_indicator_eq_eLpNorm_restrict measurable]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top v)
  refine holder.trans ?_
  calc
    _ ≤ eLpNorm (v : ℝ → ℂ) 2 μ * 1 :=
      by gcongr; exact ENNReal.rpow_le_one mass (by norm_num)
    _ ≤ _ := by rw [mul_one]; exact eLpNorm_mono_measure _ Measure.restrict_le_self

private def quarterCutCLM : BurnolL2 →L[ℂ] L¹ :=
  LinearMap.mkContinuous
    { toFun := quarterCutL1
      map_add' := fun u v => by
        have linear : originalPhysicalCutoff q (u+v) =
            originalPhysicalCutoff q u+originalPhysicalCutoff q v := by
          unfold originalPhysicalCutoff
          rw [map_add, map_add]
        have sum := Lp.coeFn_add (originalPhysicalCutoff q u) (originalPhysicalCutoff q v)
        rw [← linear] at sum
        apply Lp.ext
        filter_upwards [quarter_cut_read (u+v), quarter_cut_read u, quarter_cut_read v,
          Lp.coeFn_add (quarterCutL1 u) (quarterCutL1 v), sum] with x uv atU atV joined point
        rw [uv, joined, point, Pi.add_apply, Pi.add_apply, atU, atV]
      map_smul' := fun a v => by
        have linear : originalPhysicalCutoff q (a • v) = a • originalPhysicalCutoff q v := by
          unfold originalPhysicalCutoff
          rw [map_smul, map_smul]
        have scaled := Lp.coeFn_smul a (originalPhysicalCutoff q v)
        rw [← linear] at scaled
        apply Lp.ext
        filter_upwards [quarter_cut_read (a • v), quarter_cut_read v, Lp.coeFn_smul a (quarterCutL1 v),
          scaled] with x av atV joined point
        simp only [RingHom.id_apply]
        rw [av, joined, point, Pi.smul_apply, Pi.smul_apply, atV] }
    1 fun v => by
      change ‖quarterCutL1 v‖ ≤ 1*‖v‖
      simpa only [one_mul] using quarter_cut_bound v

/-- Complete ordinary position read for the original quarter supported fields. -/
def compactPhaseJoin : (L¹ × BurnolL2) →L[ℂ] L¹ :=
  ContinuousLinearMap.fst ℂ L¹ BurnolL2 + quarterCutCLM.comp (ContinuousLinearMap.snd ℂ L¹ BurnolL2)

def compactPhaseWave : (L¹ × BurnolL2) →L[ℂ] (ℝ →ᵇ ℂ) :=
  (Real.Lp.fourierTransformCLM ℝ ℂ).comp compactPhaseJoin

private theorem quarter_cut_identity (v : BurnolL2)
    (support : ∀ᵐ x : ℝ ∂volume, q < |x| → v x = 0) :
    originalPhysicalCutoff q v = v := by
  apply Lp.ext
  filter_upwards [originalPhysicalCutoff_coeFn q v, support] with x read zero
  rw [read]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside]
  · rw [indicator_of_notMem inside, zero (lt_of_not_ge (fun h => inside (abs_le.mp h)))]

private theorem compact_join_read (z : L¹ × BurnolL2) (support : originalPhysicalCutoff q z.2 = z.2) :
    (compactPhaseJoin z : ℝ → ℂ) =ᵐ[volume] fun x => z.1 x+z.2 x := by
  have outside := quarter_cut_read z.2
  rw [support] at outside
  filter_upwards [Lp.coeFn_add z.1 (quarterCutL1 z.2), outside] with x joined atX
  change (z.1+quarterCutL1 z.2 : L¹) x = _
  rw [joined, Pi.add_apply, atX]

private theorem compact_wave_zero (z : L¹ × BurnolL2) :
    compactPhaseWave z 0 = L1.integralCLM' ℂ (compactPhaseJoin z) := by
  change Real.Lp.fourierTransformCLM ℝ ℂ (compactPhaseJoin z) 0 = _
  rw [Real.Lp.fourierTransformCLM_apply, Real.Lp.fourierTransform_apply, Real.fourier_real_eq,
    ← L1.integral_eq' ℂ, L1.integral_eq_integral]
  simp

private theorem quarter_projected_seed_ne_zero : P ConstantDual.seed ≠ 0 := by
  let anti := burnolRadiusMinusBlockState q (by norm_num) (by norm_num)
  let test : BurnolPaAmbientCarrier := ⟨anti, burnolRadiusMinusBlockState_mem _ _⟩
  intro zero
  let : CompleteSpace BurnolPaAmbientCarrier :=
    IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
  have contact := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
    |>.inner_orthogonalProjectionOnto_eq_of_mem_left test ConstantDual.seed
  change inner ℂ test (P ConstantDual.seed) = inner ℂ anti ConstantDual.seed at contact
  rw [zero, inner_zero_right] at contact
  have adjoint : inner ℂ anti ConstantDual.seed =
      inner ℂ (burnolQuarterRestriction anti) (intervalConstant q) :=
    ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction _ _
  have restriction : burnolQuarterRestriction anti = intervalConstant q :=
    burnolRadiusMinusBlockState_restriction _ _
  rw [adjoint, restriction] at contact
  exact intervalConstant_ne_zero (by norm_num : 0 < q) (inner_self_eq_zero.mp contact.symm)

/-- The zero frequency consumes the original physical projection on the same compact field. -/
theorem compact_phase_physical_wave_zero (z : L¹ × BurnolL2)
    (support : ∀ᵐ x : ℝ ∂volume, q < |x| → z.2 x = 0) :
    physicalProjectionFromCentre z = 0 ↔ compactPhaseWave z 0 = 0 := by
  let unit := (2 : ℂ) • P ConstantDual.seed
  have unitLive : unit ≠ 0 := smul_ne_zero (by norm_num) quarter_projected_seed_ne_zero
  have original := original_physical_projection_from_split q le_rfl z.2
  change L1.integralCLM' ℂ (quarterCutL1 z.2) • unit +
    P (z.2-originalPhysicalCutoff q z.2) = P z.2 at original
  rw [quarter_cut_identity z.2 support, sub_self, map_zero, add_zero] at original
  have physical : physicalProjectionFromCentre z = compactPhaseWave z 0 • unit := by
    rw [compact_wave_zero]
    change L1.integralCLM' ℂ z.1 • unit + P z.2 =
      L1.integralCLM' ℂ (z.1+quarterCutL1 z.2) • unit
    rw [map_add, add_smul, original]
  rw [physical]
  exact ⟨fun h => (smul_eq_zero.mp h).resolve_right unitLive, fun h => by rw [h, zero_smul]⟩

/-- The ordinary wave evaluates the Fourier transform of the same tempered occurrence. -/
theorem compact_phase_wave_tempered (z : L¹ × BurnolL2)
    (support : ∀ᵐ x : ℝ ∂volume, q < |x| → z.2 x = 0) (test : SchwartzMap ℝ ℂ) :
    𝓕 (distributionOfSplit z) test = ∫ ξ, test ξ * compactPhaseWave z ξ := by
  let v := compactPhaseJoin z
  have read := compact_join_read z (quarter_cut_identity z.2 support)
  rw [TemperedDistribution.fourier_apply, distributionOfSplit_apply]
  calc
    _ = ∫ x, (𝓕 (test : ℝ → ℂ)) x * v x := by
      apply integral_congr_ae
      filter_upwards [read] with x atX
      rw [atX, ← SchwartzMap.fourier_coe]
    _ = ∫ ξ, test ξ * compactPhaseWave z ξ := by
      have bilinear : Continuous (fun p : ℝ × ℝ => innerₗ ℝ p.1 p.2) :=
        continuous_inner
      have swap := VectorFourier.integral_fourierIntegral_smul_eq_flip
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (g := (test : ℝ → ℂ)) Real.continuous_fourierChar bilinear (L1.integrable_coeFn v) test.integrable
      rw [flip_innerₗ] at swap
      change (∫ ξ, (𝓕 (v : ℝ → ℂ)) ξ • test ξ) =
        (∫ x, v x • (𝓕 (test : ℝ → ℂ)) x) at swap
      change (∫ x, (𝓕 (test : ℝ → ℂ)) x * v x) =
        ∫ ξ, test ξ * (𝓕 (v : ℝ → ℂ)) ξ
      simpa only [smul_eq_mul, mul_comm] using swap.symm

/-- Both strong limits come from the literal same counted R action. -/
theorem actual_counted_compact_phase_wave (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n => (compactPhaseJoin (countedCompactPhaseField c n),
        compactPhaseWave (countedCompactPhaseField c n))) atTop
      (𝓝 (compactPhaseJoin (countedCompactPhaseLimit c), compactPhaseWave (countedCompactPhaseLimit c))) := by
  have actual := actual_counted_compact_phase_limit c
  exact (compactPhaseJoin.continuous.tendsto _ |>.comp actual).prodMk_nhds
    (compactPhaseWave.continuous.tendsto _ |>.comp actual)

theorem actual_counted_compact_wave_read (c : BurnolCompletedMellinCoordinate) (ξ : ℝ) :
    compactPhaseWave (countedCompactPhaseLimit c) ξ = 𝓕 (countedCompactPhaseProfile c) ξ := by
  have support := (actual_compact_phase_limit_support c).mono fun _ h outside => (h outside).2
  have read := compact_join_read _ (quarter_cut_identity _ support)
  change (𝓕 (compactPhaseJoin (countedCompactPhaseLimit c) : ℝ → ℂ)) ξ = _
  apply Real.fourier_congr_ae _ ξ
  filter_upwards [read, actual_compact_phase_limit_profile c] with x joined field
  rw [joined, field.1, field.2]
  by_cases inner : r₀ < |x|
  · have missing : x ∉ symmetricInterval r₀ := fun h => inner.not_ge (abs_le.mpr h)
    rw [indicator_of_notMem missing, if_pos inner, zero_add]
  · have inside : x ∈ symmetricInterval r₀ := abs_le.mp (le_of_not_gt inner)
    rw [indicator_of_mem inside, if_neg inner, add_zero]

theorem actual_counted_compact_wave_zero (c : BurnolCompletedMellinCoordinate) :
    (∀ n, compactPhaseWave (countedCompactPhaseField c n) 0 = 0) ∧
    compactPhaseWave (countedCompactPhaseLimit c) 0 = 0 := by
  constructor
  · intro n
    exact (compact_phase_physical_wave_zero _ ((actual_counted_compact_phase_support c n).mono
      fun _ h outside => (h outside).2)).mp (actual_counted_compact_phase_projection c n)
  · exact (compact_phase_physical_wave_zero _ ((actual_compact_phase_limit_support c).mono
      fun _ h outside => (h outside).2)).mp (actual_counted_compact_phase_observations c).2

/-- The exact wave equation reads the same seed occurrence as the position Euler law. -/
theorem actual_counted_compact_wave_equation (c : BurnolCompletedMellinCoordinate) :
    let wave := 𝓕 (distributionOfSplit (countedCompactPhaseLimit c))
    GapEuler.euler wave-(star c.value-1/2) • wave = -𝓕 (distributionOfSplit (countedSeedSplit c)) := by
  let value := distributionOfSplit (countedCompactPhaseLimit c)
  let rate := star c.value-1/2
  have source : GapEuler.euler value+rate • value = distributionOfSplit (countedSeedSplit c) :=
    (actual_counted_compact_phase_observations c).1
  have actual := congrArg (fun field : TemperedDistribution ℝ ℂ => 𝓕 field) source
  rw [FourierAdd.fourier_add, FourierSMul.fourier_smul] at actual
  change GapEuler.euler (𝓕 value)-rate • 𝓕 value = _
  rw [GapEuler.euler_fourier]
  calc
    _ = -(𝓕 (GapEuler.euler value)+rate • 𝓕 value) := by abel
    _ = _ := congrArg Neg.neg actual

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
