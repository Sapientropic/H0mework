import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Interval
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FiniteLogCountingSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.JointLogConductorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KappaConductorTailSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Arithmetic.TruncatedFourier.ActualBridge
import H0mework.Arithmetic.TruncatedFourier.IntegralKernel
import H0mework.Arithmetic.TruncatedFourier.RadiusIntegralKernel

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.CompactConductorExterior
open Complex Filter FourierTransform MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.JointLogConductor
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "μq" => (volume.restrict (symmetricInterval q))
local instance : IsFiniteMeasure μq := by
  change IsFiniteMeasure (volume.restrict (Icc (-q) q))
  infer_instance

macro "compactPaid% " field:ident : term => do
  let paidOwnerPrefix := Lean.Name.num (if #["source_kernel_tail_bound","sourceTriple","source_triple_measured","sourceFrequencyTriple","source_frequency_clock_point","source_heat_product_integrable","source_inverse_pairing","source_heat_actual_pairing","source_inverse_product_integrable","source_cut_frequency_clock","source_frequency_triple_integrable","compact_profile_pairing","full_half_fold"].contains field.getId.eraseMacroScopes.toString then `_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KappaConductorTailSource else `_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KappaConductorSource) 0
  let scope := `SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalGamma.Source.KappaConductor
  return Lean.mkIdent (paidOwnerPrefix.append (scope.append field.getId))

private abbrev offDiagonalHeat := compactPaid% offDiagonalHeat
private abbrev heatLogCut := compactPaid% heatLogCut
private abbrev heat_log_paired_source_limit := compactPaid% heat_log_paired_source_limit
private abbrev sourceHeatCotest := compactPaid% sourceHeatCotest
private abbrev source_heat_cotest_physical := compactPaid% source_heat_cotest_physical
private abbrev source_cut_frequency_clock := compactPaid% source_cut_frequency_clock
private abbrev source_frequency_clock_point := compactPaid% source_frequency_clock_point
private abbrev kernel_clock_integrable := compactPaid% kernel_clock_integrable
private abbrev kernel_clock_norm_payment := compactPaid% kernel_clock_norm_payment
private abbrev kernel_clock_payment := compactPaid% kernel_clock_payment
private abbrev sourceFrequencyTriple := compactPaid% sourceFrequencyTriple
private abbrev compact_profile_pairing := compactPaid% compact_profile_pairing

private theorem heat_real (time distance : ℝ) :
    star (offDiagonalHeat time distance) = offDiagonalHeat time distance := by
  change star (((Real.sqrt (Real.pi / time) * Real.exp (-(Real.pi ^ 2 * distance ^ 2 / time)) : ℝ) : ℂ)) = _
  exact Complex.conj_ofReal _

private theorem heat_swap (time x y : ℝ) :
    offDiagonalHeat time (x - y) = offDiagonalHeat time (y - x) := by
  change (((Real.sqrt (Real.pi / time) * Real.exp (-(Real.pi ^ 2 * (x - y) ^ 2 / time)) : ℝ) : ℂ)) =
    (((Real.sqrt (Real.pi / time) * Real.exp (-(Real.pi ^ 2 * (y - x) ^ 2 / time)) : ℝ) : ℂ))
  rw [show (x - y) ^ 2 = (y - x) ^ 2 by ring]

private theorem compact_value_integrable (r : Hq) : Integrable (E r : ℝ → ℂ) :=
  (burnolQuarterZeroExtensionRaw_integrable r).congr (burnolQuarterZeroExtension_coe r).symm

private theorem compact_value_outside (r : Hq) :
    ∀ᵐ y : ℝ ∂volume, q < |y| → E r y = 0 := by
  filter_upwards [burnolQuarterZeroExtension_coe r] with y source
  intro outside
  rw [source, indicator_of_notMem (show y ∉ symmetricInterval q from fun h =>
    not_le.mpr outside (abs_le.mpr h))]

private theorem exterior_cotest_buffer (test : SchwartzMap ℝ ℂ) (support : tsupport test ⊆ Ioi q) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ x ∈ tsupport test, delta ≤ x - q := by
  have excluded : q ∉ tsupport test := fun inside => lt_irrefl q (support inside)
  obtain ⟨delta, positive, buffer⟩ := Metric.mem_nhds_iff.mp
    ((isClosed_tsupport test).isOpen_compl.mem_nhds excluded)
  refine ⟨delta, positive, ?_⟩
  intro x inside
  have lower : q < x := support inside
  apply le_of_not_gt
  intro small
  have near : x ∈ Metric.ball q delta := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr lower)]
    exact small
  exact buffer near inside

private def triple (test : SchwartzMap ℝ ℂ) (value : BurnolL2) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  star (test p.1.1) * value p.1.2 * (p.2 : ℂ)⁻¹ * offDiagonalHeat p.2 (p.1.1 - p.1.2)

private theorem triple_measured (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    AEStronglyMeasurable (triple test value) ((volume.prod volume).prod (volume.restrict (Ioi 0))) := by
  exact (compactPaid% source_triple_measured) test value

private theorem compact_triple_integrable (test : SchwartzMap ℝ ℂ) (r : Hq)
    (support : tsupport test ⊆ Ioi q) :
    Integrable (triple test (E r)) ((volume.prod volume).prod (volume.restrict (Ioi 0))) := by
  obtain ⟨delta, positive, buffer⟩ := exterior_cotest_buffer test support
  let C : ℝ := delta⁻¹
  have measured := triple_measured test (E r)
  have domination : Integrable (fun xy : ℝ × ℝ => C * ‖test xy.1‖ * ‖E r xy.2‖)
      (volume.prod volume) := by
    simpa only [mul_assoc] using (test.integrable.norm.mul_prod (compact_value_integrable r).norm).const_mul C
  have wholeOutside : ∀ᵐ xy : ℝ × ℝ ∂volume.prod volume, q < |xy.2| → E r xy.2 = 0 :=
    Measure.quasiMeasurePreserving_snd.ae (compact_value_outside r)
  have apart (x y : ℝ) (testNonzero : test x ≠ 0) (valueNonzero : E r y ≠ 0)
      (outside : q < |y| → E r y = 0) : delta ≤ |x - y| := by
    have point := buffer x (subset_tsupport test testNonzero)
    have bounded : |y| ≤ q := le_of_not_gt (fun large => valueNonzero (outside large))
    have upper : y ≤ q := (le_abs_self y).trans bounded
    have oriented : 0 ≤ x - y := by linarith [point]
    rw [abs_of_nonneg oriented]
    linarith [point]
  have allClocks : ∀ᵐ xy : ℝ × ℝ ∂volume.prod volume,
      IntegrableOn (fun time : ℝ => triple test (E r) (xy, time)) (Ioi 0) := by
    filter_upwards [wholeOutside] with xy outside
    by_cases testZero : test xy.1 = 0
    · simp only [triple, testZero, star_zero, zero_mul, IntegrableOn]
      convert integrable_zero ℝ ℂ (volume.restrict (Ioi 0)) using 1 <;> rfl
    by_cases valueZero : E r xy.2 = 0
    · simp only [triple, valueZero, mul_zero, zero_mul, IntegrableOn]
      convert integrable_zero ℝ ℂ (volume.restrict (Ioi 0)) using 1 <;> rfl
    have distance := positive.trans_le (apart xy.1 xy.2 testZero valueZero outside)
    have nonzero : xy.1 - xy.2 ≠ 0 := by intro equal; simp only [equal, abs_zero, lt_self_iff_false] at distance
    have source := (kernel_clock_integrable (xy.1 - xy.2) nonzero).const_mul
      (star (test xy.1) * E r xy.2)
    simpa only [triple, mul_assoc, IntegrableOn] using source
  have totalBudget : Integrable (fun xy : ℝ × ℝ => ∫ time : ℝ in Ioi 0, ‖triple test (E r) (xy, time)‖)
      (volume.prod volume) := by
    apply domination.mono' measured.norm.integral_prod_right'
    filter_upwards [wholeOutside] with xy outside
    have cNonnegative : 0 ≤ C := inv_nonneg.mpr positive.le
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    by_cases testZero : test xy.1 = 0
    · simp only [triple, testZero, star_zero, zero_mul, norm_zero, integral_zero]
      positivity
    by_cases valueZero : E r xy.2 = 0
    · simp only [triple, valueZero, mul_zero, zero_mul, norm_zero, integral_zero]
      positivity
    have separated := apart xy.1 xy.2 testZero valueZero outside
    have distance := positive.trans_le separated
    have nonzero : xy.1 - xy.2 ≠ 0 := by intro equal; simp only [equal, abs_zero, lt_self_iff_false] at distance
    have normalizedClock : (∫ time : ℝ in Ioi 0, ‖triple test (E r) (xy, time)‖) =
        ‖test xy.1‖ * ‖E r xy.2‖ * |xy.1 - xy.2|⁻¹ := by
      have shape : (fun time : ℝ => ‖triple test (E r) (xy, time)‖) =
          fun time : ℝ => (‖test xy.1‖ * ‖E r xy.2‖) * ‖(time : ℂ)⁻¹ * offDiagonalHeat time (xy.1 - xy.2)‖ := by
        funext time
        simp only [triple, norm_mul, norm_star]
        ring
      rw [shape, integral_const_mul, kernel_clock_norm_payment _ nonzero]
    rw [normalizedClock]
    have inverse : |xy.1 - xy.2|⁻¹ ≤ C := by
      simpa only [one_div, C] using one_div_le_one_div_of_le positive separated
    exact (mul_le_mul_of_nonneg_left inverse (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)
  exact (integrable_prod_iff measured).mpr ⟨allClocks, totalBudget⟩

private def clockRead (test : SchwartzMap ℝ ℂ) (value : BurnolL2) (time : ℝ) : ℂ :=
  ∫ xy : ℝ × ℝ, triple test value (xy, time) ∂volume.prod volume
private def spatialRead (test : SchwartzMap ℝ ℂ) (value : BurnolL2) (xy : ℝ × ℝ) : ℂ :=
  star (test xy.1) * value xy.2 * ((|xy.1 - xy.2|⁻¹ : ℝ) : ℂ)

private theorem clock_collapse (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    (fun xy : ℝ × ℝ => ∫ time : ℝ in Ioi 0, triple test value (xy, time)) =ᵐ[volume.prod volume]
      spatialRead test value := by
  have diagonal : ∀ᵐ xy : ℝ × ℝ ∂volume.prod volume, xy.1 - xy.2 ≠ 0 := by
    apply (Measure.ae_prod_iff_ae_ae (show MeasurableSet {xy : ℝ × ℝ | xy.1 - xy.2 ≠ 0} from (isClosed_eq (by fun_prop : Continuous (fun xy : ℝ × ℝ => xy.1 - xy.2)) continuous_const).measurableSet.compl)).mpr
    filter_upwards with x
    filter_upwards [volume.ae_ne x] with y different
    exact sub_ne_zero.mpr different.symm
  filter_upwards [diagonal] with xy different
  have shape : (fun time : ℝ => triple test value (xy, time)) =
      fun time : ℝ => (star (test xy.1) * value xy.2) * ((time : ℂ)⁻¹ * offDiagonalHeat time (xy.1 - xy.2)) := by
    funext time
    unfold triple
    ring
  rw [shape, integral_const_mul, kernel_clock_payment _ different]
  rfl

private theorem clock_read_integrable (test : SchwartzMap ℝ ℂ) (r : Hq)
    (support : tsupport test ⊆ Ioi q) : IntegrableOn (clockRead test (E r)) (Ioi 0) :=
  (compact_triple_integrable test r support).integral_prod_right

private theorem clock_integral_payment (test : SchwartzMap ℝ ℂ) (r : Hq)
    (support : tsupport test ⊆ Ioi q) :
    (∫ time : ℝ in Ioi 0, clockRead test (E r) time) =
      ∫ xy : ℝ × ℝ, spatialRead test (E r) xy ∂volume.prod volume := by
  have joint := compact_triple_integrable test r support
  unfold clockRead
  rw [← integral_integral_swap (f := fun xy time => triple test (E r) (xy, time)) joint]
  exact integral_congr_ae (clock_collapse test (E r))

private theorem clock_physical_pairing (test : SchwartzMap ℝ ℂ) (r : Hq)
    (support : tsupport test ⊆ Ioi q) :
    ∀ᵐ time : ℝ ∂volume.restrict (Ioi 0), ∀ positive : 0 < time,
      clockRead test (E r) time = (time : ℂ)⁻¹ *
        inner ℂ ((sourceHeatCotest time positive test).toLp 2 volume) (E r) := by
  have rows := (compact_triple_integrable test r support).prod_left_ae
  filter_upwards [rows] with time row
  intro positive
  have paired : inner ℂ ((sourceHeatCotest time positive test).toLp 2 volume) (E r) =
      ∫ y : ℝ, (E r) y * ∫ x : ℝ, star (test x) * offDiagonalHeat time (y - x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(sourceHeatCotest time positive test).coeFn_toLp 2 volume] with y actual
    rw [actual, RCLike.inner_apply, starRingEnd_apply, source_heat_cotest_physical, Complex.star_def, ← integral_conj]
    apply congrArg (E r y * ·)
    apply integral_congr_ae
    filter_upwards with x
    change star (offDiagonalHeat time (y - x) * test x) =
      star (test x) * offDiagonalHeat time (y - x)
    rw [star_mul, heat_real]
  rw [paired, ← integral_const_mul]
  have swapped : clockRead test (E r) time =
      ∫ y : ℝ, ∫ x : ℝ, triple test (E r) ((x, y), time) := by
    unfold clockRead
    rw [← integral_prod_swap (fun xy : ℝ × ℝ => triple test (E r) (xy, time)), integral_prod (fun xy : ℝ × ℝ => triple test (E r) (xy.swap, time)) row.swap]
    rfl
  rw [swapped]
  apply integral_congr_ae
  filter_upwards with y
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [triple]
  rw [heat_swap time x y]
  ring

private theorem compact_cotest_read_zero (test : SchwartzMap ℝ ℂ) (r : Hq)
    (support : tsupport test ⊆ Ioi q) : inner ℂ (test.toLp 2 volume) (E r) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [compact_value_outside r, test.coeFn_toLp 2 volume] with x outside actual
  rw [actual, RCLike.inner_apply]
  by_cases testZero : test x = 0
  · simp only [testZero, map_zero, mul_zero, Pi.zero_apply]
  · have positive : q < |x| := by
      rw [abs_of_pos ((by norm_num : (0 : ℝ) < q).trans (support (subset_tsupport test testZero)))]
      exact support (subset_tsupport test testZero)
    simp only [outside positive, zero_mul, Pi.zero_apply]

private theorem compact_log_cotest_read_zero (test : SchwartzMap ℝ ℂ) (r : Hq)
    (support : tsupport test ⊆ Ioi q) : inner ℂ (logSchwartzL2 test) (E r) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [compact_value_outside r, original_log_schwartz_raw test] with x outside actual
  rw [actual, RCLike.inner_apply]
  by_cases testZero : test x = 0
  · simp [testZero]
  · have positive : q < |x| := by
      rw [abs_of_pos ((by norm_num : (0 : ℝ) < q).trans (support (subset_tsupport test testZero)))]
      exact support (subset_tsupport test testZero)
    simp only [outside positive, zero_mul, Pi.zero_apply]

private theorem gamma_heat_source (test : SchwartzMap ℝ ℂ) (r : Hq)
    (support : tsupport test ⊆ Ioi q) :
    Tendsto (fun N : ℕ => ∫ frequency : ℝ, star ((𝓕⁻ test) frequency) * (heatLogCut N frequency : ℂ) *
        (𝓕⁻ (E r)) frequency) atTop (𝓝 (inner ℂ (wholeConductorTest test) (E r))) := by
  have source := heat_log_paired_source_limit (𝓕⁻ test) (𝓕⁻ (E r))
  have paired := Lp.inner_fourier_eq (logSchwartzL2 (𝓕⁻ test)) (𝓕⁻ (E r))
  rw [fourier_fourierInv_eq] at paired
  unfold wholeConductorTest
  rw [inner_add_left, compact_log_cotest_read_zero test r support, zero_add]
  exact paired.symm ▸ source

private theorem clock_cut_limit (test : SchwartzMap ℝ ℂ) (r : Hq)
    (support : tsupport test ⊆ Ioi q) :
    Tendsto (fun N : ℕ => ∫ time : ℝ in Ioc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1), clockRead test (E r) time)
      atTop (𝓝 (∫ time : ℝ in Ioi 0, clockRead test (E r) time)) := by
  let h : ℝ → ℂ := clockRead test (E r)
  let cut : ℕ → ℝ → ℂ := fun N => (Ioc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1)).indicator h
  have whole : IntegrableOn h (Ioi 0) := clock_read_integrable test r support
  have measured (N : ℕ) : AEStronglyMeasurable (cut N) (volume.restrict (Ioi 0)) :=
    whole.aestronglyMeasurable.indicator measurableSet_Ioc
  have domination (N : ℕ) : ∀ᵐ time : ℝ ∂volume.restrict (Ioi 0), ‖cut N time‖ ≤ ‖h time‖ := by
    filter_upwards with time
    by_cases inside : time ∈ Ioc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1)
    · simp only [cut, indicator_of_mem inside]
      exact le_rfl
    · simp only [cut, indicator_of_notMem inside, norm_zero, norm_nonneg]
  have upper : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have point : ∀ᵐ time : ℝ ∂volume.restrict (Ioi 0), Tendsto (fun N : ℕ => cut N time) atTop (𝓝 (h time)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with time positive
    have lower := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds (show (0 : ℝ) < time from positive))
    have high := upper.eventually_ge_atTop time
    apply tendsto_const_nhds.congr'
    filter_upwards [lower, high] with N below above
    simp only [cut, indicator_of_mem (show time ∈ Ioc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1) from ⟨below, above⟩)]
  have source := tendsto_integral_of_dominated_convergence (fun time => ‖h time‖) measured whole.norm domination point
  have actual (N : ℕ) : (∫ time : ℝ in Ioi 0, cut N time) =
      ∫ time : ℝ in Ioc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1), h time := by
    unfold cut
    rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict_of_subset (by
      intro time inside
      exact (by positivity : (0 : ℝ) < 1 / ((N : ℝ) + 1)).trans inside.1)]
  simpa only [actual, h] using source

private theorem cut_clock_payment (N : ℕ) (test : SchwartzMap ℝ ℂ) (r : Hq)
    (support : tsupport test ⊆ Ioi q) :
    (∫ frequency : ℝ, star ((𝓕⁻ test) frequency) * (heatLogCut N frequency : ℂ) * (𝓕⁻ (E r)) frequency) =
      -(1 / 2 : ℂ) * ∫ time : ℝ in Ioc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1), clockRead test (E r) time := by
  have native := clock_physical_pairing test r support
  have nativeWhole := (ae_restrict_iff' measurableSet_Ioi).mp native
  rw [source_cut_frequency_clock]
  have read : (fun time : ℝ => ∫ frequency : ℝ, sourceFrequencyTriple test (E r) (time, frequency)) =ᵐ[
      volume.restrict (Ioc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1))]
      fun time => -clockRead test (E r) time := by
    filter_upwards [ae_restrict_of_ae nativeWhole, ae_restrict_mem measurableSet_Ioc] with time native interval
    have positive : 0 < time := (by positivity : (0 : ℝ) < 1 / ((N : ℝ) + 1)).trans interval.1
    rw [source_frequency_clock_point time positive test (E r), compact_cotest_read_zero test r support,
      mul_zero, zero_sub, native positive positive, mul_neg]
  rw [integral_congr_ae read, integral_neg]
  ring

private theorem compact_exterior_kernel_source (test : SchwartzMap ℝ ℂ) (r : Hq)
    (support : tsupport test ⊆ Ioi q) :
    inner ℂ (wholeConductorTest test) (E r) =
      -(1 / 2 : ℂ) * ∫ xy : ℝ × ℝ, star (test xy.1) * E r xy.2 * ((|xy.1 - xy.2|⁻¹ : ℝ) : ℂ) ∂volume.prod volume := by
  have native := gamma_heat_source test r support
  have clock := (clock_cut_limit test r support).const_mul (-(1 / 2 : ℂ))
  have same : (fun N : ℕ => -(1 / 2 : ℂ) * ∫ time : ℝ in Ioc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1), clockRead test (E r) time) =
      fun N : ℕ => ∫ frequency : ℝ, star ((𝓕⁻ test) frequency) * (heatLogCut N frequency : ℂ) * (𝓕⁻ (E r)) frequency := by
    funext N
    exact (cut_clock_payment N test r support).symm
  rw [same] at clock
  have read := tendsto_nhds_unique native clock
  rw [clock_integral_payment test r support] at read
  simpa only [spatialRead] using read

private def compactEvenProfile (r : Hq) (x : ℝ) : ℂ :=
  (symmetricInterval q).indicator (fun x : ℝ => r |x|) x

private theorem compact_even_profile_raw (r : Hq) (even : reflectRestricted q r = r) :
    (E r : ℝ → ℂ) =ᵐ[volume] compactEvenProfile r := by
  have reflected : (fun x : ℝ => r x) =ᵐ[μq] fun x : ℝ => r (-x) := by
    filter_upwards [Lp.coeFn_compMeasurePreserving r (negMeasurePreserving_restrict q)] with x source
    change reflectRestricted q r x = r (-x) at source
    rw [even] at source
    exact source
  have reflectedWhole := ae_imp_of_ae_restrict reflected
  filter_upwards [burnolQuarterZeroExtension_coe r, reflectedWhole] with x source parity
  rw [source]
  unfold compactEvenProfile
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem inside]
    by_cases positive : 0 ≤ x
    · rw [abs_of_nonneg positive]
    · rw [abs_of_neg (lt_of_not_ge positive)]
      exact parity inside
  · rw [indicator_of_notMem inside, indicator_of_notMem inside]

private def compactKernelRaw (x y : ℝ) : ℂ :=
  (symmetricInterval q).indicator (fun y : ℝ => ((|x - y|⁻¹ : ℝ) : ℂ)) y

private theorem compact_kernel_memLp (x : ℝ) (outside : q < x) : MemLp (compactKernelRaw x) 2 volume := by
  apply (memLp_indicator_iff_restrict (measurableSet_symmetricInterval q)).mpr
  apply MemLp.of_bound (C := (x - q)⁻¹) (by fun_prop)
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with y inside
  have apart : 0 < x - y := by linarith [inside.2]
  have lower : 0 < x - q := sub_pos.mpr outside
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos apart, abs_of_pos (inv_pos.mpr apart)]
  simpa only [one_div] using one_div_le_one_div_of_le lower (by linarith [inside.2] : x - q ≤ x - y)

private def compactKernel (x : ℝ) (outside : q < x) : BurnolL2 :=
  (compact_kernel_memLp x outside).toLp (compactKernelRaw x)

private theorem compact_kernel_inner (x : ℝ) (outside : q < x) (r : Hq) :
    inner ℂ (compactKernel x outside) (E r) =
      ∫ y : ℝ, E r y * ((|x - y|⁻¹ : ℝ) : ℂ) := by
  rw [L2.inner_def]
  have source : (compactKernel x outside : ℝ → ℂ) =ᵐ[volume] compactKernelRaw x :=
    (compact_kernel_memLp x outside).coeFn_toLp
  apply integral_congr_ae
  filter_upwards [source, burnolQuarterZeroExtension_coe r] with y kernel profile
  rw [kernel, profile, RCLike.inner_apply, starRingEnd_apply]
  unfold compactKernelRaw
  by_cases inside : y ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem inside]
    simp only [Complex.star_def, Complex.conj_ofReal]
  · rw [indicator_of_notMem inside, indicator_of_notMem inside]
    simp only [star_zero, mul_zero, zero_mul]

private theorem compact_kernel_q_sum (x t : ℝ) (outside : q < x) (inside : t ∈ Ioc 0 q) :
    star (compactKernelRaw x t) + star (compactKernelRaw x (-t)) =
      (2 : ℂ) * ((x / (x ^ 2 - t ^ 2) : ℝ) : ℂ) := by
  have positive : 0 < x := (by norm_num : (0 : ℝ) < q).trans outside
  have tInside : t ∈ symmetricInterval q := ⟨by linarith [inside.1], inside.2⟩
  have ntInside : -t ∈ symmetricInterval q := ⟨by linarith [inside.2], by linarith [inside.1]⟩
  have first : 0 < x - t := by linarith [inside.2]
  have second : 0 < x + t := by linarith [inside.1]
  unfold compactKernelRaw
  rw [indicator_of_mem tInside, indicator_of_mem ntInside]
  simp only [sub_neg_eq_add, abs_of_pos first, abs_of_pos second,
    Complex.star_def, Complex.conj_ofReal]
  have denominator : x ^ 2 - t ^ 2 ≠ 0 := by
    rw [show x ^ 2 - t ^ 2 = (x - t) * (x + t) by ring]
    exact mul_ne_zero first.ne' second.ne'
  have scalar : (x - t)⁻¹ + (x + t)⁻¹ = 2 * (x / (x ^ 2 - t ^ 2)) := by
    field_simp [first.ne', second.ne', denominator]
    ring
  exact_mod_cast scalar

private theorem compact_half_profile_read (x : ℝ) (outside : q < x) (r : Hq)
    (even : reflectRestricted q r = r) :
    (∫ y : ℝ, E r y * ((|x - y|⁻¹ : ℝ) : ℂ)) =
      (2 : ℂ) * ∫ t : ℝ in Ioc 0 q, ((x / (x ^ 2 - t ^ 2) : ℝ) : ℂ) * r t := by
  have kernel : (compactKernel x outside : ℝ → ℂ) =ᵐ[volume] compactKernelRaw x :=
    (compact_kernel_memLp x outside).coeFn_toLp
  have source := compact_profile_pairing (compactKernel x outside) (E r)
    (compactKernelRaw x) (compactEvenProfile r) kernel (compact_even_profile_raw r even)
    (fun t : ℝ => by
      have parity : -t ∈ symmetricInterval q ↔ t ∈ symmetricInterval q := by
        simp only [symmetricInterval, mem_Icc]
        constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
      unfold compactEvenProfile
      by_cases inside : t ∈ symmetricInterval q
      · rw [indicator_of_mem (parity.mpr inside), indicator_of_mem inside, abs_neg]
      · rw [indicator_of_notMem (fun h => inside (parity.mp h)), indicator_of_notMem inside])
    (fun t large => by
      unfold compactEvenProfile
      rw [indicator_of_notMem (show t ∉ symmetricInterval q from fun h => not_le.mpr large (abs_le.mpr h))])
  rw [compact_kernel_inner] at source
  rw [source, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
  rw [compact_kernel_q_sum x t outside inside]
  unfold compactEvenProfile
  rw [indicator_of_mem (show t ∈ symmetricInterval q from ⟨by linarith [inside.1], inside.2⟩),
    abs_of_pos inside.1]
  ring

private theorem compact_exterior_stieltjes (test : SchwartzMap ℝ ℂ) (r : Hq)
    (even : reflectRestricted q r = r) (support : tsupport test ⊆ Ioi q) :
    inner ℂ (wholeConductorTest test) (E r) =
      -∫ x : ℝ, star (test x) * ∫ t : ℝ in Ioc 0 q, ((x / (x ^ 2 - t ^ 2) : ℝ) : ℂ) * r t := by
  have budget := (compact_triple_integrable test r support).integral_prod_left.congr (clock_collapse test (E r))
  rw [compact_exterior_kernel_source test r support]
  have source : (∫ xy : ℝ × ℝ, spatialRead test (E r) xy ∂volume.prod volume) =
      (2 : ℂ) * ∫ x : ℝ, star (test x) * ∫ t : ℝ in Ioc 0 q, ((x / (x ^ 2 - t ^ 2) : ℝ) : ℂ) * r t := by
    rw [integral_prod _ budget, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [spatialRead, mul_assoc]
    rw [integral_const_mul]
    by_cases testZero : test x = 0
    · simp only [testZero, star_zero, zero_mul, mul_zero]
    · rw [compact_half_profile_read x (support (subset_tsupport test testZero)) r even]
      ring
  change -(1 / 2 : ℂ) * (∫ xy : ℝ × ℝ, spatialRead test (E r) xy ∂volume.prod volume) = _
  rw [source]
  ring

end
end OriginalGamma.Source.CompactConductorExterior
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
