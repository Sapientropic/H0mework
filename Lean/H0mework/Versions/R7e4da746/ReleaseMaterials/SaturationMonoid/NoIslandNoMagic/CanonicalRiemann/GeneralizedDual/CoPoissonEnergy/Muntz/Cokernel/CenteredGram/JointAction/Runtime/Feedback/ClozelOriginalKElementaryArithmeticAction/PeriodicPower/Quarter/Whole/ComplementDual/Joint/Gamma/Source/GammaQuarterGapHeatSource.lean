import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Interval
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.Order.Floor
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.ConductorDualSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FiniteLogCountingSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.JointLogConductorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KappaConductorTailSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.GammaQuarterGapHeat
open Complex Filter FourierTransform MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.KappaConductor
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.JointLogConductor
open OriginalGamma.Source.RelativeConductorGapReadback
noncomputable section
local notation "q" => (1/4:ℝ)
macro "quarterGapHeatPaid% " field:ident : term => do
  let owner:=Lean.Name.num (if #["source_kernel_tail_bound","sourceTriple","source_triple_measured","sourceFrequencyTriple","source_frequency_clock_point","source_heat_product_integrable","source_inverse_pairing","source_heat_actual_pairing","source_inverse_product_integrable","source_cut_frequency_clock","source_frequency_triple_integrable","compact_profile_pairing","full_half_fold"].contains field.getId.eraseMacroScopes.toString then `_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KappaConductorTailSource else `_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KappaConductorSource) 0
  let scope:=`SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalGamma.Source.KappaConductor
  return Lean.mkIdent (owner.append (scope.append field.getId))
private abbrev offDiagonalHeat (time distance : ℝ) : ℂ :=
  (Real.sqrt (Real.pi/time)*Real.exp (-(Real.pi^2*distance^2/time)):ℝ)
private abbrev heatLogCut := quarterGapHeatPaid% heatLogCut
private abbrev heat_log_paired_source_limit := quarterGapHeatPaid% heat_log_paired_source_limit
private abbrev sourceHeatCotest := quarterGapHeatPaid% sourceHeatCotest
private theorem source_heat_cotest_physical (time : ℝ) (positive : 0<time)
    (test : SchwartzMap ℝ ℂ) (y : ℝ) :
    sourceHeatCotest time positive test y=∫x:ℝ,offDiagonalHeat time (y-x)*test x :=
  (quarterGapHeatPaid% source_heat_cotest_physical) time positive test y
private abbrev sourceFrequencyTriple := quarterGapHeatPaid% sourceFrequencyTriple
private abbrev source_triple_measured := quarterGapHeatPaid% source_triple_measured
private theorem kernel_clock_integrable (distance : ℝ) (nonzero : distance≠0) :
    IntegrableOn (fun time:ℝ=>(time:ℂ)⁻¹*offDiagonalHeat time distance) (Ioi 0) :=
  (quarterGapHeatPaid% kernel_clock_integrable) distance nonzero
private theorem kernel_clock_norm_payment (distance : ℝ) (nonzero : distance≠0) :
    (∫time:ℝ in Ioi 0,‖(time:ℂ)⁻¹*offDiagonalHeat time distance‖)=|distance|⁻¹ :=
  (quarterGapHeatPaid% kernel_clock_norm_payment) distance nonzero
private theorem kernel_clock_payment (distance : ℝ) (nonzero : distance≠0) :
    (∫time:ℝ in Ioi 0,(time:ℂ)⁻¹*offDiagonalHeat time distance)=((|distance|⁻¹:ℝ):ℂ) :=
  (quarterGapHeatPaid% kernel_clock_payment) distance nonzero
private abbrev tailWeight (y : ℝ) : ℝ := (1+|y|)⁻¹
private theorem tail_weight_memLp : MemLp tailWeight 2 volume :=
  quarterGapHeatPaid% tail_weight_memLp
private theorem source_kernel_tail_bound (delta x y : ℝ) (positive : 0<delta)
    (bounded : |x|≤4) (apart : delta≤|x-y|) :
    |x-y|⁻¹≤(1+5/delta)*tailWeight y :=
  (quarterGapHeatPaid% source_kernel_tail_bound) delta x y positive bounded apart
private abbrev source_cut_frequency_clock := quarterGapHeatPaid% source_cut_frequency_clock
private abbrev source_frequency_clock_point := quarterGapHeatPaid% source_frequency_clock_point
private abbrev sourceTriple (test : SchwartzMap ℝ ℂ) (value : BurnolL2) (p : (ℝ×ℝ)×ℝ) : ℂ :=
  star (test p.1.1)*value p.1.2*(p.2:ℂ)⁻¹*offDiagonalHeat p.2 (p.1.1-p.1.2)
private theorem source_cotest_buffer (test : SchwartzMap ℝ ℂ) (support : tsupport test ⊆ Ioo (0:ℝ) q) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ x ∈ tsupport test, delta ≤ x - 0 ∧ delta ≤ q - x := by
  have compact : IsCompact (tsupport test) := isCompact_Icc.of_isClosed_subset (isClosed_tsupport test)
    (support.trans Ioo_subset_Icc_self)
  obtain ⟨delta, positive, bounded⟩ := compact.exists_forall_le'
    (f := fun x : ℝ => min (x - 0) (q - x)) (by fun_prop) (a := (0 : ℝ)) (by
      intro x inside
      have point := support inside
      exact lt_min (sub_pos.mpr point.1) (sub_pos.mpr point.2))
  exact ⟨delta, positive, fun x inside => le_min_iff.mp (bounded x inside)⟩

private theorem source_triple_integrable (test : SchwartzMap ℝ ℂ) (value : BurnolL2)
    (support : tsupport test ⊆ Ioo (0:ℝ) q) (window : ∀ᵐ y : ℝ ∂volume, y ∈ Ioo (0:ℝ) q → value y = 0) :
    Integrable (sourceTriple test value) ((volume.prod volume).prod (volume.restrict (Ioi 0))) := by
  obtain ⟨delta, positive, buffer⟩ := source_cotest_buffer test support
  let C : ℝ := 1 + 5 / delta
  have measured : AEStronglyMeasurable (sourceTriple test value) ((volume.prod volume).prod (volume.restrict (Ioi 0))) := source_triple_measured test value
  have normalized : Integrable (fun y : ℝ => tailWeight y * ‖value y‖) :=
    tail_weight_memLp.integrable_mul (Lp.memLp value).norm
  have domination : Integrable (fun xy : ℝ × ℝ => C * ‖test xy.1‖ * (tailWeight xy.2 * ‖value xy.2‖))
      (volume.prod volume) := by
    simpa only [mul_assoc] using ((test.integrable.norm).mul_prod normalized).const_mul C
  have wholeWindow : ∀ᵐ xy : ℝ × ℝ ∂volume.prod volume, xy.2 ∈ Ioo (0:ℝ) q → value xy.2 = 0 :=
    Measure.quasiMeasurePreserving_snd.ae window
  have apart (x y : ℝ) (testNonzero : test x ≠ 0) (valueNonzero : value y ≠ 0)
      (gap : y ∈ Ioo (0:ℝ) q → value y = 0) : delta ≤ |x - y| := by
    have point := buffer x (subset_tsupport test testNonzero)
    by_cases lower : y ≤ 0
    · have oriented : 0 ≤ x - y := by linarith [point.1]
      rw [abs_of_nonneg oriented]
      linarith [point.1]
    · have upper : q ≤ y := by
        by_contra fails
        exact valueNonzero (gap ⟨lt_of_not_ge lower, lt_of_not_ge fails⟩)
      have oriented : x - y ≤ 0 := by linarith [point.2]
      rw [abs_of_nonpos oriented]
      linarith [point.2]
  have allClocks : ∀ᵐ xy : ℝ × ℝ ∂volume.prod volume,
      IntegrableOn (fun time : ℝ => sourceTriple test value (xy, time)) (Ioi 0) := by
    filter_upwards [wholeWindow] with xy gap
    by_cases testZero : test xy.1 = 0
    · simp only [sourceTriple, testZero, star_zero, zero_mul, IntegrableOn]
      convert integrable_zero ℝ ℂ (volume.restrict (Ioi 0)) using 1 <;> rfl
    by_cases valueZero : value xy.2 = 0
    · simp only [sourceTriple, valueZero, mul_zero, zero_mul, IntegrableOn]
      convert integrable_zero ℝ ℂ (volume.restrict (Ioi 0)) using 1 <;> rfl
    have distance := positive.trans_le (apart xy.1 xy.2 testZero valueZero gap)
    have source := (kernel_clock_integrable (xy.1 - xy.2) ((by intro equal; simp only [equal, abs_zero, lt_self_iff_false] at distance))).const_mul
      (star (test xy.1) * value xy.2)
    simpa only [sourceTriple, mul_assoc, IntegrableOn] using source
  have totalBudget : Integrable (fun xy : ℝ × ℝ => ∫ time : ℝ in Ioi 0, ‖sourceTriple test value (xy, time)‖)
      (volume.prod volume) := by
    apply domination.mono' measured.norm.integral_prod_right'
    filter_upwards [wholeWindow] with xy gap
    have cNonnegative : 0 ≤ C := by dsimp [C]; positivity
    have weightNonnegative : 0 ≤ tailWeight xy.2 := by unfold tailWeight; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    by_cases testZero : test xy.1 = 0
    · simp only [sourceTriple, testZero, star_zero, zero_mul, norm_zero, integral_zero]
      positivity
    by_cases valueZero : value xy.2 = 0
    · simp only [sourceTriple, valueZero, mul_zero, zero_mul, norm_zero, integral_zero]
      positivity
    have distance := positive.trans_le (apart xy.1 xy.2 testZero valueZero gap)
    have nonzero : xy.1 - xy.2 ≠ 0 := by intro equal; simp only [equal, abs_zero, lt_self_iff_false] at distance
    have normalizedClock : (∫ time : ℝ in Ioi 0, ‖sourceTriple test value (xy, time)‖) =
        ‖test xy.1‖ * ‖value xy.2‖ * |xy.1 - xy.2|⁻¹ := by
      have shape : (fun time : ℝ => ‖sourceTriple test value (xy, time)‖) =
          fun time : ℝ => (‖test xy.1‖ * ‖value xy.2‖) * ‖(time : ℂ)⁻¹ * offDiagonalHeat time (xy.1 - xy.2)‖ := by
        funext time
        simp only [sourceTriple, norm_mul, norm_star]
        ring_nf
      rw [shape, integral_const_mul, kernel_clock_norm_payment _ nonzero]
    rw [normalizedClock]
    have point := support (subset_tsupport test testZero)
    have bounded : |xy.1| ≤ 4 := by rw [abs_of_pos point.1]; linarith [point.2]
    have source := source_kernel_tail_bound delta xy.1 xy.2 positive bounded (apart xy.1 xy.2 testZero valueZero gap)
    calc
      _ ≤ (‖test xy.1‖ * ‖value xy.2‖) * (C * tailWeight xy.2) :=
        mul_le_mul_of_nonneg_left source (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  exact (integrable_prod_iff measured).mpr ⟨allClocks, totalBudget⟩

private def sourceClockRead (test : SchwartzMap ℝ ℂ) (value : BurnolL2) (time : ℝ) : ℂ :=
  ∫ xy : ℝ × ℝ, sourceTriple test value (xy, time) ∂volume.prod volume

private def sourceSpatialRead (test : SchwartzMap ℝ ℂ) (value : BurnolL2) (xy : ℝ × ℝ) : ℂ :=
  star (test xy.1) * value xy.2 * ((|xy.1 - xy.2|⁻¹ : ℝ) : ℂ)

private theorem source_clock_read_integrable (test : SchwartzMap ℝ ℂ) (value : BurnolL2)
    (support : tsupport test ⊆ Ioo (0:ℝ) q) (window : ∀ᵐ y : ℝ ∂volume, y ∈ Ioo (0:ℝ) q → value y = 0) :
    IntegrableOn (sourceClockRead test value) (Ioi 0) :=
  (source_triple_integrable test value support window).integral_prod_right

private theorem source_clock_collapse (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    (fun xy : ℝ × ℝ => ∫ time : ℝ in Ioi 0, sourceTriple test value (xy, time)) =ᵐ[volume.prod volume]
      sourceSpatialRead test value := by
  have diagonal : ∀ᵐ xy : ℝ × ℝ ∂volume.prod volume, xy.1 - xy.2 ≠ 0 := by
    apply (Measure.ae_prod_iff_ae_ae (show MeasurableSet {xy : ℝ × ℝ | xy.1 - xy.2 ≠ 0} from (isClosed_eq (by fun_prop : Continuous (fun xy : ℝ × ℝ => xy.1 - xy.2)) continuous_const).measurableSet.compl)).mpr
    filter_upwards with x
    filter_upwards [volume.ae_ne x] with y different
    exact sub_ne_zero.mpr different.symm
  filter_upwards [diagonal] with xy different
  have shape : (fun time : ℝ => sourceTriple test value (xy, time)) =
      fun time : ℝ => (star (test xy.1) * value xy.2) * ((time : ℂ)⁻¹ * offDiagonalHeat time (xy.1 - xy.2)) := by
    funext time
    unfold sourceTriple
    ring_nf
  rw [shape, integral_const_mul, kernel_clock_payment _ different]
  rfl

private theorem source_spatial_read_integrable (test : SchwartzMap ℝ ℂ) (value : BurnolL2)
    (support : tsupport test ⊆ Ioo (0:ℝ) q) (window : ∀ᵐ y : ℝ ∂volume, y ∈ Ioo (0:ℝ) q → value y = 0) :
    Integrable (sourceSpatialRead test value) (volume.prod volume) :=
  (source_triple_integrable test value support window).integral_prod_left.congr (source_clock_collapse test value)

private theorem source_clock_integral_payment (test : SchwartzMap ℝ ℂ) (value : BurnolL2)
    (support : tsupport test ⊆ Ioo (0:ℝ) q) (window : ∀ᵐ y : ℝ ∂volume, y ∈ Ioo (0:ℝ) q → value y = 0) :
    (∫ time : ℝ in Ioi 0, sourceClockRead test value time) = ∫ xy : ℝ × ℝ, sourceSpatialRead test value xy ∂volume.prod volume := by
  have joint := source_triple_integrable test value support window
  unfold sourceClockRead
  rw [← integral_integral_swap (f := fun xy time => sourceTriple test value (xy, time)) joint]
  exact integral_congr_ae (source_clock_collapse test value)

private theorem source_clock_physical_pairing (test : SchwartzMap ℝ ℂ) (value : BurnolL2)
    (support : tsupport test ⊆ Ioo (0:ℝ) q) (window : ∀ᵐ y : ℝ ∂volume, y ∈ Ioo (0:ℝ) q → value y = 0) :
    ∀ᵐ time : ℝ ∂volume.restrict (Ioi 0), ∀ positive : 0 < time,
      sourceClockRead test value time = (time : ℂ)⁻¹ *
        inner ℂ ((sourceHeatCotest time positive test).toLp 2 volume) value := by
  have rows := (source_triple_integrable test value support window).prod_left_ae
  filter_upwards [rows] with time row
  intro positive
  have paired : inner ℂ ((sourceHeatCotest time positive test).toLp 2 volume) value =
      ∫ y : ℝ, value y * ∫ x : ℝ, star (test x) * offDiagonalHeat time (y - x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(sourceHeatCotest time positive test).coeFn_toLp 2 volume] with y actual
    rw [actual, RCLike.inner_apply, starRingEnd_apply, source_heat_cotest_physical, Complex.star_def, ← integral_conj]
    apply congrArg (value y * ·)
    apply integral_congr_ae
    filter_upwards with x
    unfold offDiagonalHeat
    rw [map_mul, Complex.conj_ofReal, starRingEnd_apply]
    change _ = star (test x) * _
    ring_nf
  rw [paired, ← integral_const_mul]
  have swapped : sourceClockRead test value time =
      ∫ y : ℝ, ∫ x : ℝ, sourceTriple test value ((x, y), time) := by
    unfold sourceClockRead
    rw [← integral_prod_swap (fun xy : ℝ × ℝ => sourceTriple test value (xy, time)), integral_prod (fun xy : ℝ × ℝ => sourceTriple test value (xy.swap, time)) row.swap]
    rfl
  rw [swapped]
  apply integral_congr_ae
  filter_upwards with y
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  unfold sourceTriple offDiagonalHeat
  rw [show (x - y) ^ 2 = (y - x) ^ 2 by ring]
  ring_nf

private theorem source_clock_cut_limit (test : SchwartzMap ℝ ℂ) (value : BurnolL2)
    (support : tsupport test ⊆ Ioo (0:ℝ) q) (window : ∀ᵐ y : ℝ ∂volume, y ∈ Ioo (0:ℝ) q → value y = 0) :
    Tendsto (fun N : ℕ => ∫ time : ℝ in Ioc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1), sourceClockRead test value time)
      atTop (𝓝 (∫ time : ℝ in Ioi 0, sourceClockRead test value time)) := by
  let h : ℝ → ℂ := sourceClockRead test value
  let cut : ℕ → ℝ → ℂ := fun N => (Ioc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1)).indicator h
  have whole : IntegrableOn h (Ioi 0) := source_clock_read_integrable test value support window
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


private theorem cotest_first_read_zero (test : SchwartzMap ℝ ℂ) (value : BurnolL2)
    (support : tsupport test ⊆ Ioo (0:ℝ) q)
    (window : ∀ᵐ y:ℝ ∂volume,y∈Ioo (0:ℝ) q→value y=0) :
    inner ℂ (test.toLp 2 volume) value=0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [window,test.coeFn_toLp 2 volume] with x gap native
  rw [native,RCLike.inner_apply]
  by_cases vanishes : test x=0
  · simp only [vanishes,map_zero,mul_zero,Pi.zero_apply]
  · simp only [gap (support (subset_tsupport test vanishes)),zero_mul,Pi.zero_apply]

private theorem cotest_log_read_zero (test : SchwartzMap ℝ ℂ) (value : BurnolL2)
    (support : tsupport test ⊆ Ioo (0:ℝ) q)
    (window : ∀ᵐ y:ℝ ∂volume,y∈Ioo (0:ℝ) q→value y=0) :
    inner ℂ (logSchwartzL2 test) value=0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [window,original_log_schwartz_raw test] with x gap logarithm
  rw [logarithm,RCLike.inner_apply]
  by_cases vanishes : test x=0
  · simp [vanishes]
  · simp only [gap (support (subset_tsupport test vanishes)),zero_mul,Pi.zero_apply]

private theorem gamma_heat_source (test : SchwartzMap ℝ ℂ) (value : BurnolL2)
    (support : tsupport test ⊆ Ioo (0:ℝ) q)
    (window : ∀ᵐ y:ℝ ∂volume,y∈Ioo (0:ℝ) q→value y=0) :
    Tendsto (fun N:ℕ=>∫frequency:ℝ,star ((𝓕⁻ test) frequency)*(heatLogCut N frequency:ℂ)*(𝓕⁻ value) frequency)
      atTop (𝓝 (inner ℂ (wholeConductorTest test) value)) := by
  have source:=heat_log_paired_source_limit (𝓕⁻ test) (𝓕⁻ value)
  have paired:=Lp.inner_fourier_eq (logSchwartzL2 (𝓕⁻ test)) (𝓕⁻ value)
  rw [fourier_fourierInv_eq] at paired
  rw [wholeConductorTest,inner_add_left,cotest_log_read_zero test value support window,zero_add]
  exact paired.symm ▸ source

private theorem cut_clock_payment (N : ℕ) (test : SchwartzMap ℝ ℂ) (value : BurnolL2)
    (support : tsupport test ⊆ Ioo (0:ℝ) q)
    (window : ∀ᵐ y:ℝ ∂volume,y∈Ioo (0:ℝ) q→value y=0) :
    (∫frequency:ℝ,star ((𝓕⁻ test) frequency)*(heatLogCut N frequency:ℂ)*(𝓕⁻ value) frequency)=
      -(1/2:ℂ)*∫time:ℝ in Ioc (1/((N:ℝ)+1)) ((N:ℝ)+1),sourceClockRead test value time := by
  have native:=source_clock_physical_pairing test value support window
  have nativeWhole:=(ae_restrict_iff' measurableSet_Ioi).mp native
  rw [source_cut_frequency_clock]
  have read : (fun time:ℝ=>∫frequency:ℝ,sourceFrequencyTriple test value (time,frequency))=ᵐ[
      volume.restrict (Ioc (1/((N:ℝ)+1)) ((N:ℝ)+1))]
      fun time=>-sourceClockRead test value time := by
    filter_upwards [ae_restrict_of_ae nativeWhole,ae_restrict_mem measurableSet_Ioc] with time native interval
    have positive : 0<time := (by positivity : (0:ℝ)<1/((N:ℝ)+1)).trans interval.1
    rw [source_frequency_clock_point time positive test value,
      cotest_first_read_zero test value support window,mul_zero,zero_sub,native positive positive,mul_neg]
  rw [integral_congr_ae read,integral_neg]
  ring_nf

private theorem gamma_gap_source (test : SchwartzMap ℝ ℂ) (value : BurnolL2)
    (support : tsupport test ⊆ Ioo (0:ℝ) q)
    (window : ∀ᵐ y:ℝ ∂volume,y∈Ioo (0:ℝ) q→value y=0) :
    inner ℂ (wholeConductorTest test) value=
      -(1/2:ℂ)*∫xy:ℝ×ℝ,star (test xy.1)*value xy.2*((|xy.1-xy.2|⁻¹:ℝ):ℂ) ∂volume.prod volume := by
  have native:=gamma_heat_source test value support window
  have clock:=(source_clock_cut_limit test value support window).const_mul (-(1/2:ℂ))
  have same : (fun N:ℕ=>-(1/2:ℂ)*∫time:ℝ in Ioc (1/((N:ℝ)+1)) ((N:ℝ)+1),sourceClockRead test value time)=
      fun N:ℕ=>∫frequency:ℝ,star ((𝓕⁻ test) frequency)*(heatLogCut N frequency:ℂ)*(𝓕⁻ value) frequency := by
    funext N
    exact (cut_clock_payment N test value support window).symm
  rw [same] at clock
  have read:=tendsto_nhds_unique native clock
  rw [source_clock_integral_payment test value support window] at read
  simpa only [sourceSpatialRead] using read

end
end OriginalGamma.Source.GammaQuarterGapHeat
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
