import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaGapLocalSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaIterated.Position
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.ExpandedGap

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.ConductorFaithfulness

open BurnolPhysicalState Complex Filter MeasureTheory Set
open OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.GammaGapLocal
open OriginalGamma.Source.KGamma.Iterated
open scoped InnerProductSpace Topology

open private interval_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.ExpandedGap
open private actual_gap_kernel_domain from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaGapLocalSource

local notation "q" => (1/4 : ℝ)
local notation "edge" => (1/8 : ℝ)
local notation "T" => burnolTateReciprocalL2

private theorem zero_gap_of_zero_conductor (w : BurnolL2) (gap : w ∈ locallyConstantFace q)
    (silent : GammaPair w 0) : ∀ᵐ x : ℝ ∂volume, |x| < q → w x = 0 := by
  obtain ⟨mean, read⟩ := interval_read gap
  have constant : ∀ᵐ x : ℝ ∂volume, |x| < q → w x = mean := by
    filter_upwards [read] with x source inside
    exact source (abs_le.mp inside.le)
  suffices mean = 0 by simpa only [this] using constant
  by_contra live
  obtain ⟨bound, nonnegative, near⟩ := actual_constant_gap_gamma_origin w 0 mean silent constant
  have positive := norm_pos_iff.mpr live
  let r := min edge (Real.exp (-(bound/‖mean‖+1)))
  have rPos : 0 < r := lt_min (by norm_num) (Real.exp_pos _)
  have nonnull : (volume : Measure ℝ) (Ioo 0 r) ≠ 0 := by
    rw [Real.volume_Ioo, sub_zero]
    exact (ENNReal.ofReal_pos.mpr rPos).ne'
  have cost : ∀ᵐ x : ℝ ∂volume.restrict (Ioo 0 r), |Real.log x| * ‖mean‖ ≤ bound := by
    filter_upwards [ae_restrict_of_ae (s := Ioo 0 r) near,
      ae_restrict_of_ae (s := Ioo 0 r) (Lp.coeFn_zero (α := ℝ) (E := ℂ) (p := 2) (μ := volume)),
      ae_restrict_mem measurableSet_Ioo] with x inside zero support
    have paid := inside ⟨support.1, support.2.trans_le (min_le_left _ _)⟩
    have erased : (0 : BurnolL2) x = (0 : ℂ) := by simpa only [Pi.zero_apply] using zero
    rwa [erased, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos support.1] at paid
  obtain ⟨x, inside, bounded⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae nonnull cost
  have small : Real.log x < -(bound/‖mean‖+1) :=
    (Real.log_lt_iff_lt_exp inside.1).mpr (inside.2.trans_le (min_le_right _ _))
  have negative : Real.log x < 0 := small.trans_le (by
    have paid := div_nonneg nonnegative positive.le
    linarith)
  have forced := mul_lt_mul_of_pos_right (neg_lt_neg small) positive
  rw [neg_neg, add_mul, div_mul_cancel₀ _ positive.ne', one_mul] at forced
  rw [abs_of_neg negative] at bounded
  linarith

private theorem integral_inverse_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) :
    (∫ y in Ioi q, f y) = ∫ t in Ioo (0:ℝ) 4, (t^2)⁻¹ • f t⁻¹ := by
  have image : (fun t : ℝ => t⁻¹) '' Ioo (0:ℝ) 4 = Ioi q := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (lt_inv_comm₀ (by norm_num : 0 < q) ht.1).mpr
        (by simpa only [show q⁻¹ = 4 by norm_num] using ht.2)
    · intro hy
      have positive : 0 < y := (by norm_num : 0 < q).trans hy
      refine ⟨y⁻¹, ⟨inv_pos.mpr positive, ?_⟩, inv_inv _⟩
      exact (inv_lt_comm₀ positive (by norm_num : (0:ℝ) < 4)).mpr
        (by simpa only [show (4:ℝ)⁻¹ = q by norm_num] using (show q < y from hy))
  have actual := integral_image_eq_integral_abs_deriv_smul (s := Ioo (0:ℝ) 4)
    measurableSet_Ioo (fun x hx => (hasDerivAt_inv hx.1.ne').hasDerivWithinAt)
    (fun _ _ _ _ equal => inv_injective equal) f
  rw [image] at actual
  have nonnegative (t : ℝ) : |(t^2)⁻¹| = (t^2)⁻¹ :=
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))
  simpa only [abs_neg, nonnegative] using actual

/-- The actual off-diagonal read in reciprocal source coordinates. -/
def reciprocalGapRead (w : BurnolL2) (x : ℝ) : ℂ :=
  ∫ t in Ioo (0:ℝ) 4, (1 - (x*t)^2)⁻¹ • (T w) t

private theorem gap_raw_reciprocal (w : BurnolL2) (even : reflectL2 w = w)
    (gap : ∀ᵐ y : ℝ ∂volume, |y| < q → w y = 0) (x : ℝ) (inside : x ∈ Icc (0:ℝ) edge) :
    originalGapGammaRaw w x = -reciprocalGapRead w x := by
  let f (y : ℝ) := w y * ((|x-y|⁻¹ : ℝ) : ℂ)
  have integrable : Integrable f := (actual_gap_kernel_domain w gap x inside).1
  have reflected : Integrable (fun y : ℝ => f (-y)) :=
    negMeasurePreserving.integrable_comp_of_integrable integrable
  have split := integral_add_compl (s := Ioi (0:ℝ)) measurableSet_Ioi integrable
  rw [compl_Ioi] at split
  have whole : (∫ y : ℝ in Ioi (0:ℝ), f y + f (-y)) = ∫ y : ℝ, f y := by
    rw [integral_add integrable.integrableOn reflected.integrableOn, integral_comp_neg_Ioi, neg_zero, split]
  have raw := Lp.coeFn_compMeasurePreserving w negMeasurePreserving
  change (reflectL2 w : ℝ → ℂ) =ᵐ[volume] fun y => w (-y) at raw
  rw [even] at raw
  let g (y : ℝ) := (y⁻¹ / (1-(x*y⁻¹)^2)) • w y
  have tail : (∫ y : ℝ in Ioi (0:ℝ), f y + f (-y)) =
      ∫ y : ℝ in Ioi q, (2:ℝ) • g y := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [raw, gap, volume.ae_ne q] with y evenAt empty notEdge
    by_cases outside : q < y
    · have positive : 0 < y := (by norm_num : 0 < q).trans outside
      have minus : 0 < y-x := by linarith [inside.2]
      have plus : 0 < x+y := add_pos_of_nonneg_of_pos inside.1 positive
      have scaling : 1-(x*y⁻¹)^2 = (-x^2+y^2)/y^2 := by
        field_simp [positive.ne']
        ring
      have cancel : y⁻¹*y^2 = y := by field_simp [positive.ne']
      have combine : (y-x)⁻¹+(x+y)⁻¹ = 2*(y⁻¹/(1-(x*y⁻¹)^2)) := by
        rw [scaling, div_div_eq_mul_div, cancel]
        rw [show -x^2+y^2 = (y-x)*(x+y) by ring]
        field_simp [minus.ne', plus.ne']
        ring
      rw [indicator_of_mem (show y ∈ Ioi (0:ℝ) from positive),
        indicator_of_mem (show y ∈ Ioi q from outside)]
      dsimp only [f, g]
      rw [← evenAt, abs_sub_comm x y, abs_of_pos minus, sub_neg_eq_add, abs_of_pos plus,
        ← mul_add, ← Complex.ofReal_add, combine, smul_smul, Complex.real_smul, mul_comm]
    · have below : y < q := lt_of_le_of_ne (le_of_not_gt outside) notEdge
      rw [indicator_of_notMem (show y ∉ Ioi q from outside)]
      by_cases positive : 0 < y
      · rw [indicator_of_mem (show y ∈ Ioi (0:ℝ) from positive)]
        dsimp only [f]
        rw [← evenAt, empty (by rwa [abs_of_pos positive]), zero_mul, zero_mul, add_zero]
      · exact indicator_of_notMem positive _
  have inverse : (∫ y in Ioi q, g y) = reciprocalGapRead w x := by
    rw [integral_inverse_tail]
    unfold reciprocalGapRead
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (s := Ioo (0:ℝ) 4) (burnolTateReciprocalL2_coeFn w),
      ae_restrict_mem measurableSet_Ioo] with t source ht
    rw [source, burnolTateReciprocalRaw, abs_of_pos ht.1]
    dsimp only [g]
    rw [inv_inv, smul_smul]
    have coeff : (t^2)⁻¹ * (t / (1-(x*t)^2)) = (1-(x*t)^2)⁻¹ * t⁻¹ := by
      rw [div_eq_mul_inv]
      field_simp [ht.1.ne']
    rw [coeff, mul_smul]
    congr 1
    rw [Complex.real_smul, Complex.ofReal_inv]
  rw [originalGapGammaRaw, ← whole, tail, integral_smul, inverse, Complex.real_smul]
  norm_num only [Complex.ofReal_ofNat]
  ring

/-- Erasing the original conductor forces the compact reciprocal field's actual read to vanish. -/
theorem zero_conductor_reciprocal (w : BurnolL2) (even : reflectL2 w = w)
    (gap : w ∈ locallyConstantFace q) (silent : GammaPair w 0) :
    (∀ᵐ y : ℝ ∂volume, |y| < q → w y = 0) ∧
      (∀ᵐ x : ℝ ∂volume, x ∈ Ioo (0:ℝ) edge → reciprocalGapRead w x = 0) := by
  have empty := zero_gap_of_zero_conductor w gap silent
  refine ⟨empty, ?_⟩
  filter_upwards [(actual_original_q_gap_Gamma_local_source w 0 silent empty).2,
    Lp.coeFn_zero (α := ℝ) (E := ℂ) (p := 2) (μ := volume)] with x read gone hx
  have actual := read hx
  have zero : (0 : BurnolL2) x = (0 : ℂ) := by simpa only [Pi.zero_apply] using gone
  rw [zero, gap_raw_reciprocal w even empty x ⟨hx.1.le,hx.2.le⟩] at actual
  exact neg_eq_zero.mp actual.symm

end OriginalKFiniteOrderRelease.PositionGapCayley.ConductorFaithfulness
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
