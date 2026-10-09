import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import H0mework.Versions.V2.Arithmetic.SonineSource.ModifiedWeakFEQuarterCarrier
import H0mework.Versions.V2.Arithmetic.RiemannSpectral.SourceRechart

/-!
# Quarter-Mellin source rechart into additive Burnol L2

The quarter chart and its Mellin coordinate determine an even additive
position function by the literal change of variables `u = t⁻²`.  Its L2
admission is generated from the existing quarter-L2 membership and the
exponential Jacobian.  No compact-support or Burnol-gap hypothesis is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace BurnolPhysicalState

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Positive additive-position source obtained from the literal reciprocal
square change of variables. -/
def quarterMellinAdditivePositiveRechartRaw {z : ℂ}
    (value : QuarterMellinL2Test z) (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) •
    ((t : ℂ) ^ (-(1 : ℂ)) •
      positiveMellinExtension value.1 (t ^ (-2 : ℝ)))

/-- Even full-line source used by the physical Burnol carrier. -/
def quarterMellinAdditiveEvenRechartRaw {z : ℂ}
    (value : QuarterMellinL2Test z) (t : ℝ) : ℂ :=
  quarterMellinAdditivePositiveRechartRaw value |t|

@[simp] theorem quarterMellinAdditiveEvenRechartRaw_neg {z : ℂ}
    (value : QuarterMellinL2Test z) (t : ℝ) :
    quarterMellinAdditiveEvenRechartRaw value (-t) =
      quarterMellinAdditiveEvenRechartRaw value t := by
  simp [quarterMellinAdditiveEvenRechartRaw]

/-- The additive logarithmic half-density of the same source. -/
def quarterMellinAdditiveHalfDensity {z : ℂ}
    (value : QuarterMellinL2Test z) (x : ℝ) : ℂ :=
  burnolQuarterFeatureAdditiveRechart value.1 x

private theorem quarterMellinAdditiveHalfDensity_memLp {z : ℂ}
    (value : QuarterMellinL2Test z) :
    MemLp (quarterMellinAdditiveHalfDensity value) 2 volume := by
  let energy := positiveMellinLogQuarterTransform value.1
  have energyMem : MemLp energy 2 volume := value.2.1
  have qmp : Measure.QuasiMeasurePreserving
      (fun x : ℝ => (-2 : ℝ) * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := (-2 : ℝ)) (by norm_num))
  have measurable : AEStronglyMeasurable
      (quarterMellinAdditiveHalfDensity value) volume := by
    have composed := energyMem.1.comp_quasiMeasurePreserving qmp
    exact (composed.const_smul (1 / 2 : ℂ)).congr
      (ae_of_all volume fun x => by
        simp [quarterMellinAdditiveHalfDensity,
          burnolQuarterFeatureAdditiveRechart, energy])
  rw [memLp_two_iff_integrable_sq_norm measurable]
  have energyIntegrable : Integrable (fun x : ℝ => ‖energy x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm energyMem.1).mp energyMem
  have composedIntegrable :
      Integrable (fun x : ℝ => ‖energy ((-2 : ℝ) * x)‖ ^ 2) :=
    energyIntegrable.comp_mul_left' (by norm_num)
  have scaledIntegrable : Integrable
      (fun x : ℝ => (1 / 4 : ℝ) * ‖energy ((-2 : ℝ) * x)‖ ^ 2) :=
    composedIntegrable.const_mul (1 / 4 : ℝ)
  exact scaledIntegrable.congr (ae_of_all volume fun x => by
    simp [quarterMellinAdditiveHalfDensity,
      burnolQuarterFeatureAdditiveRechart, energy]
    ring)

private theorem aestronglyMeasurable_positive_of_mellinConvergent
    {f : ℝ → ℂ} {s : ℂ} (convergent : MellinConvergent f s) :
    AEStronglyMeasurable f (volume.restrict (Ioi 0)) := by
  have weighted : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * f t)
      (volume.restrict (Ioi 0)) := by
    exact convergent.aestronglyMeasurable
  have inverseWeight : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (1 - s))
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact continuousOn_of_forall_continuousAt fun t positive =>
      (Complex.continuousAt_ofReal_cpow_const t (1 - s)
        (Or.inr positive.ne'))
  apply (inverseWeight.mul weighted).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positive
  change (t : ℂ) ^ (1 - s) * ((t : ℂ) ^ (s - 1) * f t) = f t
  rw [← mul_assoc, ← Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr positive.ne')]
  have exponent : (1 - s) + (s - 1) = 0 := by ring
  rw [exponent, Complex.cpow_zero, one_mul]

private theorem quarterMellinAdditivePositiveRechartRaw_convergent {z : ℂ}
    (value : QuarterMellinL2Test z) :
    MellinConvergent (quarterMellinAdditivePositiveRechartRaw value)
      (1 - 2 * z) := by
  have composed : MellinConvergent
      (fun t : ℝ => positiveMellinExtension value.1 (t ^ (-2 : ℝ)))
      (-2 * z) := by
    apply (MellinConvergent.comp_rpow (s := -2 * z)
      (a := (-2 : ℝ)) (by norm_num)).2
    rw [show (-2 * z) / ((-2 : ℝ) : ℂ) = z by
      norm_num]
    exact value.2.2
  have weighted : MellinConvergent
      (fun t : ℝ => (t : ℂ) ^ (-(1 : ℂ)) •
        positiveMellinExtension value.1 (t ^ (-2 : ℝ)))
      (1 - 2 * z) := by
    apply MellinConvergent.cpow_smul.mpr
    convert composed using 1
    all_goals ring
  exact weighted.const_smul (1 / 2 : ℂ)

private theorem quarterMellinAdditiveEvenRechartRaw_aestronglyMeasurable_positive
    {z : ℂ} (value : QuarterMellinL2Test z) :
    AEStronglyMeasurable (quarterMellinAdditiveEvenRechartRaw value)
      (volume.restrict (Ioi 0)) := by
  have source := aestronglyMeasurable_positive_of_mellinConvergent
    (quarterMellinAdditivePositiveRechartRaw_convergent value)
  exact source.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positive
    rw [quarterMellinAdditiveEvenRechartRaw, abs_of_pos positive])

private theorem quarterMellinAdditiveEvenRechartRaw_aestronglyMeasurable
    {z : ℂ} (value : QuarterMellinL2Test z) :
    AEStronglyMeasurable (quarterMellinAdditiveEvenRechartRaw value) volume := by
  have positive :=
    quarterMellinAdditiveEvenRechartRaw_aestronglyMeasurable_positive value
  have positiveClosed : AEStronglyMeasurable
      (quarterMellinAdditiveEvenRechartRaw value)
      (volume.restrict (Ici 0)) := by
    rwa [← Measure.restrict_congr_set Ioi_ae_eq_Ici]
  have negPreserving : MeasurePreserving (fun t : ℝ => -t)
      (volume.restrict (Iic 0)) (volume.restrict (Ici 0)) := by
    convert negMeasurePreserving.restrict_preimage measurableSet_Ici using 1
    ext t
    simp
  have negativeComposed := positiveClosed.comp_measurePreserving negPreserving
  have negative : AEStronglyMeasurable
      (quarterMellinAdditiveEvenRechartRaw value)
      (volume.restrict (Iic 0)) :=
    negativeComposed.congr (ae_of_all _ fun t => by
      simp)
  have combined :=
    aestronglyMeasurable_union_iff.mpr ⟨negative, positive⟩
  simpa only [Iic_union_Ioi, Measure.restrict_univ] using combined

private theorem quarterMellinAdditiveHalfDensity_sqNorm {z : ℂ}
    (value : QuarterMellinL2Test z) (x : ℝ) :
    ‖quarterMellinAdditiveHalfDensity value x‖ ^ 2 =
      Real.exp x *
        ‖quarterMellinAdditiveEvenRechartRaw value (Real.exp x)‖ ^ 2 := by
  have featureRead :
      positiveMellinLogQuarterTransform value.1 (-2 * x) =
        (Real.exp ((-2 * x) / 4) : ℂ) *
          positiveMellinExtension value.1 (Real.exp (-2 * x)) := by
    change (Real.exp ((-2 * x) / 4) : ℂ) *
        value.1 ⟨Real.exp (-2 * x), Real.exp_pos _⟩ =
      (Real.exp ((-2 * x) / 4) : ℂ) *
        (if positive : 0 < Real.exp (-2 * x) then
          value.1 ⟨Real.exp (-2 * x), positive⟩ else 0)
    rw [dif_pos (Real.exp_pos _)]
  simp only [quarterMellinAdditiveHalfDensity,
    burnolQuarterFeatureAdditiveRechart]
  rw [featureRead]
  simp only [
    quarterMellinAdditiveEvenRechartRaw, abs_of_pos (Real.exp_pos x),
    quarterMellinAdditivePositiveRechartRaw, smul_eq_mul]
  rw [show Real.exp x ^ (-2 : ℝ) = Real.exp (-2 * x) by
    rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
    congr 1
    ring]
  simp only [positiveMellinExtension]
  rw [show (Real.exp x : ℂ) ^ (-(1 : ℂ)) =
      (Real.exp (-x) : ℂ) by
    simp only [Complex.cpow_neg, Complex.cpow_one]
    simpa using (Complex.exp_neg (x : ℂ)).symm]
  simp only [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  ring_nf
  have leftExp : Real.exp (x * (-1 / 2 : ℝ)) ^ 2 = Real.exp (-x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have rightExp : Real.exp x * Real.exp (-x) ^ 2 = Real.exp (-x) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [leftExp]
  conv_lhs => rw [← rightExp]
  ring

private theorem integrableOn_exp_weight_iff (g : ℝ → ℝ) :
    IntegrableOn g (Ioi 0) ↔
      Integrable (fun x : ℝ => Real.exp x * g (Real.exp x)) := by
  have change :=
    MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (fun _ _ _ _ equality => Real.exp_injective equality) g
  simpa only [image_univ, Real.range_exp,
    abs_of_pos (Real.exp_pos _), smul_eq_mul,
    integrableOn_univ] using change

theorem quarterMellinAdditiveEvenRechartRaw_memLp {z : ℂ}
    (value : QuarterMellinL2Test z) :
    MemLp (quarterMellinAdditiveEvenRechartRaw value) 2 volume := by
  have measurable :=
    quarterMellinAdditiveEvenRechartRaw_aestronglyMeasurable value
  rw [memLp_two_iff_integrable_sq_norm measurable]
  have chartIntegrable : Integrable (fun x : ℝ =>
      ‖quarterMellinAdditiveHalfDensity value x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm
      (quarterMellinAdditiveHalfDensity_memLp value).1).mp
        (quarterMellinAdditiveHalfDensity_memLp value)
  have positiveIntegrable : IntegrableOn (fun t : ℝ =>
      ‖quarterMellinAdditiveEvenRechartRaw value t‖ ^ 2) (Ioi 0) :=
    (integrableOn_exp_weight_iff _).mpr
      (chartIntegrable.congr (ae_of_all volume fun x =>
        quarterMellinAdditiveHalfDensity_sqNorm value x))
  have negativeIntegrable : IntegrableOn (fun t : ℝ =>
      ‖quarterMellinAdditiveEvenRechartRaw value t‖ ^ 2) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let embedding : MeasurableEmbedding (fun t : ℝ => -t) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [embedding.integrableOn_map_iff]
    simp_rw [Function.comp_def, neg_preimage, neg_Iic, neg_zero,
      quarterMellinAdditiveEvenRechartRaw_neg value]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr positiveIntegrable
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact negativeIntegrable.union positiveIntegrable

/-- Source-exact even additive-position `L²` value. -/
def quarterMellinAdditiveEvenRechart {z : ℂ}
    (value : QuarterMellinL2Test z) : BurnolL2 :=
  (quarterMellinAdditiveEvenRechartRaw_memLp value).toLp
    (quarterMellinAdditiveEvenRechartRaw value)

theorem quarterMellinAdditiveEvenRechart_coeFn {z : ℂ}
    (value : QuarterMellinL2Test z) :
    (quarterMellinAdditiveEvenRechart value : ℝ → ℂ) =ᵐ[volume]
      quarterMellinAdditiveEvenRechartRaw value :=
  MemLp.coeFn_toLp (quarterMellinAdditiveEvenRechartRaw_memLp value)

theorem reflectL2_quarterMellinAdditiveEvenRechart {z : ℂ}
    (value : QuarterMellinL2Test z) :
    reflectL2 (quarterMellinAdditiveEvenRechart value) =
      quarterMellinAdditiveEvenRechart value := by
  apply Lp.ext
  have atNeg := negMeasurePreserving.quasiMeasurePreserving.ae
    (quarterMellinAdditiveEvenRechart_coeFn value)
  filter_upwards [
    Lp.coeFn_compMeasurePreserving
      (quarterMellinAdditiveEvenRechart value) negMeasurePreserving,
    atNeg,
    quarterMellinAdditiveEvenRechart_coeFn value]
    with x reflection sourceNeg source
  calc
    reflectL2 (quarterMellinAdditiveEvenRechart value) x =
        quarterMellinAdditiveEvenRechart value (-x) := reflection
    _ = quarterMellinAdditiveEvenRechartRaw value (-x) := sourceNeg
    _ = quarterMellinAdditiveEvenRechartRaw value x :=
      quarterMellinAdditiveEvenRechartRaw_neg value x
    _ = quarterMellinAdditiveEvenRechart value x := source.symm

end
end BurnolPhysicalState
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
