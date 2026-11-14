import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.PrimeField
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.FixedCollar

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszSourceGreen OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.Current
open scoped Topology InnerProductSpace
open private actual_dual_pair_price homogeneous_dilation_domain from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.UnitDual
open private correction_smooth_dual from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB
open private dual_product_domain from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.FixedCollar
open private even_half_integral from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TailLog
open private outgoing_even from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.ActedSchur
local notation "q" => (1/4 : ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "D" => burnolMultiplicativeDilation
local notation "R" => burnolDirectRightResolventCLM
local notation "order" => generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "bare" => generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner

private theorem native_inverse_source (c : BurnolCompletedMellinCoordinate) :
    fourierL2.symm (nativeSource c) =
      E (correction c.value c.belowOne : Hq) - gapState c := by
  rw [actual_native_source]
  change fourierL2.symm (-(fourierL2 (elementarySource c)) +
    fourierL2 (E (correction c.value c.belowOne : Hq))) = _
  rw [map_add, map_neg, fourierL2.symm_apply_apply, fourierL2.symm_apply_apply]
  change -gapState c + E (correction c.value c.belowOne : Hq) = _
  module

/-- The two singular summands are read only as one genuine whole L2 source. -/
theorem actual_native_inverse_source_raw (c : BurnolCompletedMellinCoordinate) :
    (fourierL2.symm (nativeSource c) : ℝ → ℂ) =ᵐ[volume]
      fun x => (symmetricInterval q).indicator (dualRaw c.value c.belowOne) x - halfPower c x := by
  rw [native_inverse_source]
  have corr := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (actual_correction_raw c.value c.belowOne)
  filter_upwards [Lp.coeFn_sub (E (correction c.value c.belowOne : Hq)) (gapState c),
    burnolQuarterZeroExtension_coe (correction c.value c.belowOne : Hq),
    gapState_read c, corr] with x subtracted extended gap raw
  rw [subtracted, Pi.sub_apply, extended, gap]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem inside, raw inside]
    have source := actual_gap_seed_raw c x
    rw [seedCut, indicator_of_mem inside] at source
    unfold dualRaw
    linear_combination -source
  · rw [indicator_of_notMem inside, indicator_of_notMem inside]
    have source := actual_gap_seed_raw c x
    rw [seedCut, indicator_of_notMem inside] at source
    linear_combination -source

private theorem star_power (c : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0 < x) :
    star ((x : ℂ)^(-c.value)) = (x : ℂ)^(-star c.value) := by
  have argument : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg positive.le]
    exact Real.pi_ne_zero.symm
  have source := Complex.cpow_conj (x : ℂ) (-c.value) argument
  rw [Complex.conj_ofReal] at source
  simpa only [← Complex.star_def, star_neg] using source.symm

private theorem homogeneous_mellin (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (even : reflectL2 v = v) (value : ℂ)
    (source : HasMellin (v : ℝ → ℂ) (1-c.value) value) :
    Integrable (fun x : ℝ => star (v x) * halfPower c x) ∧
      homogeneousPrice c v = star value := by
  let f := fun x : ℝ => star (v x) * halfPower c x
  have positiveRead : f =ᵐ[volume.restrict (Ioi 0)]
      fun x => (1/2 : ℂ) * star ((x : ℂ)^(-c.value) * v x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x positive
    dsimp only [f]
    rw [halfPower, powerRaw, abs_of_pos positive, star_mul, star_power c x positive]
    ring
  have original : IntegrableOn (fun x : ℝ => (x : ℂ)^(-c.value) * v x) (Ioi 0) := by
    simpa only [MellinConvergent, show (1-c.value)-1 = -c.value by ring, smul_eq_mul] using source.1
  have conjugated : IntegrableOn (fun x : ℝ => star ((x : ℂ)^(-c.value) * v x)) (Ioi 0) := by
    apply original.norm.mono' (continuous_star.comp_aestronglyMeasurable original.1)
    exact ae_of_all _ fun x => by simp
  have positiveDomain : IntegrableOn f (Ioi 0) :=
    (conjugated.const_mul (1/2 : ℂ)).congr positiveRead.symm
  have negativeRead := Lp.coeFn_compMeasurePreserving v negMeasurePreserving
  change (reflectL2 v : ℝ → ℂ) =ᵐ[volume] (fun x : ℝ => v (-x)) at negativeRead
  rw [even] at negativeRead
  have parity : ∀ᵐ x : ℝ ∂volume, f (-x) = f x := by
    filter_upwards [negativeRead] with x read
    simp only [f, halfPower, powerRaw, abs_neg]
    rw [← read]
  have negativeDomain : IntegrableOn f (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let embedding : MeasurableEmbedding (fun t : ℝ => -t) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [embedding.integrableOn_map_iff]
    simp only [Function.comp_def, neg_preimage, neg_Iic, neg_zero]
    exact ((integrableOn_Ici_iff_integrableOn_Ioi).mpr positiveDomain).congr
      (ae_restrict_of_ae (show f =ᵐ[volume] (fun x : ℝ => f (-x)) from
        parity.mono (fun _ read => read.symm)))
  have domain : Integrable f := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact negativeDomain.union positiveDomain
  refine ⟨domain, ?_⟩
  change (∫ x : ℝ, f x) = _
  rw [even_half_integral f domain parity, integral_congr_ae positiveRead, integral_const_mul]
  have conjugateIntegral : (∫ x : ℝ in Ioi 0, star ((x : ℂ)^(-c.value) * v x)) =
      star (∫ x : ℝ in Ioi 0, (x : ℂ)^(-c.value) * v x) := by
    simpa only [starRingEnd_apply] using (integral_conj (𝕜 := ℂ)
      (μ := volume.restrict (Ioi (0 : ℝ))) (f := fun x : ℝ => (x : ℂ)^(-c.value) * v x))
  rw [conjugateIntegral]
  have read : (∫ x : ℝ in Ioi 0, (x : ℂ)^(-c.value) * v x) = value := by
    simpa only [mellin, show (1-c.value)-1 = -c.value by ring, smul_eq_mul] using source.2
  rw [read]
  ring

/-- Both L1 prices are generated for the actual dilated acted source, without assigning L2 to dualRaw. -/
theorem actual_native_mixed_domains (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) :
    Integrable (fun x : ℝ => star (D h (nativeOutgoingCotest c (order c.value)) x) * halfPower c x) ∧
    Integrable (fun x : ℝ => star (D h (nativeOutgoingCotest c (order c.value)) x) *
      dualRaw c.value c.belowOne x) μq := by
  have paid := (homogeneous_mellin c _ (outgoing_even c zero _) _
    (actual_native_top_hasMellin c zero)).1
  have shifted := homogeneous_dilation_domain c h _ paid
  exact ⟨shifted, dual_product_domain c _ shifted⟩

/-- The full power leg consumes the true original top including its phase. -/
theorem actual_native_mixed_homogeneous_price (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) :
    homogeneousPrice c (D h (nativeOutgoingCotest c (order c.value))) =
      fullMellinTranslationCharacter (star c.value) (-h) *
        star ((2 : ℂ)^(order c.value) * bare c.value c.value *
          burnolAmbientCompletedMellinEvaluator c (physicalCotest c : BurnolL2)) := by
  rw [actual_homogeneous_price_dilation]
  rw [(homogeneous_mellin c _ (outgoing_even c zero _) _ (actual_native_top_hasMellin c zero)).2]

private theorem inverse_first (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) :
    fourierL2.symm (D (-h) (((R c)^(order c.value)) (nativeCotest c))) =
      D h (nativeOutgoingCotest c (order c.value)) := by
  have source := congrArg fourierL2.symm (fourierL2_burnolMultiplicativeDilation h
    (nativeOutgoingCotest c (order c.value)))
  rw [fourierL2.symm_apply_apply] at source
  have field : fourierL2 (nativeOutgoingCotest c (order c.value)) =
      ((R c)^(order c.value)) (nativeCotest c) := by
    rw [← actual_native_acted_field c zero (order c.value), fourierL2.apply_symm_apply]
  rw [field] at source
  exact source.symm

/-- Actual native mixed price: the remaining source-map difference is the complete quarter dual contact, with Unit still separate. -/
theorem actual_native_prime_mixed_contact (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) :
    inner ℂ (D (-h) (((R c)^(order c.value)) (nativeCotest c))) (nativeSource c) =
      (∫ x : ℝ, star (D h (nativeOutgoingCotest c (order c.value)) x) *
        dualRaw c.value c.belowOne x ∂μq) -
      fullMellinTranslationCharacter (star c.value) (-h) *
        star ((2 : ℂ)^(order c.value) * bare c.value c.value *
          burnolAmbientCompletedMellinEvaluator c (physicalCotest c : BurnolL2)) := by
  let v := D h (nativeOutgoingCotest c (order c.value))
  have pair := actual_dual_pair_price c v (actual_native_mixed_domains c zero h).1
  rw [correction_smooth_dual] at pair
  have moved := (fourierL2.symm.inner_map_map
    (D (-h) (((R c)^(order c.value)) (nativeCotest c))) (nativeSource c)).symm
  rw [inverse_first c zero h, native_inverse_source, inner_sub_right] at moved
  have extended := ContinuousLinearMap.adjoint_inner_right Rq v
    (correction c.value c.belowOne : Hq)
  change inner ℂ v (E (correction c.value c.belowOne : Hq)) =
    inner ℂ (Rq v) (correction c.value c.belowOne : Hq) at extended
  rw [extended] at moved
  have homogeneous := actual_native_mixed_homogeneous_price c zero h
  change homogeneousPrice c v = _ at homogeneous
  change inner ℂ (D (-h) (((R c)^(order c.value)) (nativeCotest c))) (nativeSource c) =
    (∫ x : ℝ, star (v x) * dualRaw c.value c.belowOne x ∂μq) - _
  rw [moved, pair, ← homogeneous]
  dsimp only [v]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
