import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Resolved
import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitRegularity.Mass
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Source
open Complex Filter MeasureTheory Set BurnolPhysicalState FourierTransform
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszSource.Translator
open OriginalKElementaryArithmeticAction.PeriodicPower.Sampling OriginalKElementaryArithmeticAction.PeriodicPower.Source OriginalKElementaryArithmeticAction.PeriodicPower.Resolved
open scoped Topology ENNReal InnerProductSpace
open private box_fourier_trig from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Resolved
open private circleRaw circle_mem circleValue circle_coefficient from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Sampling
open private ordinaryFourier ordinaryFourier_continuous ordinaryFourier_coeFn from
  H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitRegularity.Mass
local notation "F" => fourierL2
local notation "q" => (1/4:ℝ)
local instance periodPositive : Fact (0<(1:ℝ)) := ⟨by norm_num⟩
local notation "CircleL2" => Lp ℂ 2 (AddCircle.haarAddCircle (T:=(1:ℝ)))
local notation "cell" => Ioc (-(1/2):ℝ) (-(1/2)+1)

theorem tailBound_nonnegative (c : BurnolCompletedMellinCoordinate) : 0≤tailBound c := by
  have mass : 0≤tailMass c:=integral_nonneg (fun _=>norm_nonneg _)
  unfold tailBound
  positivity

theorem resolved_fourier_memLp (c : BurnolCompletedMellinCoordinate) :
    MemLp (resolvedFourierRaw c) 2 volume :=
  (Lp.memLp (F (resolvedSource c))).ae_eq (actual_resolved_fourier_raw c)

private theorem resolved_fourier_even (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    resolvedFourierRaw c (-x)=resolvedFourierRaw c x := by
  by_cases zero:x=0
  · simp only [zero,neg_zero]
  · rw [resolvedFourierRaw,resolvedFourierRaw,ForcingWhole.raw_even,
      box_fourier_trig x zero,box_fourier_trig (-x) (neg_ne_zero.mpr zero)]
    simp only [Complex.ofReal_neg,mul_neg,Complex.sin_neg,div_neg,neg_div,neg_neg]

theorem actual_resolved_fourier_integrable (c : BurnolCompletedMellinCoordinate) :
    Integrable (resolvedFourierRaw c) := by
  have center : IntegrableOn (resolvedFourierRaw c) (Icc (-1:ℝ) 1) :=
    ((resolved_fourier_memLp c).locallyIntegrable (by norm_num)).integrableOn_isCompact isCompact_Icc
  have right : IntegrableOn (resolvedFourierRaw c) (Ioi (1:ℝ)) := by
    have dominant := (integrableOn_Ioi_rpow_of_lt (by norm_num:(-2:ℝ)< -1) (by norm_num:(0:ℝ)<1)).const_mul (tailBound c)
    apply dominant.mono' (resolved_fourier_memLp c).aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x inside
    have positive : 0<x:=lt_trans zero_lt_one inside
    rw [Real.rpow_neg positive.le,Real.rpow_two,←div_eq_mul_inv]
    simpa only [abs_of_pos positive] using actual_resolved_fourier_bound c x positive.ne'
  have left : IntegrableOn (resolvedFourierRaw c) (Iio (-1:ℝ)) := by
    have reflectedRight : IntegrableOn (resolvedFourierRaw c) (Ioi (-(-1:ℝ))) := by simpa only [neg_neg] using right
    simpa only [resolved_fourier_even] using reflectedRight.comp_neg_Iio
  have whole:=left.union (center.union right)
  have cover : Iio (-1:ℝ) ∪ (Icc (-1:ℝ) 1 ∪ Ioi (1:ℝ))=univ := by
    ext x
    simp only [mem_union,mem_Iio,mem_Icc,mem_Ioi,mem_univ,iff_true]
    rcases lt_or_ge x (-1) with h|h
    · exact Or.inl h
    · rcases le_or_gt x 1 with h'|h'
      · exact Or.inr (Or.inl ⟨h,h'⟩)
      · exact Or.inr (Or.inr h')
  simpa only [cover,integrableOn_univ] using whole

theorem actual_resolved_F_integrable (c : BurnolCompletedMellinCoordinate) :
    Integrable (F (resolvedSource c):ℝ→ℂ) :=
  (actual_resolved_fourier_integrable c).congr (actual_resolved_fourier_raw c).symm

private theorem point_ordinary (value : BurnolL2) (x : ℝ) :
    fourierPoint value x=ordinaryFourier value x := by
  unfold fourierPoint ordinaryFourier VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with t
  rw [Circle.smul_def,Real.fourierChar_apply]
  simp only [smul_eq_mul,innerₗ_apply_apply,Real.inner_apply]
  congr 2
  push_cast
  ring

/-- Absolute integration of the generated Fourier remainder recovers its original continuous source. -/
theorem actual_resolved_inverse_fourier (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    fourierPoint (F (resolvedSource c)) x=resolvedRaw c x := by
  have ordinary:=ordinaryFourier_coeFn (F (resolvedSource c)) (actual_resolved_F_integrable c)
  rw [fourierL2_fourierL2] at ordinary
  have reflected : (reflectL2 (resolvedSource c):ℝ→ℂ)=ᵐ[volume]resolvedRaw c := by
    filter_upwards [Lp.coeFn_compMeasurePreserving (resolvedSource c) negMeasurePreserving,
      negMeasurePreserving.quasiMeasurePreserving.ae (actual_resolved_raw c)] with t reflection raw
    change reflectL2 (resolvedSource c) t=resolvedSource c (-t) at reflection
    change resolvedSource c (-t)=resolvedRaw c (-t) at raw
    rw [reflection,raw]
    simp only [resolvedRaw,abs_neg]
  have same:=Measure.eq_of_ae_eq (ordinary.symm.trans reflected)
    (ordinaryFourier_continuous _ (actual_resolved_F_integrable c)) (actual_resolved_continuous c)
  rw [point_ordinary,congrFun same]

def representative (x : AddCircle (1:ℝ)) : ℝ := (AddCircle.equivIoc 1 (-(1/2):ℝ) x).1

private theorem representative_preserving :
    MeasurePreserving representative AddCircle.haarAddCircle (volume.restrict cell) := by
  have normalized : (volume:Measure (AddCircle (1:ℝ)))=AddCircle.haarAddCircle := by
    simpa only [ENNReal.ofReal_one,one_smul] using (AddCircle.volume_eq_smul_haarAddCircle (T:=(1:ℝ)))
  have source:=(measurePreserving_subtype_coe measurableSet_Ioc).comp (AddCircle.measurePreserving_equivIoc (1:ℝ) (a:=-(1/2)))
  change MeasurePreserving representative (volume:Measure (AddCircle (1:ℝ))) (volume.restrict cell) at source
  simpa only [normalized,Function.comp_def,representative] using source

def circleMap : BurnolL2 →L[ℂ] CircleL2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ representative representative_preserving).toContinuousLinearMap.comp
    (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 cell)

theorem circleMap_raw (value : BurnolL2) :
    (circleMap value:AddCircle (1:ℝ)→ℂ)=ᵐ[AddCircle.haarAddCircle] fun x=>value (representative x) := by
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 cell value) representative_preserving,
    representative_preserving.quasiMeasurePreserving.ae (LpToLpRestrictCLM_coeFn ℂ cell value)]
    with x mapped restricted
  change circleMap value x=LpToLpRestrictCLM ℝ ℂ ℂ volume 2 cell value (representative x) at mapped
  exact mapped.trans restricted

theorem circleMap_original (value : BurnolL2) : circleMap value=circleValue value := by
  apply Lp.ext
  filter_upwards [circleMap_raw value,(circle_mem value).coeFn_toLp] with x mapped old
  exact mapped.trans old.symm

def translated (value : BurnolL2) (k : ℤ) : BurnolL2 :=
  Lp.compMeasurePreserving (fun x:ℝ=>x+(k:ℝ)) (measurePreserving_add_right volume (k:ℝ)) value

theorem translated_raw (c : BurnolCompletedMellinCoordinate) (k : ℤ) :
    (circleMap (translated (F (resolvedSource c)) k):AddCircle (1:ℝ)→ℂ)=ᵐ[AddCircle.haarAddCircle]
      fun x=>resolvedFourierRaw c (representative x+k) := by
  have read : (translated (F (resolvedSource c)) k:ℝ→ℂ)=ᵐ[volume]
      fun x=>resolvedFourierRaw c (x+k) := by
    filter_upwards [Lp.coeFn_compMeasurePreserving (F (resolvedSource c)) (measurePreserving_add_right volume (k:ℝ)),
      (measurePreserving_add_right volume (k:ℝ)).quasiMeasurePreserving.ae (actual_resolved_fourier_raw c)]
      with x shifted source
    exact shifted.trans source
  filter_upwards [circleMap_raw (translated (F (resolvedSource c)) k),
    representative_preserving.quasiMeasurePreserving.ae (ae_restrict_of_ae read)] with x mapped actual
  exact mapped.trans actual

def aliasPiece (c : BurnolCompletedMellinCoordinate) (k : ℤ) : CircleL2 :=
  if k=0 then 0 else circleMap (translated (F (resolvedSource c)) k)

private theorem shifted_distance (x : AddCircle (1:ℝ)) (k : ℤ) (nonzero:k≠0) :
    (1/2:ℝ)*|(k:ℝ)|≤|representative x+k| := by
  have representative_mem:representative x∈cell := (AddCircle.equivIoc 1 (-(1/2):ℝ) x).2
  have bound : |representative x|≤(1/2:ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [representative_mem.1,representative_mem.2]
  have one : (1:ℝ)≤|(k:ℝ)| := by
    exact_mod_cast (Int.one_le_abs nonzero)
  have triangle:=abs_add_le (representative x+k) (-representative x)
  rw [abs_neg,show representative x+(k:ℝ)+ -representative x=(k:ℝ) by ring] at triangle
  linarith

theorem aliasPiece_norm_bound (c : BurnolCompletedMellinCoordinate) (k : ℤ) :
    ‖aliasPiece c k‖≤4*tailBound c/(k:ℝ)^2 := by
  by_cases zero:k=0
  · subst k
    simp [aliasPiece]
  · rw [aliasPiece,if_neg zero]
    have boundNonnegative : 0≤4*tailBound c/(k:ℝ)^2 := by positivity [tailBound_nonnegative c]
    have pointwise : ∀ᵐx∂AddCircle.haarAddCircle,
        ‖circleMap (translated (F (resolvedSource c)) k) x‖≤4*tailBound c/(k:ℝ)^2 := by
      filter_upwards [translated_raw c k] with x read
      rw [read]
      have distance:=shifted_distance x k zero
      have kpos : 0 < |(k:ℝ)| := abs_pos.mpr (by exact_mod_cast zero)
      have xpos : 0 < |representative x+k| := lt_of_lt_of_le (by positivity) distance
      apply (actual_resolved_fourier_bound c _ (abs_pos.mp xpos)).trans
      have squared : (k:ℝ)^2≤4*|representative x+k|^2 := by nlinarith [sq_abs (k:ℝ)]
      have denominator : (0:ℝ)<(k:ℝ)^2 := sq_pos_of_ne_zero (by exact_mod_cast zero)
      apply (div_le_div_iff₀ (sq_pos_of_pos xpos) denominator).mpr
      nlinarith [mul_le_mul_of_nonneg_left squared (tailBound_nonnegative c)]
    simpa [measureUnivNNReal]
      using Lp.norm_le_of_ae_bound boundNonnegative pointwise

theorem aliasPiece_summable_norm (c : BurnolCompletedMellinCoordinate) :
    Summable (fun k:ℤ=>‖aliasPiece c k‖) := by
  have major:Summable (fun k:ℤ=>4*tailBound c/(k:ℝ)^2) := by
    simpa only [mul_one,div_eq_mul_inv,one_mul] using
      (Real.summable_one_div_int_pow.mpr (by decide:1<2)).mul_left (4*tailBound c)
  exact major.of_nonneg_of_le (fun _=>norm_nonneg _) (aliasPiece_norm_bound c)

def aliasValue (c : BurnolCompletedMellinCoordinate) : CircleL2 := ∑' k:ℤ,aliasPiece c k
def periodizedValue (c : BurnolCompletedMellinCoordinate) : CircleL2 :=
  circleMap (F (resolvedSource c))+aliasValue c

end OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
