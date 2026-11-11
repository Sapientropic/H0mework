import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Derivative

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Even
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszSource.Translator
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open scoped Topology InnerProductSpace
open private sourceOneMinusSquare_reflect from
  H0mework.Versions.R7e4da746.Arithmetic.RieszForcing.SourceParity
local notation "q"=>(1/4:ℝ)
local notation "μq"=>volume.restrict (symmetricInterval q)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "S"=>burnolMeanZeroTruncatedFourier
local notation "L"=>burnolMeanZeroOneMinusSquare
local notation "BI"=>burnolMeanZeroBlockInverse

private theorem fourier_even (raw:ℝ→ℂ) (even:∀x:ℝ,raw (-x)=raw x) (x:ℝ):
    Constructor.fourierRaw raw (-x)=Constructor.fourierRaw raw x:=by
  rw [Constructor.fourierRaw_integral,Constructor.fourierRaw_integral]
  have moved:=intervalIntegral.integral_comp_neg
    (f:=fun y:ℝ=>Constructor.phase x y*raw y) (a:=-q) (b:=q)
  calc
    _=∫y:ℝ in (-q)..q,Constructor.phase x (-y)*raw (-y):=by
      apply intervalIntegral.integral_congr
      intro y _
      dsimp only
      rw [even y]
      simp only [Constructor.phase,neg_mul,mul_neg,neg_neg]
    _=_:=by simpa only [neg_neg] using moved

theorem actual_first_reflection (w:ℂ) (below:w.re<1):
    sourceMeanZeroReflection (firstSource w below)=firstSource w below:=by
  apply Subtype.ext
  change reflectRestricted q (firstSource w below:Hq)=(firstSource w below:Hq)
  apply Lp.ext
  have raw:=actual_smooth_raw (seedRaw w) (actual_seed_integrable w below)
  filter_upwards [raw,(negMeasurePreserving_restrict q).quasiMeasurePreserving.ae raw,
    Lp.coeFn_compMeasurePreserving (firstSource w below:Hq) (negMeasurePreserving_restrict q)]
    with x positive negative reflected
  change (firstSource w below:Hq) x=centeredFourierRaw (seedRaw w) x at positive
  change (firstSource w below:Hq) (-x)=centeredFourierRaw (seedRaw w) (-x) at negative
  change reflectRestricted q (firstSource w below:Hq) x=(firstSource w below:Hq) (-x) at reflected
  rw [reflected,negative,positive,centeredFourierRaw,centeredFourierRaw,
    fourier_even _ (actual_seed_even w) x]

theorem actual_correction_reflection (w:ℂ) (below:w.re<1):
    sourceMeanZeroReflection (correction w below)=correction w below:=by
  have equation:L (correction w below)=S (firstSource w below):=
    actual_correction_equation w below
  have reflected:L (sourceMeanZeroReflection (correction w below))=S (firstSource w below):=by
    rw [sourceOneMinusSquare_reflect,equation,←sourceMeanZeroFourier_reflect,actual_first_reflection]
  have recovered:=congrArg BI reflected
  change (BI*L) (sourceMeanZeroReflection (correction w below))=correction w below at recovered
  have inverse:BI*L=1:=Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  rwa [inverse,one_apply_eq_self] at recovered

theorem actual_correction_raw_even (w:ℂ) (below:w.re<1) (x:ℝ) (inside:x∈Icc (-q) q):
    correctionRaw w below (-x)=correctionRaw w below x:=by
  have source:(fun y:ℝ=>correctionRaw w below (-y))=ᵐ[μq]correctionRaw w below:=by
    filter_upwards [actual_correction_raw w below,
      (negMeasurePreserving_restrict q).quasiMeasurePreserving.ae (actual_correction_raw w below),
      Lp.coeFn_compMeasurePreserving (correction w below:Hq) (negMeasurePreserving_restrict q)]
      with y positive negative reflected
    change reflectRestricted q (correction w below:Hq) y=(correction w below:Hq) (-y) at reflected
    have fixed:reflectRestricted q (correction w below:Hq)=(correction w below:Hq):=
      congrArg (fun a:M=>(a:Hq)) (actual_correction_reflection w below)
    rw [fixed] at reflected
    exact negative.symm.trans (reflected.symm.trans positive)
  exact MeasureTheory.Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (-q:ℝ)≠q) source
    ((actual_correction_continuous w below).comp continuous_neg).continuousOn
    (actual_correction_continuous w below).continuousOn inside

theorem actual_dual_even (w:ℂ) (below:w.re<1) (x:ℝ) (inside:x∈Icc (-q) q):
    dualRaw w below (-x)=dualRaw w below x:=by
  rw [dualRaw,dualRaw,actual_seed_even,actual_correction_raw_even w below x inside]

/-- The full source mean is split only after its actual reflection has been generated. -/
theorem actual_positive_dual_mean (w:ℂ) (below:w.re<1):
    (∫x:ℝ in (0:ℝ)..q,dualRaw w below x)=0:=by
  have domain:IntegrableOn (dualRaw w below) (symmetricInterval q) volume:=actual_dual_integrable w below
  have negative:IntervalIntegrable (dualRaw w below) volume (-q) 0:=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-q:ℝ)≤0)).mpr
      (domain.mono_set (fun x inside=>⟨inside.1,le_trans inside.2 (by norm_num)⟩))
  have positive:IntervalIntegrable (dualRaw w below) volume 0 q:=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ)≤q)).mpr
      (domain.mono_set (fun x inside=>⟨le_trans (by norm_num) inside.1,inside.2⟩))
  have whole:(∫x:ℝ in (-q)..q,dualRaw w below x)=0:=by
    rw [intervalIntegral.integral_of_le (by norm_num : (-q:ℝ)≤q),←integral_Icc_eq_integral_Ioc]
    exact actual_dual_mean w below
  have halves:(∫x:ℝ in (-q)..(0:ℝ),dualRaw w below x)=∫x:ℝ in (0:ℝ)..q,dualRaw w below x:=by
    have moved:=intervalIntegral.integral_comp_neg (f:=dualRaw w below) (a:=(0:ℝ)) (b:=q)
    rw [neg_zero] at moved
    rw [←moved]
    apply intervalIntegral.integral_congr
    intro x inside
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤q)] at inside
    exact actual_dual_even w below x ⟨by linarith [inside.1],inside.2⟩
  rw [←intervalIntegral.integral_add_adjacent_intervals negative positive,halves] at whole
  linear_combination (1/2:ℂ)*whole

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Even
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
