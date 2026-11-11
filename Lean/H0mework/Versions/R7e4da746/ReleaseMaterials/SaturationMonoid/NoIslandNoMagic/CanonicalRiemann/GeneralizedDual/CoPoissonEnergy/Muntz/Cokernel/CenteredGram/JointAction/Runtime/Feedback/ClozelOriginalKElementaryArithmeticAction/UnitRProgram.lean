import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseSourceRTail
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalFullLossRAction
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction OriginalKSourceResolventReconstruction
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKExteriorCoPoissonAction
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "R" => burnolDirectRightResolventCLM
local notation "T" => burnolTateReciprocalL2

private def gamma (c:BurnolCompletedMellinCoordinate) : ℂ :=
  star c.value*GapEuler.gapMean q c

private theorem conjugate_zero (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    riemannZeta (barC c).value=0 := by
  simpa only [OriginalPrimitiveRankBalance.conjugateCoordinate,Complex.star_def,zero,map_zero] using
    riemannZeta_conj c.value

private def unitPrice (c:BurnolCompletedMellinCoordinate) : ℂ := (1-c.value)*gamma (barC c)
private def weightedUnitCurrent (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) : BurnolL2 :=
  (2*gamma (barC c)) • ConstantDual.value-
    (2:ℂ) • elementaryReverseSource (barC c) (conjugate_zero c zero)

private theorem unitEquation (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    unitPrice c • R c ConstantDual.value=weightedUnitCurrent c zero := by
  have actual:=elementary_reverse_unit_resolvent (barC c) (conjugate_zero c zero)
  change elementaryReverseSource (barC c) (conjugate_zero c zero)=gamma (barC c) •
    (ConstantDual.value-((1-star (star c.value))/2) •
      burnolDirectRightResolvent (star (star c.value)/2) ConstantDual.value) at actual
  rw [star_star] at actual
  change elementaryReverseSource (barC c) (conjugate_zero c zero)=gamma (barC c) •
    (ConstantDual.value-((1-c.value)/2) • R c ConstantDual.value) at actual
  rw [weightedUnitCurrent,actual]
  unfold unitPrice
  module

open private gamma_ne_zero
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseSourceRTail

private theorem unitPrice_ne_zero (c:BurnolCompletedMellinCoordinate) : unitPrice c≠0 := by
  have nonzero:1-c.value≠0 := by
    intro same
    have value:c.value=1 := by linear_combination -same
    have bound:=c.belowOne
    rw [value] at bound
    norm_num at bound
  have generated:=gamma_ne_zero (barC c)
  change gamma (barC c)≠0 at generated
  exact mul_ne_zero nonzero generated

private def unitCurrent (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) : BurnolL2 :=
  (unitPrice c)⁻¹ • weightedUnitCurrent c zero

theorem actual_unit_R (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    R c ConstantDual.value=unitCurrent c zero := by
  unfold unitCurrent
  rw [←unitEquation c zero,smul_smul,inv_mul_cancel₀ (unitPrice_ne_zero c),one_smul]

private def FT : BurnolL2→L[ℂ]BurnolL2 :=
  fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.comp T

private theorem FT_dilation (t:ℝ) (v:BurnolL2) :
    FT (burnolMultiplicativeDilation t v)=burnolMultiplicativeDilation t (FT v) := by
  change fourierL2 (T (burnolMultiplicativeDilation t v))=_
  have moved:=burnolTateReciprocalL2_dilation_inverse (-t) v
  simp only [neg_neg] at moved
  rw [←moved,fourierL2_burnolMultiplicativeDilation,neg_neg]
  rfl

private theorem FT_R (c:BurnolCompletedMellinCoordinate) (v:BurnolL2) :
    FT (R c v)=R c (FT v) := by
  have right:1/4<(c.value/2).re := by rw [Complex.div_re];norm_num;linarith [c.rightHalf]
  change FT (burnolDirectRightResolvent (c.value/2) v)=_
  unfold burnolDirectRightResolvent
  rw [map_neg,←FT.integral_comp_comm (burnolDirectRightResolventIntegrand_integrableOn _ right v)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [burnolDirectRightResolventIntegrand,map_smul,FT_dilation]

private def unitRoot (v:BurnolL2) : BurnolL2 :=
  (2:ℂ) • burnolMultiplicativeDilation (Real.log q) v

private theorem unitRoot_actual : unitRoot ConstantDual.value=T burnolUnitCountingPrimitiveL2 := by
  have actual:=congrArg T ConstantFourier.reciprocal_value
  rw [burnolTateReciprocalL2_involutive] at actual
  change ConstantDual.value=T ((Real.sqrt q:ℂ) •
    burnolMultiplicativeDilation (Real.log q) burnolUnitCountingPrimitiveL2) at actual
  rw [map_smul] at actual
  have inverse:=burnolTateReciprocalL2_dilation_inverse (-Real.log q) burnolUnitCountingPrimitiveL2
  simp only [neg_neg] at inverse
  rw [←inverse] at actual
  have moved:=congrArg (burnolMultiplicativeDilation (Real.log q)) actual
  rw [map_smul,burnolMultiplicativeDilation_add,add_neg_cancel,burnolMultiplicativeDilation_zero] at moved
  have four:Real.sqrt (4:ℝ)=2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.sqrt_sq (by norm_num : (0:ℝ)≤2)]
  have root:Real.sqrt q=1/2 := by norm_num [Real.sqrt_div,four]
  rw [root] at moved
  unfold unitRoot
  linear_combination (norm:=module) (2:ℂ) • moved

private def boxScale (v:BurnolL2) (r:ℝ) : BurnolL2 :=
  (Real.sqrt r:ℂ) • burnolMultiplicativeDilation (-Real.log r) (unitRoot v)
private def boxProgram (lo hi:ℝ) (f f':ℝ→ℂ) (v:BurnolL2) : BurnolL2 :=
  f hi • (boxScale v hi-boxScale v lo)-
    ∫ u:ℝ in Ioc lo hi,f' u • (boxScale v u-boxScale v lo)

open private step family_integrable
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.WeightedProgram

private theorem boxProgram_actual (lo hi:ℝ) (f f':ℝ→ℂ) (positive:0<lo)
    (regular:ContinuousOn f' (Icc lo hi)) :
    T (WeightedProgram.program lo hi f f' burnolUnitCountingPrimitiveL2)=
      boxProgram lo hi f f' ConstantDual.value := by
  have scale (r:ℝ) : T (burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 r)=
      boxScale ConstantDual.value r := by
    change T ((Real.sqrt r:ℂ) • burnolMultiplicativeDilation (Real.log r)
      burnolUnitCountingPrimitiveL2)=_
    have inverse:=burnolTateReciprocalL2_dilation_inverse (-Real.log r) burnolUnitCountingPrimitiveL2
    simp only [neg_neg] at inverse
    rw [map_smul,←inverse,←unitRoot_actual]
    rfl
  unfold WeightedProgram.program boxProgram
  rw [map_sub,map_smul,←burnolTateReciprocalL2.integral_comp_comm
    (family_integrable lo hi f' positive regular burnolUnitCountingPrimitiveL2)]
  simp only [step,map_smul,map_sub,scale]

private theorem boxScale_R (c:BurnolCompletedMellinCoordinate) (v:BurnolL2) (r:ℝ) :
    R c (boxScale v r)=boxScale (R c v) r := by
  change burnolDirectRightResolvent (c.value/2) (boxScale v r)=_
  unfold boxScale unitRoot
  rw [burnolDirectRightResolvent_smul,burnolDirectRightResolvent_dilation,
    burnolDirectRightResolvent_smul,burnolDirectRightResolvent_dilation]
  rfl

private theorem box_family_integrable (lo hi:ℝ) (f':ℝ→ℂ) (positive:0<lo)
    (regular:ContinuousOn f' (Icc lo hi)) (v:BurnolL2) :
    IntegrableOn (fun u=>f' u • (boxScale v u-boxScale v lo)) (Ioc lo hi) := by
  have source:=burnolTateReciprocalL2.integrable_comp
    (family_integrable lo hi f' positive regular (T (unitRoot v)))
  apply source.congr
  filter_upwards with u
  have scale (r:ℝ) : T (burnolSourceScalePrimitive (T (unitRoot v)) r)=boxScale v r := by
    change T ((Real.sqrt r:ℂ) • burnolMultiplicativeDilation (Real.log r) (T (unitRoot v)))=_
    have inverse:=burnolTateReciprocalL2_dilation_inverse (-Real.log r) (T (unitRoot v))
    simp only [neg_neg] at inverse
    rw [map_smul,←inverse,burnolTateReciprocalL2_involutive]
    rfl
  simp only [step,map_smul,map_sub,scale]

private theorem boxProgram_R (c:BurnolCompletedMellinCoordinate) (lo hi:ℝ) (f f':ℝ→ℂ)
    (positive:0<lo) (regular:ContinuousOn f' (Icc lo hi)) (v:BurnolL2) :
    R c (boxProgram lo hi f f' v)=boxProgram lo hi f f' (R c v) := by
  unfold boxProgram
  rw [map_sub,map_smul,←(R c).integral_comp_comm
    (box_family_integrable lo hi f' positive regular v)]
  simp only [map_smul,map_sub,boxScale_R]

open private slope slope_measurable weight_integrable
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantForward

private def unitTailProgram (v:BurnolL2) : BurnolL2 :=
  -(∫ u:ℝ in Ioi 4,slope u • (boxScale v u-boxScale v 4))

private theorem unitTail_actual : T ConstantForward.value=unitTailProgram ConstantDual.value := by
  have scale (r:ℝ) : T (burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 r)=
      boxScale ConstantDual.value r := by
    change T ((Real.sqrt r:ℂ) • burnolMultiplicativeDilation (Real.log r)
      burnolUnitCountingPrimitiveL2)=_
    have inverse:=burnolTateReciprocalL2_dilation_inverse (-Real.log r) burnolUnitCountingPrimitiveL2
    simp only [neg_neg] at inverse
    rw [map_smul,←inverse,←unitRoot_actual]
    rfl
  unfold ConstantForward.value InfiniteWeightedProgram.program unitTailProgram
  rw [map_neg,←burnolTateReciprocalL2.integral_comp_comm
    (InfiniteWeightedProgram.family_integrable _ slope_measurable
      weight_integrable burnolUnitCountingPrimitiveL2)]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  change T (slope u • (burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 u-
    burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 4))=_
  rw [map_smul,map_sub,scale,scale]

private theorem unitTail_family_integrable (v:BurnolL2) :
    IntegrableOn (fun u=>slope u • (boxScale v u-boxScale v 4)) (Ioi 4) := by
  have source:=burnolTateReciprocalL2.integrable_comp
    (InfiniteWeightedProgram.family_integrable _ slope_measurable
      weight_integrable (T (unitRoot v)))
  apply source.congr
  filter_upwards with u
  have scale (r:ℝ) : T (burnolSourceScalePrimitive (T (unitRoot v)) r)=boxScale v r := by
    change T ((Real.sqrt r:ℂ) • burnolMultiplicativeDilation (Real.log r) (T (unitRoot v)))=_
    have inverse:=burnolTateReciprocalL2_dilation_inverse (-Real.log r) (T (unitRoot v))
    simp only [neg_neg] at inverse
    rw [map_smul,←inverse,burnolTateReciprocalL2_involutive]
    rfl
  change T (slope u • (burnolSourceScalePrimitive (T (unitRoot v)) u-
    burnolSourceScalePrimitive (T (unitRoot v)) 4))=_
  rw [map_smul,map_sub,scale,scale]

private theorem unitTail_R (c:BurnolCompletedMellinCoordinate) (v:BurnolL2) :
    R c (unitTailProgram v)=unitTailProgram (R c v) := by
  unfold unitTailProgram
  rw [map_neg,←(R c).integral_comp_comm (unitTail_family_integrable v)]
  simp only [map_smul,map_sub,boxScale_R]

/-- The same full forward source generates this entire Fourier/R effect, including its centering tail. -/
theorem full_forward_F_R (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (i:Fin 2) :
    R c (fourierL2 (FullUnit.fullForward c h i))=
      FT (boxProgram (bandLower h) 4 (positiveWeight c h i) (deriv (positiveWeight c h i))
        (unitCurrent c zero)+centeringMean c h i • unitTailProgram (unitCurrent c zero)) := by
  have regular:ContinuousOn (deriv (positiveWeight c h i)) (Icc (bandLower h) 4) :=
    (positiveWeight_deriv_continuousOn c h i).mono (fun _ inside=>(bandLower_pos h).trans_le inside.1)
  have wave:T (exteriorWave c h i)=boxProgram (bandLower h) 4 (positiveWeight c h i)
      (deriv (positiveWeight c h i)) ConstantDual.value :=
    boxProgram_actual _ _ _ _ (bandLower_pos h) regular
  have full:fourierL2 (FullUnit.fullForward c h i)=FT
      (boxProgram (bandLower h) 4 (positiveWeight c h i) (deriv (positiveWeight c h i))
        ConstantDual.value+centeringMean c h i • unitTailProgram ConstantDual.value) := by
    rw [←wave,←unitTail_actual]
    change fourierL2 (FullUnit.fullForward c h i)=fourierL2 (T (T (exteriorWave c h i)+
      centeringMean c h i • T ConstantForward.value))
    rw [map_add,map_smul,burnolTateReciprocalL2_involutive,burnolTateReciprocalL2_involutive]
    rfl
  rw [full,←FT_R]
  congr 1
  rw [map_add,map_smul,boxProgram_R c _ _ _ _ (bandLower_pos h) regular,unitTail_R,actual_unit_R]

end OriginalFullLossRAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
