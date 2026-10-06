import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationActualSpectralCurrent

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalAbelZeroRead
open GaussCoreHilbert GaussUnitaryHistory SourceJointResidualEnergy
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalHalfAxis
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumGaugeSourceInjection PreparationVacuumSourceFieldFamily
open PreparationVacuumMixedFieldReturn
open MeasureTheory Filter Set
open scoped Topology BigOperators InnerProductSpace

/-- The actual spectral frequency difference retains all degenerate pairs. -/
def sourceStaticGap (F : GaussUnitaryHistory.Index) (i j : Channel F) : ℝ :=
  channelValue F i-channelValue F j

theorem sourceStaticPhase_exp (F : GaussUnitaryHistory.Index) (i j : Channel F) (t : ℝ) :
    sourceStaticPhase F i j t=Complex.exp (Complex.I*(sourceStaticGap F i j : ℂ)*(t : ℂ)) := by
  unfold sourceStaticPhase sourcePhase sourceStaticGap
  simp only [Complex.star_def,←Complex.exp_conj,map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal]
  rw [←Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_sub]
  ring

def sourceStaticDenominator (F : GaussUnitaryHistory.Index) (i j : Channel F) (lambda : ℂ) : ℂ :=
  lambda-Complex.I*(sourceStaticGap F i j : ℂ)

private theorem weighted_source_exp (F : GaussUnitaryHistory.Index) (i j : Channel F) (lambda : ℂ) (t : ℝ) :
    laplaceWeight lambda t*sourceStaticPhase F i j t=
      Complex.exp (-(sourceStaticDenominator F i j lambda)*(t : ℂ)) := by
  rw [sourceStaticPhase_exp]
  unfold laplaceWeight sourceStaticDenominator
  rw [←Complex.exp_add]
  congr 1
  ring

private theorem weighted_source_integrable (F : GaussUnitaryHistory.Index) (i j : Channel F)
    (lambda : ℂ) (off : 0<lambda.re) :
    IntegrableOn (fun t : ℝ=>laplaceWeight lambda t*sourceStaticPhase F i j t) (Ioi 0) := by
  simp_rw [weighted_source_exp]
  apply integrableOn_exp_mul_complex_Ioi _ 0
  simpa only [sourceStaticDenominator,Complex.neg_re,Complex.sub_re,Complex.mul_re,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,neg_lt_zero] using off

private theorem weighted_source_integral (F : GaussUnitaryHistory.Index) (i j : Channel F)
    (lambda : ℂ) (off : 0<lambda.re) :
    (∫ t : ℝ in Ioi 0,laplaceWeight lambda t*sourceStaticPhase F i j t)=
      (sourceStaticDenominator F i j lambda)⁻¹ := by
  simp_rw [weighted_source_exp]
  rw [integral_exp_mul_complex_Ioi (show (-(sourceStaticDenominator F i j lambda)).re<0 from
    by simpa only [sourceStaticDenominator,Complex.neg_re,Complex.sub_re,Complex.mul_re,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,neg_lt_zero] using off) 0]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,div_neg,neg_div,neg_neg,one_div]

def sourceStaticAbel (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) (lambda : ℂ) : ℂ :=
  ∑ i : Channel q.F,∑ j : Channel q.F,
    (sourceStaticDenominator q.F i j lambda)⁻¹*sourceStaticCoefficient q left right mu a i j

theorem sourceStaticHalf_generated (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) (lambda : ℂ) (off : 0<lambda.re)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot mu a)=
      sourceStaticAbel q left right mu a lambda := by
  unfold sourcePoleCurrentHalf sourceStaticAbel
  simp_rw [sourceStaticCurrent_channels q left right mu a _ nonrealL nonrealR,Finset.mul_sum,←mul_assoc]
  rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>
    (weighted_source_integrable q.F i j lambda off).mul_const _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _=>(weighted_source_integrable q.F i j lambda off).mul_const _)]
  simp only [integral_mul_const,weighted_source_integral q.F _ _ lambda off]



/-- This is the exact actual static residue, retaining energy degeneracy and the escape channel. -/
def sourceStaticResidue (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) : ℂ :=
  ∑ i : Channel q.F,∑ j : Channel q.F,
    if channelValue q.F i=channelValue q.F j then sourceStaticCoefficient q left right mu a i j else 0

private theorem abel_factor_zero (d : ℝ) :
    Tendsto (fun eta : ℝ=>(eta : ℂ)*((eta : ℂ)-Complex.I*(d : ℂ))⁻¹)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (if d=0 then (1 : ℂ) else 0)) := by
  by_cases hd : d=0
  · rw [if_pos hd]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with eta heta
    have hn : (eta : ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ne_of_gt heta)
    simp only [hd,Complex.ofReal_zero,mul_zero,sub_zero,mul_inv_cancel₀ hn]
  · rw [if_neg hd]
    have hn : (0 : ℂ)-Complex.I*(d : ℂ)≠0:=by
      simp only [zero_sub,neg_ne_zero]
      exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hd)
    have hcast : Tendsto (fun eta : ℝ=>(eta : ℂ)) (nhdsWithin 0 (Ioi 0)) (𝓝 (0 : ℂ)):=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hden := hcast.sub_const (Complex.I*(d : ℂ))
    have h := hcast.mul (hden.inv₀ hn)
    simpa only [zero_mul] using h

theorem sourceStaticAbel_zero (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) :
    Tendsto (fun eta : ℝ=>(eta : ℂ)*sourceStaticAbel q left right mu a (eta : ℂ))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (sourceStaticResidue q left right mu a)) := by
  classical
  simp only [sourceStaticAbel,Finset.mul_sum]
  unfold sourceStaticResidue
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  have h := (abel_factor_zero (sourceStaticGap q.F i j)).mul_const (sourceStaticCoefficient q left right mu a i j)
  simpa only [sourceStaticDenominator,sourceStaticGap,sub_eq_zero,mul_assoc,ite_mul,one_mul,zero_mul] using h

theorem sourceActualStaticHalf_Abel_zero (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun eta : ℝ=>(eta : ℂ)*sourcePoleCurrentHalf q 0 0 left right (eta : ℂ) (gaugeSlot mu a))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (sourceStaticResidue q left right mu a)) := by
  apply (sourceStaticAbel_zero q left right mu a).congr'
  filter_upwards [self_mem_nhdsWithin] with eta heta
  rw [sourceStaticHalf_generated q left right mu a (eta : ℂ) (by simpa only [Complex.ofReal_re] using (show 0<eta from heta)) nonrealL nonrealR]

end LowEnergy.PreparationVacuumPhysicalAbelZeroRead
