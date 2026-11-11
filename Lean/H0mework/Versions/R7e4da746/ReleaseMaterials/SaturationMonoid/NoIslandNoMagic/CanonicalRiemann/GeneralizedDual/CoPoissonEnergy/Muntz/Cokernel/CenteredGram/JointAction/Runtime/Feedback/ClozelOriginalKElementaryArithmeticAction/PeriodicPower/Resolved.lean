import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Prolate.FourierTail

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Resolved
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszSource.Translator
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction OriginalKElementaryArithmeticAction.FreeParameter.Riesz
open OriginalKElementaryArithmeticAction.PeriodicPower.Source OriginalKElementaryArithmeticAction.PeriodicPower.Lattice
open ProlateKernel ProlateFourierTail
open scoped Topology ENNReal InnerProductSpace
open private phase_pair sinTail_step cos_norm from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Prolate.FourierTail
local notation "q" => (1/4:ℝ)
local notation "F" => fourierL2
local notation "C" => ConstantDual.seed
local notation "freq" => (2*(Real.pi:ℂ))

def jumpCoefficient (c : BurnolCompletedMellinCoordinate) : ℂ :=
  GapEuler.gapMean q c-(1/2:ℂ)*(q:ℂ)^(-star c.value)

def resolvedSource (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  elementarySource c-jumpCoefficient c • C

def resolvedRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (1/2:ℂ)*((max q |x|:ℝ):ℂ)^(-star c.value)

private theorem denominator_ne (c : BurnolCompletedMellinCoordinate) : 1-star c.value≠0 := by
  intro same
  have realPart:=congrArg Complex.re same
  simp only [sub_re,one_re,star_def,conj_re,zero_re] at realPart
  linarith [c.belowOne]

theorem actual_jump_coefficient (c : BurnolCompletedMellinCoordinate) :
    jumpCoefficient c=coefficient (star c.value) := by
  have gap:=GapEuler.gapMean_primitive q (by norm_num) c
  unfold jumpCoefficient coefficient
  apply (eq_div_iff (mul_ne_zero (by norm_num) (denominator_ne c))).mpr
  linear_combination 2*gap

/-- Removing the literal q jump leaves the same original R source, with its complete coefficient. -/
theorem actual_resolved_R_source (c : BurnolCompletedMellinCoordinate) :
    resolvedSource c=(-star c.value*(q:ℂ)^(-star c.value)/4) •
      burnolDirectRightResolvent (star c.value/2) C := by
  rw [resolvedSource,←elementary_unit_resolvent,actual_free_unit,actual_jump_coefficient,freeUnit]
  simp only [smul_sub,smul_smul]
  have scalar : -(coefficient (star c.value)*((1-star c.value)/2))=
      -star c.value*(q:ℂ)^(-star c.value)/4 := by
    unfold coefficient
    calc
      _=(-star c.value*(q:ℂ)^(-star c.value)/4)*((1-star c.value)/(1-star c.value)) := by
        simp only [div_mul_eq_div_div]
        ring
      _=_ := by rw [div_self (denominator_ne c),mul_one]
  calc
    _=(-(coefficient (star c.value)*((1-star c.value)/2))) •
        burnolDirectRightResolvent (star c.value/2) C := by module
    _=_ := by rw [scalar]

private theorem even_gap_raw (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolEvenRaw (burnolAmbientMellinKernelRaw c) x=
      burnolEvenRaw (burnolAmbientMellinKernelRaw c) |x| := by
  rcases le_total 0 x with positive|negative
  · rw [abs_of_nonneg positive]
  · rw [abs_of_nonpos negative]
    unfold burnolEvenRaw
    simp only [neg_neg]
    ring

theorem actual_resolved_raw (c : BurnolCompletedMellinCoordinate) :
    (resolvedSource c:ℝ→ℂ)=ᵐ[volume]resolvedRaw c := by
  filter_upwards [Lp.coeFn_sub (elementarySource c) (jumpCoefficient c • C),
    Lp.coeFn_smul (jumpCoefficient c) C,gapState_read c,ConstantDual.seed_coeFn]
    with x difference scalar elementary constant
  change (elementarySource c-jumpCoefficient c • C:BurnolL2) x=_
  rw [difference,Pi.sub_apply,scalar,Pi.smul_apply,smul_eq_mul]
  change elementarySource c x=burnolEvenRaw (burnolAmbientMellinKernelRaw c) x at elementary
  rw [elementary,constant]
  by_cases inside : |x|≤q
  · rw [ConstantDual.seedRaw,if_pos inside,gapState_raw_gap c (abs_le.mp inside),
      resolvedRaw,max_eq_left inside]
    unfold jumpCoefficient
    ring
  · have outside : q < |x| := lt_of_not_ge inside
    rw [ConstantDual.seedRaw,if_neg inside,mul_zero,sub_zero,even_gap_raw,
      gapState_raw_tail c outside,resolvedRaw,max_eq_right outside.le]

theorem actual_resolved_continuous (c : BurnolCompletedMellinCoordinate) :
    Continuous (resolvedRaw c) := by
  have powerContinuous : Continuous (fun x:ℝ=>((max q |x|:ℝ):ℂ)^(-star c.value)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ContinuousAt.comp (g:=fun y:ℝ=>(y:ℂ)^(-star c.value)) (f:=fun y:ℝ=>max q |y|)
      (Complex.continuousAt_ofReal_cpow_const (max q |x|) (-star c.value)
        (Or.inr (ne_of_gt (lt_of_lt_of_le (by norm_num:(0:ℝ)<q) (le_max_left _ _)))))
      (continuous_const.max continuous_abs).continuousAt
  exact continuous_const.mul powerContinuous

theorem actual_resolved_positive_sample (c : BurnolCompletedMellinCoordinate) (n : ℕ) :
    resolvedRaw c (n+1)=powerSample c n := by
  have positive : (0:ℝ)≤n+1 := by positivity
  have outside : q≤n+1 := by have nn:=Nat.cast_nonneg (α:=ℝ) n;linarith
  rw [resolvedRaw,abs_of_nonneg positive,max_eq_right outside]
  unfold powerSample
  push_cast
  rfl

def resolvedFourierRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ForcingWhole.raw c x-jumpCoefficient c*burnolRadiusTruncatedFourierRaw q (intervalConstant q) x

theorem actual_resolved_fourier_raw (c : BurnolCompletedMellinCoordinate) :
    (F (resolvedSource c):ℝ→ℂ)=ᵐ[volume]resolvedFourierRaw c := by
  rw [resolvedSource,map_sub,map_smul]
  filter_upwards [Lp.coeFn_sub (F (elementarySource c)) (jumpCoefficient c • F C),
    Lp.coeFn_smul (jumpCoefficient c) (F C),ForcingWhole.whole_read c,
    burnolRadiusFourierL2_zeroExtension_ae_eq_raw (intervalConstant q)] with x difference scalar actual box
  change (F (elementarySource c)-jumpCoefficient c • F C:BurnolL2) x=_
  rw [difference,Pi.sub_apply,scalar,Pi.smul_apply,smul_eq_mul]
  change F (elementarySource c) x=ForcingWhole.raw c x at actual
  change F C x=burnolRadiusTruncatedFourierRaw q (intervalConstant q) x at box
  rw [actual,box]
  rfl

private theorem box_fourier_trig (x : ℝ) (nonzero : x≠0) :
    burnolRadiusTruncatedFourierRaw q (intervalConstant q) x=
      2*Complex.sin (scale*(x:ℂ))/(freq*(x:ℂ)) := by
  have source:=Edge.raw_apply q x
  rw [phase_pair] at source
  have edge:=ProlateFourierTail.EdgeTrig.original_trig x nonzero
  unfold scale frequency at edge
  unfold scale frequency
  linear_combination source-edge

/-- The leading 1/x edge term cancels against the actual constant seed Fourier source. -/
theorem actual_resolved_fourier_tail (c : BurnolCompletedMellinCoordinate) (x : ℝ) (nonzero : x≠0) :
    resolvedFourierRaw c x=
      star c.value*((q:ℂ)^(-(star c.value+1))*Complex.cos (scale*(x:ℂ))-
        (star c.value+1)*cosTail c 2 x)/(freq*(x:ℂ))^2 := by
  have original:=ProlateFourierTail.original_numerator c nonzero
  have integrated:=sinTail_step c 1 (by omega) x
  norm_num only [Nat.cast_one,Nat.reduceAdd] at integrated
  rw [resolvedFourierRaw,box_fourier_trig x nonzero]
  unfold jumpCoefficient
  have ne : freq*(x:ℂ)≠0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    (Complex.ofReal_ne_zero.mpr nonzero)
  field_simp [Complex.ofReal_ne_zero.mpr nonzero,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  linear_combination (freq*(x:ℂ))*original+star c.value*integrated

def tailMass (c : BurnolCompletedMellinCoordinate) : ℝ :=
  ∫t:ℝ in Ioi q,‖(t:ℂ)^(-(star c.value+2))‖

private theorem cos_tail_bound (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    ‖cosTail c 2 x‖≤tailMass c := by
  have one (y:ℝ) : ‖tail c 2 y‖≤tailMass c := by
    apply (norm_integral_le_integral_norm _).trans_eq
    apply integral_congr_ae
    filter_upwards with t
    simp only [Constructor.phase,norm_mul,Circle.norm_coe,mul_one,Nat.cast_ofNat]
  unfold cosTail
  rw [norm_div,norm_ofNat]
  apply (div_le_iff₀ (by norm_num:(0:ℝ)<2)).mpr
  exact (norm_add_le _ _).trans ((add_le_add (one x) (one (-x))).trans_eq (by ring))

def tailBound (c : BurnolCompletedMellinCoordinate) : ℝ :=
  ‖star c.value‖*(‖(q:ℂ)^(-(star c.value+1))‖+‖star c.value+1‖*tailMass c)/(2*Real.pi)^2

theorem actual_resolved_fourier_bound (c : BurnolCompletedMellinCoordinate) (x : ℝ) (nonzero : x≠0) :
    ‖resolvedFourierRaw c x‖≤tailBound c/|x|^2 := by
  rw [actual_resolved_fourier_tail c x nonzero,norm_div,norm_mul,norm_pow,norm_mul]
  have numerator : ‖(q:ℂ)^(-(star c.value+1))*Complex.cos (scale*(x:ℂ))-
      (star c.value+1)*cosTail c 2 x‖≤
      ‖(q:ℂ)^(-(star c.value+1))‖+‖star c.value+1‖*tailMass c := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul,norm_mul]
    exact add_le_add ((mul_le_mul_of_nonneg_left (cos_norm x) (norm_nonneg _)).trans_eq (mul_one _))
      (mul_le_mul_of_nonneg_left (cos_tail_bound c x) (norm_nonneg _))
  apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left numerator (norm_nonneg _)) (sq_nonneg _)).trans_eq
  rw [norm_mul,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
    Complex.norm_real,Real.norm_eq_abs]
  unfold tailBound
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Resolved
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
