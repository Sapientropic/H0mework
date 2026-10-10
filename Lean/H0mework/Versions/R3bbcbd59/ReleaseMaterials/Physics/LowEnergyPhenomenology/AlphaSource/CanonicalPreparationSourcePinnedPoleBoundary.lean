import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePinnedPoleChannels
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceJointCausalField

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumObservedPoleTensor
open GaussCoreHilbert GaussUnitaryHistory SourceJointResidualEnergy
open PreparationVacuumPhysicalSlowBlock PreparationVacuumPhysicalPinnedVelocity
open CanonicalGradedSpatialSource
open Filter Set
open scoped BigOperators InnerProductSpace Topology
attribute [local irreducible] sourcePinnedChannel sourcePinnedVelocity sourcePinnedResolvent

def sourcePoleSide (c eta : ℝ) : ℂ := (eta:ℂ)+Complex.I*(c:ℂ)
def sourceVelocityGap (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c : ℝ) (i : Channel F) : ℝ :=
  sourcePinnedValue F n i+c

def sourceResonanceProjection (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c : ℝ) : SourceOp :=
  ∑i : Channel F,if sourceVelocityGap F n c i=0 then sourcePinnedChannel F n i else 0

def sourceOffPoleReturn (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c eta : ℝ) : SourceOp :=
  ∑i : Channel F,if sourceVelocityGap F n c i=0 then 0 else
    ((eta:ℂ)+Complex.I*(sourceVelocityGap F n c i:ℂ))⁻¹ • sourcePinnedChannel F n i

def sourceOffPolePrice (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c : ℝ) : ℝ :=
  ∑i : Channel F,if sourceVelocityGap F n c i=0 then 0 else |sourceVelocityGap F n c i|⁻¹

def sourceOffPoleError (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c : ℝ) : ℝ :=
  ∑i : Channel F,if sourceVelocityGap F n c i=0 then 0 else |sourceVelocityGap F n c i|⁻¹^2

theorem sourceOffPolePrice_nonneg (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c : ℝ) : 0 ≤ sourceOffPolePrice F n c := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> positivity

theorem sourcePinnedResolvent_boundary (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c eta : ℝ) (positive : 0<eta) :
    sourcePinnedResolvent F n (sourcePoleSide c eta)=
      (eta:ℂ)⁻¹ • sourceResonanceProjection F n c+sourceOffPoleReturn F n c eta := by
  have realPart : (sourcePoleSide c eta).re=eta := by simp [sourcePoleSide]
  rw [sourcePinnedResolvent_channels F n _ (by rw [realPart];exact positive)]
  unfold sourceResonanceProjection sourceOffPoleReturn
  rw [Finset.smul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have denominator : sourcePoleSide c eta+Complex.I*(sourcePinnedValue F n i:ℂ)=
      (eta:ℂ)+Complex.I*(sourceVelocityGap F n c i:ℂ) := by
    simp only [sourcePoleSide,sourceVelocityGap,Complex.ofReal_add]
    ring
  rw [denominator]
  by_cases resonant : sourceVelocityGap F n c i=0
  · rw [if_pos resonant]
    simp only [resonant,Complex.ofReal_zero,mul_zero,add_zero,if_true]

  · rw [if_neg resonant,if_neg resonant]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.zero_apply]
    simp only [smul_zero, zero_add]

theorem sourceResonance_eigen (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c : ℝ) :
    sourcePinnedVelocity F n*sourceResonanceProjection F n c=(-c:ℂ) • sourceResonanceProjection F n c := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [sourceResonanceProjection,mul_apply_eq_comp,sum_apply,map_sum,smul_apply,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases resonant : sourceVelocityGap F n c i=0
  · rw [if_pos resonant]
    have eigen:=congrArg (fun A : SourceOp=>A x) (sourcePinnedChannel_eigen F n i)
    have value : sourcePinnedValue F n i= -c := eq_neg_of_add_eq_zero_left resonant
    change sourcePinnedVelocity F n (sourcePinnedChannel F n i x)=
      (sourcePinnedValue F n i:ℂ) • sourcePinnedChannel F n i x at eigen
    simpa only [value,Complex.ofReal_neg] using eigen
  · simp only [if_neg resonant,zero_apply,map_zero,smul_zero]

private theorem gap_denominator (eta g : ℝ) (nonzero : g≠0) : (eta:ℂ)+Complex.I*(g:ℂ)≠0 := by
  intro zero
  have imaginary:=congrArg Complex.im zero
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,zero_mul,one_mul,zero_add,Complex.zero_im] at imaginary
  exact nonzero imaginary

private theorem gap_inverse_price (eta g : ℝ) (nonzero : g≠0) :
    ‖((eta:ℂ)+Complex.I*(g:ℂ))⁻¹‖ ≤ |g|⁻¹ := by
  rw [norm_inv]
  apply inv_anti₀ (abs_pos.mpr nonzero)
  have lower:=Complex.abs_im_le_norm ((eta:ℂ)+Complex.I*(g:ℂ))
  simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,zero_mul,one_mul,zero_add] using lower

private theorem gap_inverse_error (eta g : ℝ) (nonzero : g≠0) :
    ‖((eta:ℂ)+Complex.I*(g:ℂ))⁻¹-(Complex.I*(g:ℂ))⁻¹‖ ≤ |eta| *|g|⁻¹^2 := by
  have zeroGap : Complex.I*(g:ℂ)≠0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr nonzero)
  have difference : ((eta:ℂ)+Complex.I*(g:ℂ))⁻¹-(Complex.I*(g:ℂ))⁻¹=
      -(eta:ℂ)*(((eta:ℂ)+Complex.I*(g:ℂ))⁻¹*(Complex.I*(g:ℂ))⁻¹) := by
    field_simp [gap_denominator eta g nonzero,zeroGap,Complex.ofReal_ne_zero.mpr nonzero]
    ring
  rw [difference]
  simp only [norm_mul,norm_neg,norm_inv,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,one_mul]
  calc
    _≤|eta| *(|g|⁻¹*|g|⁻¹) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by simpa only [norm_inv] using gap_inverse_price eta g nonzero) (inv_nonneg.mpr (abs_nonneg g))) (abs_nonneg eta)
    _=_ := by ring

theorem sourceOffPoleReturn_price (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c eta : ℝ) :
    ‖sourceOffPoleReturn F n c eta‖ ≤ sourceOffPolePrice F n c := by
  unfold sourceOffPoleReturn sourceOffPolePrice
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  by_cases resonant : sourceVelocityGap F n c i=0
  · simp only [if_pos resonant,norm_zero,le_refl]
  · rw [if_neg resonant,if_neg resonant]
    exact (ContinuousLinearMap.opNorm_smul_le _ _).trans
      ((mul_le_mul (gap_inverse_price eta _ resonant) (sourcePinnedChannel_price F n i)
        (norm_nonneg _) (inv_nonneg.mpr (abs_nonneg _))).trans_eq (mul_one _))

private theorem op_sub_smul (a b : ℂ) (Q : SourceOp) : a • Q-b • Q=(a-b) • Q := by
  apply ContinuousLinearMap.ext
  intro x
  exact (sub_smul a b (Q x)).symm

theorem sourceOffPoleReturn_error (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c eta : ℝ) :
    ‖sourceOffPoleReturn F n c eta-sourceOffPoleReturn F n c 0‖ ≤ |eta| *sourceOffPoleError F n c := by
  unfold sourceOffPoleReturn sourceOffPoleError
  rw [←Finset.sum_sub_distrib,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  by_cases resonant : sourceVelocityGap F n c i=0
  · simp only [if_pos resonant,sub_self,norm_zero,mul_zero,le_refl]
  · rw [if_neg resonant,if_neg resonant,if_neg resonant]
    simp only [Complex.ofReal_zero,zero_add]
    rw [op_sub_smul]
    exact (ContinuousLinearMap.opNorm_smul_le _ _).trans
      ((mul_le_mul (gap_inverse_error eta _ resonant) (sourcePinnedChannel_price F n i)
        (norm_nonneg _) (mul_nonneg (abs_nonneg eta) (sq_nonneg _))).trans_eq (mul_one _))

def sourcePoleGapRadius (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c : ℝ) : ℝ :=
  (2*(sourceOffPolePrice F n c+1))⁻¹

theorem sourcePoleGapRadius_positive (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c : ℝ) :
    0<sourcePoleGapRadius F n c := by
  unfold sourcePoleGapRadius
  have nonnegative:=sourceOffPolePrice_nonneg F n c
  positivity

theorem sourcePoleGapRadius_gap (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c : ℝ) (i : Channel F)
    (nonzero : sourceVelocityGap F n c i≠0) :
    2*sourcePoleGapRadius F n c ≤ |sourceVelocityGap F n c i| := by
  have single : |sourceVelocityGap F n c i|⁻¹ ≤ sourceOffPolePrice F n c := by
    have h:=Finset.single_le_sum
      (f:=fun j : Channel F=>if sourceVelocityGap F n c j=0 then 0 else |sourceVelocityGap F n c j|⁻¹)
      (fun j _=>by split_ifs <;> positivity) (Finset.mem_univ i)
    simpa only [if_neg nonzero,sourceOffPolePrice] using h
  have positive : 0<sourceOffPolePrice F n c+1 := by have h:=sourceOffPolePrice_nonneg F n c;linarith
  have reciprocal : (sourceOffPolePrice F n c+1)⁻¹ ≤ |sourceVelocityGap F n c i| := by
    rw [inv_le_iff_one_le_mul₀ positive]
    have gapPositive:=abs_pos.mpr nonzero
    have product:=mul_le_mul_of_nonneg_left single gapPositive.le
    rw [mul_inv_cancel₀ gapPositive.ne'] at product
    nlinarith
  have normal : 2*sourcePoleGapRadius F n c=(sourceOffPolePrice F n c+1)⁻¹ := by
    unfold sourcePoleGapRadius
    field_simp [positive.ne']
  rw [normal]
  exact reciprocal

theorem sourceOffPoleReturn_limit (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c : ℝ) :
    Tendsto (sourceOffPoleReturn F n c) (𝓝 0) (𝓝 (sourceOffPoleReturn F n c 0)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun eta=>norm_nonneg _) (sourceOffPoleReturn_error F n c)
  simpa only [abs_zero,zero_mul] using (continuous_abs.tendsto (0:ℝ)).mul
    (tendsto_const_nhds (x:=sourceOffPoleError F n c))

theorem sourcePinnedResolvent_residue_price (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c eta : ℝ)
    (positive : 0<eta) :
    ‖(eta:ℂ) • sourcePinnedResolvent F n (sourcePoleSide c eta)-sourceResonanceProjection F n c‖ ≤
      eta*sourceOffPolePrice F n c := by
  have identity : (eta:ℂ) • sourcePinnedResolvent F n (sourcePoleSide c eta)-sourceResonanceProjection F n c=
      (eta:ℂ) • sourceOffPoleReturn F n c eta := by
    rw [sourcePinnedResolvent_boundary F n c eta positive]
    apply ContinuousLinearMap.ext
    intro x
    change (eta:ℂ) • ((eta:ℂ)⁻¹ • sourceResonanceProjection F n c x+sourceOffPoleReturn F n c eta x)-
      sourceResonanceProjection F n c x=_
    rw [smul_add,smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr positive.ne'),one_smul,add_sub_cancel_left]
    rfl
  rw [identity]
  exact (ContinuousLinearMap.opNorm_smul_le _ _).trans
    ((mul_le_mul_of_nonneg_left (sourceOffPoleReturn_price F n c eta) (norm_nonneg (eta:ℂ))).trans_eq
      (by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]))

theorem sourcePinnedResolvent_residue (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c : ℝ) :
    Tendsto (fun eta : ℝ=>(eta:ℂ) • sourcePinnedResolvent F n (sourcePoleSide c eta))
      (𝓝[>] 0) (𝓝 (sourceResonanceProjection F n c)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have pos : ∀ᶠ eta : ℝ in 𝓝[>] 0, 0 < eta := self_mem_nhdsWithin
  apply squeeze_zero' (Eventually.of_forall (fun eta=>norm_nonneg _))
    (pos.mono (fun eta positive=>sourcePinnedResolvent_residue_price F n c eta positive))
  simpa only [zero_mul,id_eq] using
    ((tendsto_id : Tendsto (fun eta : ℝ=>eta) (𝓝 0) (𝓝 0)).mul
      (tendsto_const_nhds (x:=sourceOffPolePrice F n c))).mono_left nhdsWithin_le_nhds

open PreparationVacuumFullSlowFieldResponse PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalCharacteristic PreparationVacuumOriginalGreenFeedback
open scoped Matrix Matrix.Norms.Operator

private theorem side_quadratic (a b c eta : ℝ) (coefficient : a≠0) (frequency : c≠0)
    (positive : 0<eta) : (a:ℂ)*(sourcePoleSide c eta)^2+(b:ℂ)≠0 := by
  intro zero
  have imaginary:=congrArg Complex.im zero
  have generated : ((a:ℂ)*(sourcePoleSide c eta)^2+(b:ℂ)).im=2*a*eta*c := by
    simp only [sourcePoleSide,pow_two,Complex.add_im,Complex.add_re,Complex.mul_im,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,one_mul,zero_add,
      add_zero,sub_zero]
    ring
  rw [generated,Complex.zero_im] at imaginary
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (2:ℝ)≠0) coefficient) positive.ne') frequency) imaginary

/-- Every nonzero source frequency has an actual causal side in the full field corner. -/
theorem sourcePoleSide_field_domain (n : PhysicalMomentum) (c eta : ℝ) (frequency : c≠0)
    (positive : 0<eta) : sourcePoleSide c eta∈sourceCausalDomain n := by
  have realPart : (sourcePoleSide c eta).re=eta := by simp [sourcePoleSide]
  refine ⟨by rw [realPart];exact positive,?_⟩
  have nonzero : sourcePoleSide c eta≠0 := by
    intro h
    have zero:=congrArg Complex.re h
    rw [realPart,Complex.zero_re] at zero
    exact positive.ne' zero
  have two : rootTwo≠0 := by norm_num [rootTwo,Real.sqrt_ne_zero']
  have fifteen : rootFifteen≠0 := by norm_num [rootFifteen,Real.sqrt_ne_zero']
  have root : rootTwo*rootFifteen≠0 := mul_ne_zero two fifteen
  have a:=side_quadratic (-(25/18:ℝ)) ((25/54:ℝ)*spatialSquare n) c eta (by norm_num) frequency positive
  have b:=side_quadratic (10/99:ℝ) ((12/335:ℝ)*spatialSquare n) c eta (by norm_num) frequency positive
  have k:=side_quadratic (20/27:ℝ) ((8/15:ℝ)*spatialSquare n) c eta (by norm_num) frequency positive
  norm_num only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_mul] at a b k
  rw [sourceCausalPrincipal_det]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (by norm_num : (128:ℂ)≠0) (pow_ne_zero 2 nonzero)) (mul_ne_zero root a))
    (mul_ne_zero root b)) (mul_ne_zero root k)

def sourceSignedSpeed (branch : Fin 2) (negative : Bool) : ℝ :=
  if negative then -sourceSpeed branch else sourceSpeed branch

theorem sourceSignedSpeed_nonzero (branch : Fin 2) (negative : Bool) : sourceSignedSpeed branch negative≠0 := by
  unfold sourceSignedSpeed
  split_ifs
  · exact neg_ne_zero.mpr (sourceSpeed_positive branch).ne'
  · exact (sourceSpeed_positive branch).ne'

def sourceObservedSide (n : PhysicalMomentum) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (positive : 0<eta) : sourceCausalDomain n :=
  ⟨sourcePoleSide (sourceSignedSpeed branch negative) eta,
    sourcePoleSide_field_domain n _ eta (sourceSignedSpeed_nonzero branch negative) positive⟩

end LowEnergy.PreparationVacuumObservedPoleTensor
