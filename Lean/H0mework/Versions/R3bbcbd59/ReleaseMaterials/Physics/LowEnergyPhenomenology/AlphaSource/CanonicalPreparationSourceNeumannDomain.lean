import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceCoefficientPrice

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMixedControl
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedEffective
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] activeKernel complementInverse

def inverseBudget : ℝ:=1+(termsPrice complementInverseTerms:ℝ)
def variationBudget : ℝ:=1+(termsPrice (positiveTerms activeTerms):ℝ)
def sourceRadius : ℝ:=(4*inverseBudget*variationBudget)⁻¹

theorem inverseBudget_ge_one : 1 ≤ inverseBudget :=by
  have h : (0:ℝ) ≤ (termsPrice complementInverseTerms:ℝ):=by exact_mod_cast termsPrice_nonneg complementInverseTerms
  unfold inverseBudget;linarith

theorem variationBudget_ge_one : 1 ≤ variationBudget :=by
  have h : (0:ℝ) ≤ (termsPrice (positiveTerms activeTerms):ℝ):=by exact_mod_cast termsPrice_nonneg (positiveTerms activeTerms)
  unfold variationBudget;linarith

theorem sourceRadius_pos : 0<sourceRadius :=by
  have b:=inverseBudget_ge_one
  have k:=variationBudget_ge_one
  unfold sourceRadius
  positivity

theorem sourceRadius_le_one : sourceRadius ≤ 1 :=by
  have b:=inverseBudget_ge_one
  have k:=variationBudget_ge_one
  have product : 1 ≤ 4*inverseBudget*variationBudget:=by nlinarith
  exact inv_le_one_of_one_le₀ product

private theorem projection_price (flag : Fin 289→Bool) : ‖projectionMatrix flag‖ ≤ 1 :=by
  rw [projectionMatrix,Matrix.linfty_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro i
  split_ifs <;> norm_num

theorem complementProjection_price : ‖complementProjection‖ ≤ 1:=projection_price complementFlag

private theorem projectionComplement_price : ‖(1:Matrix (Fin 289) (Fin 289) ℂ)-complementProjection‖ ≤ 1 :=by
  have identity : (1:Matrix (Fin 289) (Fin 289) ℂ)=Matrix.diagonal (fun _=>1):=rfl
  rw [identity,complementProjection,projectionMatrix,Matrix.diagonal_sub,Matrix.linfty_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro i
  split_ifs <;> norm_num

theorem complementInverse_price : ‖complementInverse‖ ≤ (termsPrice complementInverseTerms:ℝ) :=by
  have checked : complementInverseTerms.all (fun a=>decide (a.powers.total=0))=true:=by decide +kernel
  have homogeneous : ∀a∈complementInverseTerms,a.powers.total=0:=by
    intro a ha
    exact of_decide_eq_true (List.all_eq_true.mp checked a ha)
  simpa only [pow_zero,mul_one,complementInverse] using
    sourceMatrix_homogeneous_price complementInverseTerms 0 homogeneous 0 0 le_rfl (fun i=>by simp)

theorem complementOriginInverse_price : ‖complementOriginInverse‖ ≤ inverseBudget :=by
  unfold complementOriginInverse inverseBudget
  calc
    _ ≤ ‖complementInverse‖+‖(1:Matrix (Fin 289) (Fin 289) ℂ)-complementProjection‖:=norm_add_le _ _
    _ ≤ (termsPrice complementInverseTerms:ℝ)+1:=add_le_add complementInverse_price projectionComplement_price
    _= _ :=by ring

theorem activeKernel_delta_price (p : Fin 4→ℂ) (r : ℝ) (nonneg : 0 ≤ r) (small : r ≤ 1)
    (bound : ∀i,‖p i‖ ≤ r) : ‖activeKernel p-activeKernel 0‖ ≤ variationBudget*r :=by
  have h:=sourceMatrix_positive_price activeTerms p r nonneg small bound
  rw [←sourceMatrix_delta] at h
  have delta : ‖activeKernel p-activeKernel 0‖ ≤ (termsPrice (positiveTerms activeTerms):ℝ)*r:=by
    simpa only [activeKernel] using h
  calc
    _ ≤ (termsPrice (positiveTerms activeTerms):ℝ)*r:=delta
    _ ≤ variationBudget*r:=by unfold variationBudget;nlinarith

theorem complement_delta_price (p : Fin 4→ℂ) (r : ℝ) (nonneg : 0 ≤ r) (small : r ≤ 1)
    (bound : ∀i,‖p i‖ ≤ r) : ‖complementKernel p-complementKernel 0‖ ≤ variationBudget*r :=by
  have positiveBudget : 0 ≤ variationBudget:=by linarith [variationBudget_ge_one]
  have factor : complementKernel p-complementKernel 0=
      complementProjection*(activeKernel p-activeKernel 0)*complementProjection :=by
    unfold complementKernel
    noncomm_ring
  rw [factor]
  calc
    _ ≤ (‖complementProjection‖*‖activeKernel p-activeKernel 0‖)*‖complementProjection‖:=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*(variationBudget*r))*1:=by
      gcongr
      · exact complementProjection_price
      · exact activeKernel_delta_price p r nonneg small bound
      · exact complementProjection_price
    _= _ :=by ring

theorem source_neumann_price (p : Fin 4→ℂ) (bound : ∀i,‖p i‖ ≤ sourceRadius) :
    ‖complementOriginInverse*(complementKernel p-complementKernel 0)‖ ≤ (1/4:ℝ) :=by
  have b:=inverseBudget_ge_one
  have k:=variationBudget_ge_one
  calc
    _ ≤ ‖complementOriginInverse‖*‖complementKernel p-complementKernel 0‖:=norm_mul_le _ _
    _ ≤ inverseBudget*(variationBudget*sourceRadius):=mul_le_mul complementOriginInverse_price
      (complement_delta_price p sourceRadius sourceRadius_pos.le sourceRadius_le_one bound)
      (norm_nonneg _) (by linarith)
    _=1/4:=by
      have bn : inverseBudget≠0:=by linarith
      have kn : variationBudget≠0:=by linarith
      unfold sourceRadius
      field_simp [bn,kn]

theorem sourceRadius_regular (p : Fin 4→ℂ) (bound : ∀i,‖p i‖ ≤ sourceRadius) : p∈complementRegular :=by
  have small : ‖-(complementOriginInverse*(complementKernel p-complementKernel 0))‖<1:=by
    rw [norm_neg]
    have h:=source_neumann_price p bound
    linarith
  have step : IsUnit (1+complementOriginInverse*(complementKernel p-complementKernel 0)):=by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one small
  have origin : IsUnit (complementKernel 0):=
    ⟨⟨complementKernel 0,complementOriginInverse,complementOriginInverse_right,complementOriginInverse_left⟩,rfl⟩
  have factor : complementKernel 0*(1+complementOriginInverse*(complementKernel p-complementKernel 0))=complementKernel p:=by
    calc
      _=complementKernel 0+(complementKernel 0*complementOriginInverse)*(complementKernel p-complementKernel 0):=by noncomm_ring
      _= _ :=by rw [complementOriginInverse_right,one_mul];abel
  have unit:=origin.mul step
  rw [factor] at unit
  exact (Matrix.isUnit_iff_isUnit_det _).mp unit

def controlledPoint (p : Fin 4→ℂ) (bound : ∀i,‖p i‖ ≤ sourceRadius) : complementRegular:=
  ⟨p,sourceRadius_regular p bound⟩

theorem complement_full_inverse_price (p : Fin 4→ℂ) (bound : ∀i,‖p i‖ ≤ sourceRadius) :
    ‖(complementKernel p)⁻¹‖ ≤ 2*inverseBudget :=by
  have unit:=sourceRadius_regular p bound
  have inverse : (complementKernel p)⁻¹=complementOriginInverse-
      (complementOriginInverse*(complementKernel p-complementKernel 0))*(complementKernel p)⁻¹ :=by
    have old:=complementOriginInverse_left
    have new:=Matrix.mul_nonsing_inv (complementKernel p) unit
    calc
      _=(complementOriginInverse*complementKernel 0)*(complementKernel p)⁻¹:=by rw [old,one_mul]
      _=complementOriginInverse*(complementKernel p*(complementKernel p)⁻¹)-
          (complementOriginInverse*(complementKernel p-complementKernel 0))*(complementKernel p)⁻¹:=by noncomm_ring
      _= _ :=by rw [new,mul_one]
  have triangle : ‖(complementKernel p)⁻¹‖ ≤ inverseBudget+(1/4:ℝ)*‖(complementKernel p)⁻¹‖:=by
    calc
      _=‖complementOriginInverse-(complementOriginInverse*(complementKernel p-complementKernel 0))*(complementKernel p)⁻¹‖:=congrArg norm inverse
      _ ≤ ‖complementOriginInverse‖+‖(complementOriginInverse*(complementKernel p-complementKernel 0))*(complementKernel p)⁻¹‖:=norm_sub_le _ _
      _ ≤ inverseBudget+(1/4:ℝ)*‖(complementKernel p)⁻¹‖:=by
        gcongr
        · exact complementOriginInverse_price
        · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (source_neumann_price p bound) (norm_nonneg _))
  have b:=inverseBudget_ge_one
  linarith

theorem complementGreen_price (p : Fin 4→ℂ) (bound : ∀i,‖p i‖ ≤ sourceRadius) :
    ‖complementGreen (controlledPoint p bound)‖ ≤ 2*inverseBudget :=by
  have positiveBudget : 0 ≤ inverseBudget:=by linarith [inverseBudget_ge_one]
  unfold complementGreen
  change ‖complementProjection*(complementKernel p)⁻¹*complementProjection‖ ≤ _
  calc
    _ ≤ (‖complementProjection‖*‖(complementKernel p)⁻¹‖)*‖complementProjection‖:=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*(2*inverseBudget))*1:=by
      gcongr
      · exact complementProjection_price
      · exact complement_full_inverse_price p bound
      · exact complementProjection_price
    _= _ :=by ring

theorem inversePrice_exact : termsPrice complementInverseTerms=(93620677/751740:ℚ) :=by decide +kernel
theorem variationPrice_exact : termsPrice (positiveTerms activeTerms)=(1359392/375:ℚ) :=by decide +kernel

theorem sourceRadius_exact : sourceRadius=(70475625/128324498346839:ℝ) :=by
  rw [sourceRadius,inverseBudget,variationBudget,inversePrice_exact,variationPrice_exact]
  norm_num

end LowEnergy.PreparationVacuumMixedControl
