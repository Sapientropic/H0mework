import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceFullOriginCurrent

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumStaticPoleResponse
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal
open PreparationVacuumWholeOrigin PreparationVacuumFullOriginResponse
open PreparationVacuumMixedControl (termsPrice termsPrice_nonneg sourceMatrix_homogeneous_price)
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] activeKernel fullKernelFrame

def staticTensorTerms : List SourceTerm := [
  ⟨0,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,-25/54⟩⟩⟩,
  ⟨1,1,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,-12/335⟩⟩⟩,
  ⟨2,2,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,1/15⟩⟩⟩,
  ⟨2,3,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,-1/3⟩⟩⟩,
  ⟨3,2,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,-1/3⟩⟩⟩,
  ⟨3,3,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,1/15⟩⟩⟩,
  ⟨4,4,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,4/5⟩⟩⟩]
def staticInverseTerms : List SourceTerm := [
  ⟨0,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,-9/125⟩⟩⟩,
  ⟨1,1,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,-67/72⟩⟩⟩,
  ⟨2,2,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,-1/48⟩⟩⟩,
  ⟨2,3,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,-5/48⟩⟩⟩,
  ⟨3,2,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,-5/48⟩⟩⟩,
  ⟨3,3,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,-1/48⟩⟩⟩,
  ⟨4,4,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,1/24⟩⟩⟩]
def staticTensor : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix staticTensorTerms 0
def staticInverse : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix staticInverseTerms 0
def staticMomentum (κ : ℝ) : Fin 4→ℂ:=![0,Complex.I*(κ:ℂ),0,0]

def staticTerms (terms : List SourceTerm) : List SourceTerm:=terms.filter
  (fun a=>decide (a.powers.temporal=0 ∧ a.powers.second=0 ∧ a.powers.third=0))

private theorem staticTerm_zero (a : SourceTerm) (κ : ℝ)
    (off : ¬(a.powers.temporal=0 ∧ a.powers.second=0 ∧ a.powers.third=0)) : a.matrix (staticMomentum κ)=0:=by
  have vanished : a.powers.value (staticMomentum κ)=0:=by
    simp only [Powers.value,staticMomentum,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
    by_cases t : a.powers.temporal=0
    · by_cases s : a.powers.second=0
      · have u : a.powers.third≠0:=by tauto
        simp [u]
      · simp [s]
    · simp [t]
  simp [SourceTerm.matrix,vanished]

theorem staticTerms_generated (terms : List SourceTerm) (κ : ℝ) :
    sourceMatrix (staticTerms terms) (staticMomentum κ)=sourceMatrix terms (staticMomentum κ):=by
  induction terms with
  | nil=>rfl
  | cons a rest ih=>
    simp only [staticTerms,List.filter_cons] at ih ⊢
    split_ifs with on
    · rw [sourceMatrix_cons,ih,sourceMatrix_cons]
    · rw [ih,sourceMatrix_cons,staticTerm_zero a κ (by simpa using on),zero_add]

def quadraticTerms (terms : List SourceTerm) : List SourceTerm:=terms.map
  (fun a=>{a with powers:=⟨0,2,0,0⟩})

private theorem static_source_certificate : staticTerms fullLeadingTerms=quadraticTerms staticTensorTerms:=by decide +kernel

private theorem static_quadratic (terms : List SourceTerm) (constant : ∀a∈terms,a.powers=⟨0,0,0,0⟩) (κ : ℝ) :
    sourceMatrix (quadraticTerms terms) (staticMomentum κ)=(-(κ:ℂ)^2) • sourceMatrix terms 0:=by
  induction terms with
  | nil=>simp [quadraticTerms,sourceMatrix]
  | cons a rest ih=>
    have pa:=constant a (by simp)
    have tail:=ih (fun b hb=>constant b (by simp [hb]))
    change {a with powers:=⟨0,2,0,0⟩}.matrix (staticMomentum κ)+sourceMatrix (quadraticTerms rest) (staticMomentum κ)=_
    rw [tail,sourceMatrix_cons,smul_add]
    congr 1
    simp only [SourceTerm.matrix,Powers.value,pa,staticMomentum,Matrix.cons_val_zero,Matrix.cons_val_one,
      pow_zero,one_mul,mul_one,pow_two,Matrix.smul_single]
    congr 1
    rw [mul_mul_mul_comm Complex.I (κ:ℂ) Complex.I (κ:ℂ),Complex.I_mul_I]
    ring

theorem staticTensor_generated (κ : ℝ) : leadingTensor (staticMomentum κ)=(-(κ:ℂ)^2) • staticTensor:=by
  have constant : ∀a∈staticTensorTerms,a.powers=⟨0,0,0,0⟩:=by
    have checked : staticTensorTerms.all (fun a=>decide (a.powers=⟨0,0,0,0⟩))=true:=by decide +kernel
    intro a ha
    exact of_decide_eq_true (List.all_eq_true.mp checked a ha)
  change sourceMatrix fullLeadingTerms (staticMomentum κ)=_
  rw [←staticTerms_generated,static_source_certificate,static_quadratic _ constant]
  rfl

private theorem static_inverse_certificate :
    fastNormalizeTerms (productTerms staticInverseTerms staticTensorTerms++negativeTerms fiveProjectionTerms)=[]:=by decide +kernel

theorem staticInverse_left : staticInverse*staticTensor=fiveProjection:=by
  have h:=normalization_equal _ _ static_inverse_certificate (0:Fin 4→ℂ)
  simpa only [productTerms_value,staticInverse,staticTensor,fiveProjection] using h

private theorem static_support_certificate :
    fastNormalizeTerms (productTerms staticInverseTerms fiveProjectionTerms++negativeTerms staticInverseTerms)=[] ∧
    fastNormalizeTerms (productTerms fiveProjectionTerms staticTensorTerms++negativeTerms staticTensorTerms)=[] ∧
    fastNormalizeTerms (productTerms fiveProjectionTerms fiveProjectionTerms++negativeTerms fiveProjectionTerms)=[]:=by decide +kernel

theorem staticInverse_support : staticInverse*fiveProjection=staticInverse:=by
  have h:=normalization_equal _ _ static_support_certificate.1 (0:Fin 4→ℂ)
  simpa only [productTerms_value,staticInverse,fiveProjection] using h

theorem staticTensor_support : fiveProjection*staticTensor=staticTensor:=by
  have h:=normalization_equal _ _ static_support_certificate.2.1 (0:Fin 4→ℂ)
  simpa only [productTerms_value,staticTensor,fiveProjection] using h

theorem fiveProjection_square : fiveProjection*fiveProjection=fiveProjection:=by
  have h:=normalization_equal _ _ static_support_certificate.2.2 (0:Fin 4→ℂ)
  simpa only [productTerms_value,fiveProjection] using h

def paddedStaticTensor : Matrix (Fin 289) (Fin 289) ℂ:=staticTensor+(1-fiveProjection)
def paddedStaticInverse : Matrix (Fin 289) (Fin 289) ℂ:=staticInverse+(1-fiveProjection)

theorem paddedStaticInverse_left : paddedStaticInverse*paddedStaticTensor=1:=by
  unfold paddedStaticInverse paddedStaticTensor
  calc
    _=staticInverse*staticTensor+staticInverse-staticInverse*fiveProjection+
      staticTensor-fiveProjection*staticTensor+1-fiveProjection-fiveProjection+fiveProjection*fiveProjection:=by noncomm_ring
    _=1:=by rw [staticInverse_left,staticInverse_support,staticTensor_support,fiveProjection_square];abel

theorem paddedStaticInverse_right : paddedStaticTensor*paddedStaticInverse=1:=mul_eq_one_comm.mp paddedStaticInverse_left

def staticInverseBudget : ℝ:=1+(termsPrice staticInverseTerms:ℝ)

theorem staticInverseBudget_ge_one : 1 ≤ staticInverseBudget:=by
  have h : (0:ℝ) ≤ (termsPrice staticInverseTerms:ℝ):=by exact_mod_cast termsPrice_nonneg staticInverseTerms
  unfold staticInverseBudget;linarith

private theorem fiveProjection_diagonal : fiveProjection=Matrix.diagonal (fun i : Fin 289=>if i.val<5 then (1:ℂ) else 0):=by
  have checked : fastNormalizeTerms (fiveProjectionTerms++negativeTerms (projectionTerms (fun i=>decide (i.val<5))))=[]:=by decide +kernel
  have h:=normalization_equal _ _ checked (0:Fin 4→ℂ)
  simpa only [projectionTerms_value,projectionMatrix,decide_eq_true_eq,fiveProjection] using h

theorem paddedStaticInverse_price : ‖paddedStaticInverse‖ ≤ staticInverseBudget:=by
  have constant : ∀a∈staticInverseTerms,a.powers.total=0:=by
    intro a ha
    have checked : staticInverseTerms.all (fun a=>decide (a.powers.total=0))=true:=by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp checked a ha)
  have price : ‖staticInverse‖ ≤ (termsPrice staticInverseTerms:ℝ):=by
    simpa only [staticInverse,pow_zero,mul_one] using sourceMatrix_homogeneous_price staticInverseTerms 0 constant 0 0 le_rfl (fun i=>by simp)
  have outside : ‖(1:Matrix (Fin 289) (Fin 289) ℂ)-fiveProjection‖ ≤ 1:=by
    have identity : (1:Matrix (Fin 289) (Fin 289) ℂ)=Matrix.diagonal (fun _=>1):=rfl
    rw [identity,fiveProjection_diagonal,Matrix.diagonal_sub,Matrix.linfty_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro i
    split_ifs <;> norm_num
  calc
    _ ≤ ‖staticInverse‖+‖(1:Matrix (Fin 289) (Fin 289) ℂ)-fiveProjection‖:=norm_add_le _ _
    _ ≤ (termsPrice staticInverseTerms:ℝ)+1:=add_le_add price outside
    _=staticInverseBudget:=by unfold staticInverseBudget;ring

def staticRadius : ℝ:=min PreparationVacuumFullOriginResponse.sourceRadius
  (4*staticInverseBudget*(1+effectiveErrorBudget))⁻¹

theorem staticRadius_pos : 0<staticRadius:=by
  have b:=staticInverseBudget_ge_one
  have e:=effectiveErrorBudget_nonneg
  exact lt_min PreparationVacuumFullOriginResponse.sourceRadius_pos (by positivity)

theorem staticRadius_cap : staticRadius ≤ PreparationVacuumFullOriginResponse.sourceRadius:=min_le_left _ _

def staticDomain : Set ℝ:={κ | 0<κ ∧ κ ≤ staticRadius}

def staticWitness : staticDomain:=⟨staticRadius/2,by constructor <;> linarith [staticRadius_pos]⟩

theorem staticMomentum_price (κ : ℝ) (nonneg : 0 ≤ κ) (i : Fin 4) : ‖staticMomentum κ i‖ ≤ κ:=by
  fin_cases i <;> simp [staticMomentum,Complex.norm_real,abs_of_nonneg nonneg,nonneg]

def staticPoint (κ : staticDomain) : PreparationVacuumFullOriginResponse.complementRegular:=
  PreparationVacuumFullOriginResponse.controlledPoint (staticMomentum κ.val)
    (fun i=>(staticMomentum_price κ.val κ.property.1.le i).trans (κ.property.2.trans staticRadius_cap))

def normalizedKernel (κ : staticDomain) : Matrix (Fin 289) (Fin 289) ℂ:=
  (-(κ.val:ℂ)^2)⁻¹ • effectiveKernel (staticPoint κ)+(1-fiveProjection)

attribute [local irreducible] effectiveKernel leadingTensor complementGreen staticTensor paddedStaticTensor normalizedKernel

theorem normalizedKernel_price (κ : staticDomain) :
    ‖normalizedKernel κ-paddedStaticTensor‖ ≤ effectiveErrorBudget*κ.val:=by
  have kn : κ.val≠0:=ne_of_gt κ.property.1
  have cn : (κ.val:ℂ)≠0:=by exact_mod_cast kn
  have factor : normalizedKernel κ-paddedStaticTensor=
      (-(κ.val:ℂ)^2)⁻¹ • (effectiveKernel (staticPoint κ)-leadingTensor (staticMomentum κ.val)):=by
    conv_rhs=>rw [smul_sub,staticTensor_generated,smul_smul,inv_mul_cancel₀ (neg_ne_zero.mpr (pow_ne_zero 2 cn)),one_smul]
    unfold normalizedKernel paddedStaticTensor
    abel
  have price:=effectiveKernel_leading_price (staticMomentum κ.val) κ.val κ.property.1.le
    (κ.property.2.trans staticRadius_cap) (staticMomentum_price κ.val κ.property.1.le)
  change ‖effectiveKernel (staticPoint κ)-leadingTensor (staticMomentum κ.val)‖ ≤ _ at price
  rw [factor,norm_smul,norm_inv,norm_neg,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos κ.property.1]
  calc
    _ ≤ (κ.val^2)⁻¹*(effectiveErrorBudget*κ.val^3):=mul_le_mul_of_nonneg_left price (by positivity)
    _=effectiveErrorBudget*κ.val:=by field_simp

theorem normalizedKernel_neumann_price (κ : staticDomain) :
    ‖paddedStaticInverse*(normalizedKernel κ-paddedStaticTensor)‖ ≤ (1/4:ℝ):=by
  have b:=staticInverseBudget_ge_one
  have e:=effectiveErrorBudget_nonneg
  have bn : staticInverseBudget≠0:=by linarith
  have en : (1+effectiveErrorBudget)≠0:=by linarith
  have cap : κ.val ≤ (4*staticInverseBudget*(1+effectiveErrorBudget))⁻¹:=κ.property.2.trans (min_le_right _ _)
  calc
    _ ≤ ‖paddedStaticInverse‖*‖normalizedKernel κ-paddedStaticTensor‖:=norm_mul_le _ _
    _ ≤ staticInverseBudget*(effectiveErrorBudget*κ.val):=
      mul_le_mul paddedStaticInverse_price (normalizedKernel_price κ) (norm_nonneg _) (by linarith)
    _ ≤ staticInverseBudget*((1+effectiveErrorBudget)*(4*staticInverseBudget*(1+effectiveErrorBudget))⁻¹):=by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      calc
        _ ≤ (1+effectiveErrorBudget)*κ.val:=by nlinarith [κ.property.1]
        _ ≤ _:=mul_le_mul_of_nonneg_left cap (by linarith)
    _=1/4:=by field_simp [bn,en]

theorem normalizedKernel_isUnit (κ : staticDomain) : IsUnit (normalizedKernel κ):=by
  have small : ‖-(paddedStaticInverse*(normalizedKernel κ-paddedStaticTensor))‖<1:=by
    rw [norm_neg]
    linarith [normalizedKernel_neumann_price κ]
  have step : IsUnit (1+paddedStaticInverse*(normalizedKernel κ-paddedStaticTensor)):=by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one small
  have origin : IsUnit paddedStaticTensor:=
    ⟨⟨paddedStaticTensor,paddedStaticInverse,paddedStaticInverse_right,paddedStaticInverse_left⟩,rfl⟩
  have factor : paddedStaticTensor*(1+paddedStaticInverse*(normalizedKernel κ-paddedStaticTensor))=normalizedKernel κ:=by
    calc
      _=paddedStaticTensor+(paddedStaticTensor*paddedStaticInverse)*(normalizedKernel κ-paddedStaticTensor):=by noncomm_ring
      _= _:=by rw [paddedStaticInverse_right,one_mul];abel
  have unit:=origin.mul step
  rw [factor] at unit
  exact unit

theorem normalizedKernel_inverse_price (κ : staticDomain) : ‖(normalizedKernel κ)⁻¹‖ ≤ 2*staticInverseBudget:=by
  have unit:=(Matrix.isUnit_iff_isUnit_det _).mp (normalizedKernel_isUnit κ)
  have inverse : (normalizedKernel κ)⁻¹=paddedStaticInverse-
      (paddedStaticInverse*(normalizedKernel κ-paddedStaticTensor))*(normalizedKernel κ)⁻¹:=by
    calc
      _=(paddedStaticInverse*paddedStaticTensor)*(normalizedKernel κ)⁻¹:=by rw [paddedStaticInverse_left,one_mul]
      _=paddedStaticInverse*(normalizedKernel κ*(normalizedKernel κ)⁻¹)-
          (paddedStaticInverse*(normalizedKernel κ-paddedStaticTensor))*(normalizedKernel κ)⁻¹:=by noncomm_ring
      _= _:=by rw [Matrix.mul_nonsing_inv _ unit,mul_one]
  have triangle : ‖(normalizedKernel κ)⁻¹‖ ≤ staticInverseBudget+(1/4:ℝ)*‖(normalizedKernel κ)⁻¹‖:=by
    calc
      _=‖paddedStaticInverse-(paddedStaticInverse*(normalizedKernel κ-paddedStaticTensor))*(normalizedKernel κ)⁻¹‖:=congrArg norm inverse
      _ ≤ ‖paddedStaticInverse‖+‖(paddedStaticInverse*(normalizedKernel κ-paddedStaticTensor))*(normalizedKernel κ)⁻¹‖:=norm_sub_le _ _
      _ ≤ staticInverseBudget+(1/4:ℝ)*‖(normalizedKernel κ)⁻¹‖:=by
        gcongr
        · exact paddedStaticInverse_price
        · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (normalizedKernel_neumann_price κ) (norm_nonneg _))
  linarith [staticInverseBudget_ge_one]

theorem normalizedKernel_inverse_delta (κ : staticDomain) :
    ‖(normalizedKernel κ)⁻¹-paddedStaticInverse‖ ≤
      2*staticInverseBudget^2*effectiveErrorBudget*κ.val:=by
  have unit:=(Matrix.isUnit_iff_isUnit_det _).mp (normalizedKernel_isUnit κ)
  have difference : (normalizedKernel κ)⁻¹-paddedStaticInverse=
      -(paddedStaticInverse*(normalizedKernel κ-paddedStaticTensor)*(normalizedKernel κ)⁻¹):=by
    calc
      _=(paddedStaticInverse*paddedStaticTensor)*(normalizedKernel κ)⁻¹-
        paddedStaticInverse*(normalizedKernel κ*(normalizedKernel κ)⁻¹):=by
          rw [paddedStaticInverse_left,Matrix.mul_nonsing_inv _ unit,one_mul,mul_one]
      _= _:=by noncomm_ring
  have b:=staticInverseBudget_ge_one
  have e:=effectiveErrorBudget_nonneg
  have kp:=κ.property.1.le
  rw [difference,norm_neg]
  calc
    _ ≤ (‖paddedStaticInverse‖*‖normalizedKernel κ-paddedStaticTensor‖)*‖(normalizedKernel κ)⁻¹‖:=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (staticInverseBudget*(effectiveErrorBudget*κ.val))*(2*staticInverseBudget):=by
      gcongr
      · exact paddedStaticInverse_price
      · exact normalizedKernel_price κ
      · exact normalizedKernel_inverse_price κ
    _= _:=by ring

end LowEnergy.PreparationVacuumStaticPoleResponse
