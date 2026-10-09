import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceStaticActualPole
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceDressedPhotonCoupling

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalStaticSpatialCouplingReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumStaticPoleResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumWholeOrigin PreparationVacuumFullOriginResponse PreparationVacuumMixedPrincipal
open SourcePropagationConstrainedPoleReturn
open SourcePropagationNativeActionHessian CanonicalGradedSpatialSource
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCharacteristic Electromagnetic.CanonicalCoframe
open scoped Matrix BigOperators Topology Matrix.Norms.Operator

/-- All spatial directions use the original physical Fourier coordinates. -/
def sourceStaticSpatialMomentum (n : PhysicalMomentum) (kappa : ℝ) : Fin 4→ℂ :=
  ![0,Complex.I*((kappa*n 0:ℝ):ℂ),Complex.I*((kappa*n 1:ℝ):ℂ),Complex.I*((kappa*n 2:ℝ):ℂ)]

def sourceTemporalZeroTerms (terms : List SourceTerm) : List SourceTerm :=
  terms.filter (fun a=>decide (a.powers.temporal=0))

private theorem temporal_term_zero (a : SourceTerm) (n : PhysicalMomentum) (kappa : ℝ)
    (nonzero : a.powers.temporal≠0) : a.matrix (sourceStaticSpatialMomentum n kappa)=0 := by
  simp [SourceTerm.matrix,Powers.value,sourceStaticSpatialMomentum,nonzero]

theorem sourceTemporalZero_generated (terms : List SourceTerm) (n : PhysicalMomentum) (kappa : ℝ) :
    sourceMatrix (sourceTemporalZeroTerms terms) (sourceStaticSpatialMomentum n kappa)=
      sourceMatrix terms (sourceStaticSpatialMomentum n kappa) := by
  induction terms with
  | nil=>rfl
  | cons a rest ih=>
    simp only [sourceTemporalZeroTerms,List.filter_cons] at ih ⊢
    split_ifs with on
    · rw [sourceMatrix_cons,ih,sourceMatrix_cons]
    · rw [ih,sourceMatrix_cons,temporal_term_zero a n kappa (by simpa using on),zero_add]

private def spatialQuadraticTerms (axis : Fin 3) (terms : List SourceTerm) : List SourceTerm :=
  terms.map (fun a=>{a with powers:=
    ⟨0,if axis=0 then 2 else 0,if axis=1 then 2 else 0,if axis=2 then 2 else 0⟩})

private theorem spatial_certificate :
    fastNormalizeTerms (sourceTemporalZeroTerms fullLeadingTerms++negativeTerms
      (spatialQuadraticTerms 0 staticTensorTerms++spatialQuadraticTerms 1 staticTensorTerms++
        spatialQuadraticTerms 2 staticTensorTerms))=[] := by decide +kernel

private theorem spatial_quadratic (axis : Fin 3) (terms : List SourceTerm)
    (constant : ∀a∈terms,a.powers=⟨0,0,0,0⟩) (n : PhysicalMomentum) (kappa : ℝ) :
    sourceMatrix (spatialQuadraticTerms axis terms) (sourceStaticSpatialMomentum n kappa)=
      (-((kappa*n axis:ℝ):ℂ)^2) • sourceMatrix terms 0 := by
  induction terms with
  | nil=>simp [spatialQuadraticTerms,sourceMatrix]
  | cons a rest ih=>
    have pa:=constant a (by simp)
    have tail:=ih (fun b hb=>constant b (by simp [hb]))
    change {a with powers:=⟨0,if axis=0 then 2 else 0,if axis=1 then 2 else 0,if axis=2 then 2 else 0⟩}.matrix
      (sourceStaticSpatialMomentum n kappa)+sourceMatrix (spatialQuadraticTerms axis rest) (sourceStaticSpatialMomentum n kappa)=_
    rw [tail,sourceMatrix_cons,smul_add]
    congr 1
    fin_cases axis <;>
      norm_num [SourceTerm.matrix,Powers.value,pa,sourceStaticSpatialMomentum,
        Fin.ext_iff,Matrix.smul_single,mul_pow]
    all_goals
      ext i j
      simp [Matrix.single_apply,Matrix.neg_apply,mul_pow,Complex.I_sq]
      split_ifs
      all_goals simp_all
      all_goals ring

/-- The complete five-mode static tensor is spatially isotropic before any current or mode is selected. -/
theorem sourceStaticSpatialTensor_generated (n : PhysicalMomentum) (kappa : ℝ) :
    leadingTensor (sourceStaticSpatialMomentum n kappa)=
      (-((kappa^2*spatialSquare n:ℝ):ℂ)) • staticTensor := by
  have constant : ∀a∈staticTensorTerms,a.powers=⟨0,0,0,0⟩ := by
    have checked : staticTensorTerms.all (fun a=>decide (a.powers=⟨0,0,0,0⟩))=true := by decide +kernel
    intro a ha
    exact of_decide_eq_true (List.all_eq_true.mp checked a ha)
  have generated:=normalization_equal _ _ spatial_certificate (sourceStaticSpatialMomentum n kappa)
  rw [sourceTemporalZero_generated,sourceMatrix_append,sourceMatrix_append,
    spatial_quadratic 0 staticTensorTerms constant,spatial_quadratic 1 staticTensorTerms constant,
    spatial_quadratic 2 staticTensorTerms constant] at generated
  change sourceMatrix fullLeadingTerms (sourceStaticSpatialMomentum n kappa)=(-(kappa^2*spatialSquare n:ℝ):ℂ) • sourceMatrix staticTensorTerms 0
  rw [generated,←add_smul,←add_smul]
  congr 1
  simp [spatialSquare]
  ring

private theorem unit_coordinate (n : PhysicalMomentum) (unit : spatialSquare n=1) (j : Fin 3) : |n j| ≤ 1 := by
  have single : (n j)^2 ≤ ∑k : Fin 3,(n k)^2 :=
    Finset.single_le_sum (fun k _=>sq_nonneg (n k)) (Finset.mem_univ j)
  have value : (n j)^2 ≤ spatialSquare n := by
    simpa only [spatialSquare,Fin.sum_univ_three] using single
  rw [unit] at value
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (n j+1)],by nlinarith [sq_nonneg (n j-1)]⟩

theorem sourceStaticSpatialMomentum_price (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (kappa : ℝ) (nonneg : 0 ≤ kappa) (i : Fin 4) : ‖sourceStaticSpatialMomentum n kappa i‖ ≤ kappa := by
  have spatial (j : Fin 3) : ‖Complex.I*((kappa*n j:ℝ):ℂ)‖ ≤ kappa := by
    simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg nonneg]
    exact (mul_le_mul_of_nonneg_left (unit_coordinate n unit j) nonneg).trans_eq (mul_one kappa)
  fin_cases i
  · simpa [sourceStaticSpatialMomentum] using nonneg
  · simpa [sourceStaticSpatialMomentum] using spatial 0
  · simpa [sourceStaticSpatialMomentum] using spatial 1
  · simpa [sourceStaticSpatialMomentum] using spatial 2

def sourceStaticSpatialPoint (n : PhysicalMomentum) (unit : spatialSquare n=1) (kappa : staticDomain) : PreparationVacuumFullOriginResponse.complementRegular :=
  PreparationVacuumFullOriginResponse.controlledPoint (sourceStaticSpatialMomentum n kappa.val)
    (fun i=>(sourceStaticSpatialMomentum_price n unit kappa.val kappa.property.1.le i).trans
      (kappa.property.2.trans staticRadius_cap))

def sourceStaticSpatialKernel (n : PhysicalMomentum) (unit : spatialSquare n=1) (kappa : staticDomain) : Matrix (Fin 289) (Fin 289) ℂ :=
  (-(kappa.val:ℂ)^2)⁻¹ • effectiveKernel (sourceStaticSpatialPoint n unit kappa)+(1-fiveProjection)

attribute [local irreducible] effectiveKernel leadingTensor complementGreen staticTensor paddedStaticTensor sourceStaticSpatialKernel

theorem sourceStaticSpatialKernel_price (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) :
    ‖sourceStaticSpatialKernel n unit κ-paddedStaticTensor‖  ≤  effectiveErrorBudget*κ.val:=by
  have kn : κ.val≠0:=ne_of_gt κ.property.1
  have cn : (κ.val:ℂ)≠0:=by exact_mod_cast kn
  have factor : sourceStaticSpatialKernel n unit κ-paddedStaticTensor=
      (-(κ.val:ℂ)^2)⁻¹ • (effectiveKernel (sourceStaticSpatialPoint n unit κ)-leadingTensor (sourceStaticSpatialMomentum n κ.val)):=by
    conv_rhs=>rw [smul_sub,sourceStaticSpatialTensor_generated n,unit,mul_one,Complex.ofReal_pow,smul_smul,inv_mul_cancel₀ (neg_ne_zero.mpr (pow_ne_zero 2 cn)),one_smul]
    unfold sourceStaticSpatialKernel paddedStaticTensor
    abel
  have price:=effectiveKernel_leading_price (sourceStaticSpatialMomentum n κ.val) κ.val κ.property.1.le
    (κ.property.2.trans staticRadius_cap) (sourceStaticSpatialMomentum_price n unit κ.val κ.property.1.le)
  change ‖effectiveKernel (sourceStaticSpatialPoint n unit κ)-leadingTensor (sourceStaticSpatialMomentum n κ.val)‖  ≤  _ at price
  rw [factor,norm_smul,norm_inv,norm_neg,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos κ.property.1]
  calc
    _  ≤  (κ.val^2)⁻¹*(effectiveErrorBudget*κ.val^3):=mul_le_mul_of_nonneg_left price (by positivity)
    _=effectiveErrorBudget*κ.val:=by field_simp

theorem sourceStaticSpatialKernel_neumann_price (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) :
    ‖paddedStaticInverse*(sourceStaticSpatialKernel n unit κ-paddedStaticTensor)‖  ≤  (1/4:ℝ):=by
  have b:=staticInverseBudget_ge_one
  have e:=effectiveErrorBudget_nonneg
  have bn : staticInverseBudget≠0:=by linarith
  have en : (1+effectiveErrorBudget)≠0:=by linarith
  have cap : κ.val  ≤  (4*staticInverseBudget*(1+effectiveErrorBudget))⁻¹:=κ.property.2.trans (min_le_right _ _)
  calc
    _  ≤  ‖paddedStaticInverse‖*‖sourceStaticSpatialKernel n unit κ-paddedStaticTensor‖:=norm_mul_le _ _
    _  ≤  staticInverseBudget*(effectiveErrorBudget*κ.val):=
      mul_le_mul paddedStaticInverse_price (sourceStaticSpatialKernel_price n unit κ) (norm_nonneg _) (by linarith)
    _  ≤  staticInverseBudget*((1+effectiveErrorBudget)*(4*staticInverseBudget*(1+effectiveErrorBudget))⁻¹):=by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      calc
        _  ≤  (1+effectiveErrorBudget)*κ.val:=by nlinarith [κ.property.1]
        _  ≤  _:=mul_le_mul_of_nonneg_left cap (by linarith)
    _=1/4:=by field_simp [bn,en]

theorem sourceStaticSpatialKernel_isUnit (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) : IsUnit (sourceStaticSpatialKernel n unit κ):=by
  have small : ‖-(paddedStaticInverse*(sourceStaticSpatialKernel n unit κ-paddedStaticTensor))‖<1:=by
    rw [norm_neg]
    linarith [sourceStaticSpatialKernel_neumann_price n unit κ]
  have step : IsUnit (1+paddedStaticInverse*(sourceStaticSpatialKernel n unit κ-paddedStaticTensor)):=by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one small
  have origin : IsUnit paddedStaticTensor:=
    ⟨⟨paddedStaticTensor,paddedStaticInverse,paddedStaticInverse_right,paddedStaticInverse_left⟩,rfl⟩
  have factor : paddedStaticTensor*(1+paddedStaticInverse*(sourceStaticSpatialKernel n unit κ-paddedStaticTensor))=sourceStaticSpatialKernel n unit κ:=by
    calc
      _=paddedStaticTensor+(paddedStaticTensor*paddedStaticInverse)*(sourceStaticSpatialKernel n unit κ-paddedStaticTensor):=by noncomm_ring
      _= _:=by rw [paddedStaticInverse_right,one_mul];abel
  have unit:=origin.mul step
  rw [factor] at unit
  exact unit

theorem sourceStaticSpatialKernel_inverse_price (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) : ‖(sourceStaticSpatialKernel n unit κ)⁻¹‖  ≤  2*staticInverseBudget:=by
  have isunit:=(Matrix.isUnit_iff_isUnit_det _).mp (sourceStaticSpatialKernel_isUnit n unit κ)
  have inverse : (sourceStaticSpatialKernel n unit κ)⁻¹=paddedStaticInverse-
      (paddedStaticInverse*(sourceStaticSpatialKernel n unit κ-paddedStaticTensor))*(sourceStaticSpatialKernel n unit κ)⁻¹:=by
    calc
      _=(paddedStaticInverse*paddedStaticTensor)*(sourceStaticSpatialKernel n unit κ)⁻¹:=by rw [paddedStaticInverse_left,one_mul]
      _=paddedStaticInverse*(sourceStaticSpatialKernel n unit κ*(sourceStaticSpatialKernel n unit κ)⁻¹)-
          (paddedStaticInverse*(sourceStaticSpatialKernel n unit κ-paddedStaticTensor))*(sourceStaticSpatialKernel n unit κ)⁻¹:=by noncomm_ring
      _= _:=by rw [Matrix.mul_nonsing_inv _ isunit,mul_one]
  have triangle : ‖(sourceStaticSpatialKernel n unit κ)⁻¹‖  ≤  staticInverseBudget+(1/4:ℝ)*‖(sourceStaticSpatialKernel n unit κ)⁻¹‖:=by
    calc
      _=‖paddedStaticInverse-(paddedStaticInverse*(sourceStaticSpatialKernel n unit κ-paddedStaticTensor))*(sourceStaticSpatialKernel n unit κ)⁻¹‖:=congrArg norm inverse
      _  ≤  ‖paddedStaticInverse‖+‖(paddedStaticInverse*(sourceStaticSpatialKernel n unit κ-paddedStaticTensor))*(sourceStaticSpatialKernel n unit κ)⁻¹‖:=norm_sub_le _ _
      _  ≤  staticInverseBudget+(1/4:ℝ)*‖(sourceStaticSpatialKernel n unit κ)⁻¹‖:=by
        gcongr
        · exact paddedStaticInverse_price
        · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (sourceStaticSpatialKernel_neumann_price n unit κ) (norm_nonneg _))
  linarith [staticInverseBudget_ge_one]

theorem sourceStaticSpatialKernel_inverse_delta (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) :
    ‖(sourceStaticSpatialKernel n unit κ)⁻¹-paddedStaticInverse‖  ≤
      2*staticInverseBudget^2*effectiveErrorBudget*κ.val:=by
  have isunit:=(Matrix.isUnit_iff_isUnit_det _).mp (sourceStaticSpatialKernel_isUnit n unit κ)
  have difference : (sourceStaticSpatialKernel n unit κ)⁻¹-paddedStaticInverse=
      -(paddedStaticInverse*(sourceStaticSpatialKernel n unit κ-paddedStaticTensor)*(sourceStaticSpatialKernel n unit κ)⁻¹):=by
    calc
      _=(paddedStaticInverse*paddedStaticTensor)*(sourceStaticSpatialKernel n unit κ)⁻¹-
        paddedStaticInverse*(sourceStaticSpatialKernel n unit κ*(sourceStaticSpatialKernel n unit κ)⁻¹):=by
          rw [paddedStaticInverse_left,Matrix.mul_nonsing_inv _ isunit,one_mul,mul_one]
      _= _:=by noncomm_ring
  have b:=staticInverseBudget_ge_one
  have e:=effectiveErrorBudget_nonneg
  have kp:=κ.property.1.le
  rw [difference,norm_neg]
  calc
    _  ≤  (‖paddedStaticInverse‖*‖sourceStaticSpatialKernel n unit κ-paddedStaticTensor‖)*‖(sourceStaticSpatialKernel n unit κ)⁻¹‖:=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _  ≤  (staticInverseBudget*(effectiveErrorBudget*κ.val))*(2*staticInverseBudget):=by
      gcongr
      · exact paddedStaticInverse_price
      · exact sourceStaticSpatialKernel_price n unit κ
      · exact sourceStaticSpatialKernel_inverse_price n unit κ
    _= _:=by ring


end LowEnergy.PreparationPhysicalStaticSpatialCouplingReturn
