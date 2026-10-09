import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceComplementInverse

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMixedEffective
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal
open scoped Matrix BigOperators Topology
attribute [local irreducible] activeKernel complementProjection

def complementRegular : Set (Fin 4→ℂ):={p | IsUnit (complementKernel p).det}
def complementOrigin : complementRegular:=⟨0,isUnit_iff_ne_zero.mpr complementOrigin_determinant⟩

private theorem sourceMatrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms) :=by
  induction terms with
  | nil=>exact continuous_const
  | cons a rest ih=>
    have term : Continuous a.matrix:=by
      apply continuous_matrix
      intro i j
      simp only [SourceTerm.matrix,Matrix.single_apply]
      split_ifs
      · unfold Powers.value;fun_prop
      · exact continuous_const
    exact term.add ih

theorem complementKernel_continuous : Continuous complementKernel :=by
  unfold complementKernel activeKernel
  exact ((continuous_const.matrix_mul (sourceMatrix_continuous activeTerms)).matrix_mul continuous_const).add continuous_const

theorem complementRegular_near_origin : ∀ᶠ p in 𝓝 (0:Fin 4→ℂ),p∈complementRegular :=by
  have near:=complementKernel_continuous.matrix_det.continuousAt.eventually_ne complementOrigin_determinant
  simpa only [complementRegular,Set.mem_ofPred_eq,isUnit_iff_ne_zero] using near

/-- Original complement Green, generated on the source nonempty local domain. -/
def complementGreen (p : complementRegular) : Matrix (Fin 289) (Fin 289) ℂ:=
  complementProjection*(complementKernel p.val)⁻¹*complementProjection

theorem complementKernel_right (p : Fin 4→ℂ) :
    complementKernel p*complementProjection=complementProjection*activeKernel p*complementProjection :=by
  unfold complementKernel
  simp only [add_mul,sub_mul,one_mul,mul_assoc,complementProjection_square,sub_self,add_zero]

theorem complementKernel_left (p : Fin 4→ℂ) :
    complementProjection*complementKernel p=complementProjection*activeKernel p*complementProjection :=by
  unfold complementKernel
  simp only [mul_add,mul_sub,mul_one,←mul_assoc,complementProjection_square,sub_self,add_zero]

theorem complementGreen_left_support (p : complementRegular) :
    complementProjection*complementGreen p=complementGreen p :=by
  unfold complementGreen
  simp only [←mul_assoc,complementProjection_square]

theorem complementGreen_right_support (p : complementRegular) :
    complementGreen p*complementProjection=complementGreen p :=by
  unfold complementGreen
  simp only [mul_assoc,complementProjection_square]

theorem complementGreen_left (p : complementRegular) :
    complementGreen p*activeKernel p.val*complementProjection=complementProjection :=by
  calc
    _=complementProjection*((complementKernel p.val)⁻¹*
      (complementProjection*activeKernel p.val*complementProjection)):=by unfold complementGreen;noncomm_ring
    _=complementProjection*((complementKernel p.val)⁻¹*(complementKernel p.val*complementProjection)):=by rw [complementKernel_right]
    _=complementProjection:=by
      rw [←mul_assoc (complementKernel p.val)⁻¹ (complementKernel p.val) complementProjection,Matrix.nonsing_inv_mul _ p.property,one_mul,complementProjection_square]

theorem complementGreen_right (p : complementRegular) :
    complementProjection*activeKernel p.val*complementGreen p=complementProjection :=by
  calc
    _=(complementProjection*activeKernel p.val*complementProjection)*(complementKernel p.val)⁻¹*complementProjection:=by unfold complementGreen;noncomm_ring
    _=(complementProjection*complementKernel p.val)*(complementKernel p.val)⁻¹*complementProjection:=by rw [complementKernel_left]
    _=complementProjection:=by
      rw [mul_assoc complementProjection,Matrix.mul_nonsing_inv _ p.property,mul_one,complementProjection_square]

theorem complementGreen_origin : complementGreen complementOrigin=complementInverse :=by
  have unit : IsUnit (complementKernel 0).det:=isUnit_iff_ne_zero.mpr complementOrigin_determinant
  have inverse : (complementKernel 0)⁻¹=complementOriginInverse:=by
    calc
      _=(complementOriginInverse*complementKernel 0)*(complementKernel 0)⁻¹:=by rw [complementOriginInverse_left,one_mul]
      _=complementOriginInverse:=by
        rw [mul_assoc,Matrix.mul_nonsing_inv _ unit,mul_one]
  change complementProjection*(complementKernel 0)⁻¹*complementProjection=complementInverse
  rw [inverse,complementOriginInverse,mul_add,mul_sub,mul_one,complementProjection_square,
    sub_self,add_zero,complementInverse_left_support,complementInverse_right_support]

def effectiveReader (p : complementRegular) : Matrix (Fin 289) (Fin 289) ℂ:=
  reflectedKernelFrame p.val-reflectedKernelFrame p.val*activeKernel p.val*complementGreen p

def effectiveKernel (p : complementRegular) : Matrix (Fin 289) (Fin 289) ℂ:=
  reflectedKernelFrame p.val*activeKernel p.val*kernelFrame p.val-
    reflectedKernelFrame p.val*activeKernel p.val*complementGreen p*activeKernel p.val*kernelFrame p.val

def effectiveFrame (p : complementRegular) : Matrix (Fin 289) (Fin 289) ℂ:=
  kernelFrame p.val-complementGreen p*activeKernel p.val*kernelFrame p.val

def nativeEffectiveFrame (p : complementRegular) : Matrix (Fin 289) (Fin 289) ℂ:=
  originalChange p.val*effectiveFrame p

theorem effectiveKernel_frame (p : complementRegular) :
    reflectedKernelFrame p.val*activeKernel p.val*effectiveFrame p=effectiveKernel p :=by
  unfold effectiveFrame effectiveKernel
  noncomm_ring

theorem effectiveReader_complement (p : complementRegular) :
    effectiveReader p*activeKernel p.val*complementProjection=0 :=by
  unfold effectiveReader
  calc
    _=reflectedKernelFrame p.val*activeKernel p.val*complementProjection-
      reflectedKernelFrame p.val*activeKernel p.val*(complementGreen p*activeKernel p.val*complementProjection):=by noncomm_ring
    _=0:=by rw [complementGreen_left,sub_self]

theorem effectiveKernel_generated (p : complementRegular) :
    effectiveReader p*activeKernel p.val*kernelFrame p.val=effectiveKernel p :=by
  unfold effectiveReader effectiveKernel
  noncomm_ring

theorem effectiveKernel_origin : effectiveKernel complementOrigin=0 :=by
  rw [←effectiveKernel_generated]
  change effectiveReader complementOrigin*activeKernel 0*kernelFrame 0=0
  rw [mul_assoc,sourceKernel_generated,mul_zero]

private theorem firstCorrection_certificate :
    fastNormalizeTerms (productTerms (projectionTerms complementFlag) (timeCorrectionTerms++spaceCorrectionTerms)++
      negativeTerms (timeCorrectionTerms++spaceCorrectionTerms))=[] :=by decide +kernel

theorem sourceFirstCorrection_supported (p : Fin 4→ℂ) :
    complementProjection*(jetFrame p-kernelFrame p)=jetFrame p-kernelFrame p :=by
  have h:=normalization_equal _ _ firstCorrection_certificate p
  rw [productTerms_value,projectionTerms_value] at h
  have correction : jetFrame p-kernelFrame p=sourceMatrix (timeCorrectionTerms++spaceCorrectionTerms) p :=by
    unfold jetFrame jetFrameTerms kernelFrame
    simp only [sourceMatrix_append]
    abel
  rw [correction]
  simpa only [complementProjection] using h

theorem effectiveKernel_firstJet (p : complementRegular) :
    effectiveReader p*activeKernel p.val*jetFrame p.val=effectiveKernel p :=by
  have annihilate : effectiveReader p*activeKernel p.val*(jetFrame p.val-kernelFrame p.val)=0 :=by
    rw [←sourceFirstCorrection_supported p.val,←mul_assoc,effectiveReader_complement,zero_mul]
  rw [mul_sub] at annihilate
  rw [←effectiveKernel_generated]
  exact sub_eq_zero.mp annihilate

/-- Exact source Schur correction to the previously generated two-mode principal tensor. -/
theorem effectiveKernel_principal_return (time space : ℂ) (regular : planeMomentum time space∈complementRegular) :
    effectiveKernel ⟨planeMomentum time space,regular⟩=sourcePrincipal time space-
      reflectedKernelFrame (planeMomentum time space)*activeKernel (planeMomentum time space)*
        complementGreen ⟨planeMomentum time space,regular⟩*
          (sourceMatrix quadraticTerms (planeMomentum time space)+sourceMatrix cubicTerms (planeMomentum time space)) :=by
  rw [←effectiveKernel_firstJet,effectiveReader,sub_mul,sub_mul]
  rw [sourcePrincipal_generated]
  rw [mul_assoc (reflectedKernelFrame _*activeKernel _*complementGreen _),sourceFrame_residual]

/-- The complementary field is returned by its own source equation. -/
theorem complement_response (p : complementRegular) (field forcing : Fin 289→ℂ)
    (supported : complementProjection*ᵥfield=field)
    (equation : complementProjection*ᵥ(activeKernel p.val*ᵥfield)=complementProjection*ᵥforcing) :
    field=complementGreen p*ᵥforcing :=by
  have returned:=congrArg (fun v=>complementGreen p*ᵥv) equation
  simp only [Matrix.mulVec_mulVec,←mul_assoc,complementGreen_right_support] at returned
  have recovered : (complementGreen p*activeKernel p.val)*ᵥfield=field :=by
    calc
      _=(complementGreen p*activeKernel p.val)*ᵥ(complementProjection*ᵥfield):=by rw [supported]
      _=(complementGreen p*activeKernel p.val*complementProjection)*ᵥfield:=by rw [Matrix.mulVec_mulVec]
      _=field:=by rw [complementGreen_left,supported]
  rw [recovered] at returned
  exact returned

end LowEnergy.PreparationVacuumMixedEffective
