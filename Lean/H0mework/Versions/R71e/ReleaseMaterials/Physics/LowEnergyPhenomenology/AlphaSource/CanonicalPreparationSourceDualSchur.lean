import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceWholeOriginFrame

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWholeOrigin.Dual
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedEffective
open scoped Matrix BigOperators Topology

def blockIndices : List (Fin 289) := [88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111]
def complementIndices : List (Fin 289) := [88,90,91,92,93,94,96,97,98,99,100,102,103,104,105,106,107,108,109,110,111]
def blockFlag (i : Fin 289) : Bool:=blockIndices.contains i
def complementFlag (i : Fin 289) : Bool:=complementIndices.contains i
def blockProjection : Matrix (Fin 289) (Fin 289) ℂ:=projectionMatrix blockFlag
def complementProjection : Matrix (Fin 289) (Fin 289) ℂ:=projectionMatrix complementFlag

def complementOriginTerms : List SourceTerm:=selectedRows complementFlag
  (columnTerms complementFlag (originTerms activeTerms))

private def complementInverseTermsAtoms : List SourceAtom := [
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(175/5184:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-125/5184:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(25/324:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(25/216:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(125/5184:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(25/1296:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-25/432:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-25/648:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(35/432:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/216:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/324:ℚ)⟩⟩)]
private def complementInverseTermsCodes : List ℕ := [
  280720,280765,280787,280831,287102,290293,293437,293480,293503,293547,296672,299795,299839,299860,299905,306242,309433,312511,
  312555,312577,312620,315812,319000,319048,319067,319114,325382,328575,328620,328643,331720,331760,331786,331827,334952,338075,
  338122,338140,338188,341292,341338,341361,344522,347651,347697,347720,350794,350835,350860,350900,354092]
def complementInverseTerms : List SourceTerm := decodeTerms complementInverseTermsAtoms complementInverseTermsCodes

def complementInverse : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix complementInverseTerms 0

theorem complementOrigin_generated : sourceMatrix complementOriginTerms 0=
    complementProjection*activeKernel 0*complementProjection :=by
  rw [complementOriginTerms,selectedRows_generated,columnTerms_value,originTerms_generated]
  simp only [mul_assoc]
  rfl

private theorem inverse_left_certificate :
    fastNormalizeTerms (productTerms complementInverseTerms complementOriginTerms++
      negativeTerms (projectionTerms complementFlag))=[] :=by decide +kernel
private theorem inverse_right_certificate :
    fastNormalizeTerms (productTerms complementOriginTerms complementInverseTerms++
      negativeTerms (projectionTerms complementFlag))=[] :=by decide +kernel
private theorem inverse_left_support_certificate :
    fastNormalizeTerms (productTerms (projectionTerms complementFlag) complementInverseTerms++
      negativeTerms complementInverseTerms)=[] :=by decide +kernel
private theorem inverse_right_support_certificate :
    fastNormalizeTerms (productTerms complementInverseTerms (projectionTerms complementFlag)++
      negativeTerms complementInverseTerms)=[] :=by decide +kernel

theorem complementInverse_left : complementInverse*(complementProjection*activeKernel 0*complementProjection)=complementProjection :=by
  have h:=normalization_equal _ _ inverse_left_certificate 0
  rw [productTerms_value,complementOrigin_generated,projectionTerms_value] at h
  exact h

theorem complementInverse_right : (complementProjection*activeKernel 0*complementProjection)*complementInverse=complementProjection :=by
  have h:=normalization_equal _ _ inverse_right_certificate 0
  rw [productTerms_value,complementOrigin_generated,projectionTerms_value] at h
  exact h

theorem complementInverse_left_support : complementProjection*complementInverse=complementInverse :=by
  have h:=normalization_equal _ _ inverse_left_support_certificate 0
  rw [productTerms_value,projectionTerms_value] at h
  exact h

theorem complementInverse_right_support : complementInverse*complementProjection=complementInverse :=by
  have h:=normalization_equal _ _ inverse_right_support_certificate 0
  rw [productTerms_value,projectionTerms_value] at h
  exact h

theorem complementProjection_square : complementProjection*complementProjection=complementProjection :=by
  rw [complementProjection,projectionMatrix,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> norm_num

def complementKernel (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  complementProjection*activeKernel p*complementProjection+(1-complementProjection)
def complementOriginInverse : Matrix (Fin 289) (Fin 289) ℂ:=complementInverse+(1-complementProjection)

private theorem padded_inverse {R : Type*} [Ring R] (K B Q : R)
    (pair : K*B=Q) (support : K*Q=K) (read : Q*B=B) (square : Q*Q=Q) :
    (K+(1-Q))*(B+(1-Q))=1 :=by
  calc
    _=K*B+K-K*Q+B-Q*B+1-Q-Q+Q*Q:=by noncomm_ring
    _=1:=by rw [pair,support,read,square];noncomm_ring

theorem complementOriginInverse_right : complementKernel 0*complementOriginInverse=1 :=by
  apply padded_inverse _ _ _ complementInverse_right _ complementInverse_left_support complementProjection_square
  rw [mul_assoc,complementProjection_square]

theorem complementOriginInverse_left : complementOriginInverse*complementKernel 0=1 :=by
  apply padded_inverse _ _ _ complementInverse_left complementInverse_right_support _ complementProjection_square
  simp only [←mul_assoc,complementProjection_square]

theorem complementOrigin_determinant : (complementKernel 0).det≠0 :=by
  have h:=congrArg Matrix.det complementOriginInverse_right
  rw [Matrix.det_mul,Matrix.det_one] at h
  intro zero
  rw [zero,zero_mul] at h
  exact zero_ne_one h


attribute [local irreducible] activeKernel complementProjection complementInverse complementOriginInverse complementKernel dualKernelFrame

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
  dualKernelFrame.transpose-dualKernelFrame.transpose*activeKernel p.val*complementGreen p

def effectiveKernel (p : complementRegular) : Matrix (Fin 289) (Fin 289) ℂ:=
  dualKernelFrame.transpose*activeKernel p.val*dualKernelFrame-
    dualKernelFrame.transpose*activeKernel p.val*complementGreen p*activeKernel p.val*dualKernelFrame

def effectiveFrame (p : complementRegular) : Matrix (Fin 289) (Fin 289) ℂ:=
  dualKernelFrame-complementGreen p*activeKernel p.val*dualKernelFrame

def nativeEffectiveFrame (p : complementRegular) : Matrix (Fin 289) (Fin 289) ℂ:=
  originalChange p.val*effectiveFrame p

theorem effectiveKernel_frame (p : complementRegular) :
    dualKernelFrame.transpose*activeKernel p.val*effectiveFrame p=effectiveKernel p :=by
  unfold effectiveFrame effectiveKernel
  noncomm_ring

theorem effectiveReader_complement (p : complementRegular) :
    effectiveReader p*activeKernel p.val*complementProjection=0 :=by
  unfold effectiveReader
  calc
    _=dualKernelFrame.transpose*activeKernel p.val*complementProjection-
      dualKernelFrame.transpose*activeKernel p.val*(complementGreen p*activeKernel p.val*complementProjection):=by noncomm_ring
    _=0:=by rw [complementGreen_left,sub_self]

theorem effectiveKernel_generated (p : complementRegular) :
    effectiveReader p*activeKernel p.val*dualKernelFrame=effectiveKernel p :=by
  unfold effectiveReader effectiveKernel
  noncomm_ring

theorem effectiveKernel_origin : effectiveKernel complementOrigin=0 :=by
  rw [←effectiveKernel_generated]
  change effectiveReader complementOrigin*activeKernel 0*dualKernelFrame=0
  rw [mul_assoc,dual_origin_kernel,mul_zero]


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


private def dualLeadingTermsAtoms : List SourceAtom := [
  (⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(1/15:ℚ)⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(1/15:ℚ)⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(1/15:ℚ)⟩⟩),
  (⟨1,0,0,1⟩,⟨⟨(10/9:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(25/162:ℚ)⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(-1/3:ℚ)⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(-1/3:ℚ)⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(-1/3:ℚ)⟩⟩),
  (⟨1,0,0,1⟩,⟨⟨(-10/3:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-25/162:ℚ)⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,-4⟩,⟨0,0⟩⟩),
  (⟨1,0,0,1⟩,⟨⟨(50/9:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(145/162:ℚ)⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,4⟩,⟨0,0⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(4/5:ℚ)⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(4/5:ℚ)⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(4/5:ℚ)⟩⟩),
  (⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(50/27:ℚ)⟩⟩)]
private def dualLeadingTermsCodes : List ℕ := [
  0,1,2,3,4,23,24,25,26,27,46,5207,5208,5209,5210,5211,5220,5221,
  5222,5231,5232,5251,10417,10432,10454,10455,10456,10457]
def dualLeadingTerms : List SourceTerm := decodeTerms dualLeadingTermsAtoms dualLeadingTermsCodes


def leadingTensor (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix dualLeadingTerms p

private theorem dual_constant (p : Fin 4→ℂ) : sourceMatrix dualKernelTerms p=dualKernelFrame:=by unfold dualKernelFrame;rfl
private theorem inverse_constant (p : Fin 4→ℂ) : sourceMatrix complementInverseTerms p=complementInverse:=by unfold complementInverse;rfl
private theorem dual_reflected (p : Fin 4→ℂ) : sourceMatrix (reflectedTerms dualKernelTerms) p=dualKernelFrame.transpose:=by
  rw [reflectedTerms_value,dual_constant]

private theorem leading_certificate :
    fastNormalizeTerms ((productTerms (productTerms (reflectedTerms dualKernelTerms) activeTerms) dualKernelTerms++
      negativeTerms (productTerms (productTerms (productTerms (productTerms (reflectedTerms dualKernelTerms) activeTerms)
        complementInverseTerms) activeTerms) dualKernelTerms))++negativeTerms dualLeadingTerms)=[]:=by decide +kernel

theorem leadingTensor_generated (p : Fin 4→ℂ) :
    leadingTensor p=dualKernelFrame.transpose*activeKernel p*dualKernelFrame-
      dualKernelFrame.transpose*activeKernel p*complementInverse*activeKernel p*dualKernelFrame:=by
  have h:=normalization_equal _ _ leading_certificate p
  simp only [sourceMatrix_append,negativeTerms_value,productTerms_value,dual_constant,inverse_constant,dual_reflected] at h
  simpa only [leadingTensor,activeKernel,sub_eq_add_neg] using h.symm

theorem effectiveKernel_complete_return (p : complementRegular) :
    effectiveKernel p=leadingTensor p.val-
      dualKernelFrame.transpose*activeKernel p.val*(complementGreen p-complementInverse)*activeKernel p.val*dualKernelFrame:=by
  rw [leadingTensor_generated,effectiveKernel]
  noncomm_ring

theorem leadingTensor_time_mixing (p : Fin 4→ℂ) :
    leadingTensor p 0 2=-4*rootTwo*p 0 ∧ leadingTensor p 1 2=4*rootTwo*p 0 ∧
    leadingTensor p 2 0=4*rootTwo*p 0 ∧ leadingTensor p 2 1=-4*rootTwo*p 0:=by
  norm_num [leadingTensor,dualLeadingTerms,dualLeadingTermsAtoms,dualLeadingTermsCodes,
    decodeTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,Powers.value,coefficientValue,Fin.ext_iff]



theorem effectiveKernel_delta_return (p : complementRegular) :
    effectiveKernel p=leadingTensor p.val-
      dualKernelFrame.transpose*(activeKernel p.val-activeKernel 0)*(complementGreen p-complementInverse)*
        (activeKernel p.val-activeKernel 0)*dualKernelFrame:=by
  have leftZero : dualKernelFrame.transpose*activeKernel 0=0:=by
    have h:=congrArg Matrix.transpose dual_origin_kernel
    have symmetric : (activeKernel 0).transpose=activeKernel 0:=by
      simpa only [neg_zero] using activeKernel_reflect (0:Fin 4→ℂ)
    rw [Matrix.transpose_mul,Matrix.transpose_zero,symmetric] at h
    exact h
  have leftDelta : dualKernelFrame.transpose*(activeKernel p.val-activeKernel 0)=
      dualKernelFrame.transpose*activeKernel p.val:=by rw [mul_sub,leftZero,sub_zero]
  have rightDelta : (activeKernel p.val-activeKernel 0)*dualKernelFrame=activeKernel p.val*dualKernelFrame:=by
    rw [sub_mul,dual_origin_kernel,sub_zero]
  rw [effectiveKernel_complete_return,leftDelta]
  simp only [mul_assoc]
  rw [rightDelta]


end LowEnergy.PreparationVacuumWholeOrigin.Dual
