import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceFullOriginInverse

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFullOriginResponse
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedEffective
open PreparationVacuumWholeOrigin
open scoped Matrix BigOperators Topology

def dualInjectionTerms : List SourceTerm := [⟨0,2,⟨0,0,0,0⟩,1⟩,⟨1,3,⟨0,0,0,0⟩,1⟩,⟨2,4,⟨0,0,0,0⟩,1⟩]
def dualInjection : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix dualInjectionTerms 0
def fullKernelTerms : List SourceTerm:=kernelTerms++productTerms dualKernelTerms dualInjectionTerms
def fullKernelFrame : Matrix (Fin 289) (Fin 289) ℂ:=kernelFrame 0+dualKernelFrame*dualInjection

theorem fullKernel_generated (p : Fin 4→ℂ) : sourceMatrix fullKernelTerms p=fullKernelFrame:=by
  rw [fullKernelTerms,sourceMatrix_append,productTerms_value]
  rfl

theorem fullKernel_origin : activeKernel 0*fullKernelFrame=0:=by
  rw [fullKernelFrame,mul_add,←mul_assoc,sourceKernel_generated,dual_origin_kernel,zero_mul,zero_add]

attribute [local irreducible] activeKernel fullComplementProjection fullInverse originInverse complementKernel fullKernelFrame

def complementRegular : Set (Fin 4→ℂ):={p | IsUnit (complementKernel p).det}
def complementOrigin : complementRegular:=⟨0,isUnit_iff_ne_zero.mpr origin_determinant⟩

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
  have near:=complementKernel_continuous.matrix_det.continuousAt.eventually_ne origin_determinant
  simpa only [complementRegular,Set.mem_ofPred_eq,isUnit_iff_ne_zero] using near

/-- Original complement Green, generated on the source nonempty local domain. -/
def complementGreen (p : complementRegular) : Matrix (Fin 289) (Fin 289) ℂ:=
  fullComplementProjection*(complementKernel p.val)⁻¹*fullComplementProjection

theorem complementKernel_right (p : Fin 4→ℂ) :
    complementKernel p*fullComplementProjection=fullComplementProjection*activeKernel p*fullComplementProjection :=by
  unfold complementKernel
  simp only [add_mul,sub_mul,one_mul,mul_assoc,fullProjection_square,sub_self,add_zero]

theorem complementKernel_left (p : Fin 4→ℂ) :
    fullComplementProjection*complementKernel p=fullComplementProjection*activeKernel p*fullComplementProjection :=by
  unfold complementKernel
  simp only [mul_add,mul_sub,mul_one,←mul_assoc,fullProjection_square,sub_self,add_zero]

theorem complementGreen_left_support (p : complementRegular) :
    fullComplementProjection*complementGreen p=complementGreen p :=by
  unfold complementGreen
  simp only [←mul_assoc,fullProjection_square]

theorem complementGreen_right_support (p : complementRegular) :
    complementGreen p*fullComplementProjection=complementGreen p :=by
  unfold complementGreen
  simp only [mul_assoc,fullProjection_square]

theorem complementGreen_left (p : complementRegular) :
    complementGreen p*activeKernel p.val*fullComplementProjection=fullComplementProjection :=by
  calc
    _=fullComplementProjection*((complementKernel p.val)⁻¹*
      (fullComplementProjection*activeKernel p.val*fullComplementProjection)):=by unfold complementGreen;noncomm_ring
    _=fullComplementProjection*((complementKernel p.val)⁻¹*(complementKernel p.val*fullComplementProjection)):=by rw [complementKernel_right]
    _=fullComplementProjection:=by
      rw [←mul_assoc (complementKernel p.val)⁻¹ (complementKernel p.val) fullComplementProjection,Matrix.nonsing_inv_mul _ p.property,one_mul,fullProjection_square]

theorem complementGreen_right (p : complementRegular) :
    fullComplementProjection*activeKernel p.val*complementGreen p=fullComplementProjection :=by
  calc
    _=(fullComplementProjection*activeKernel p.val*fullComplementProjection)*(complementKernel p.val)⁻¹*fullComplementProjection:=by unfold complementGreen;noncomm_ring
    _=(fullComplementProjection*complementKernel p.val)*(complementKernel p.val)⁻¹*fullComplementProjection:=by rw [complementKernel_left]
    _=fullComplementProjection:=by
      rw [mul_assoc fullComplementProjection,Matrix.mul_nonsing_inv _ p.property,mul_one,fullProjection_square]

theorem complementGreen_origin : complementGreen complementOrigin=fullInverse :=by
  have unit : IsUnit (complementKernel 0).det:=isUnit_iff_ne_zero.mpr origin_determinant
  have inverse : (complementKernel 0)⁻¹=originInverse:=by
    calc
      _=(originInverse*complementKernel 0)*(complementKernel 0)⁻¹:=by rw [originInverse_left,one_mul]
      _=originInverse:=by
        rw [mul_assoc,Matrix.mul_nonsing_inv _ unit,mul_one]
  change fullComplementProjection*(complementKernel 0)⁻¹*fullComplementProjection=fullInverse
  rw [inverse,originInverse,mul_add,mul_sub,mul_one,fullProjection_square,
    sub_self,add_zero,fullInverse_left_support,fullInverse_right_support]

def effectiveReader (p : complementRegular) : Matrix (Fin 289) (Fin 289) ℂ:=
  fullKernelFrame.transpose-fullKernelFrame.transpose*activeKernel p.val*complementGreen p

def effectiveKernel (p : complementRegular) : Matrix (Fin 289) (Fin 289) ℂ:=
  fullKernelFrame.transpose*activeKernel p.val*fullKernelFrame-
    fullKernelFrame.transpose*activeKernel p.val*complementGreen p*activeKernel p.val*fullKernelFrame

def effectiveFrame (p : complementRegular) : Matrix (Fin 289) (Fin 289) ℂ:=
  fullKernelFrame-complementGreen p*activeKernel p.val*fullKernelFrame

def nativeEffectiveFrame (p : complementRegular) : Matrix (Fin 289) (Fin 289) ℂ:=
  originalChange p.val*effectiveFrame p

theorem effectiveKernel_frame (p : complementRegular) :
    fullKernelFrame.transpose*activeKernel p.val*effectiveFrame p=effectiveKernel p :=by
  unfold effectiveFrame effectiveKernel
  noncomm_ring

theorem effectiveReader_complement (p : complementRegular) :
    effectiveReader p*activeKernel p.val*fullComplementProjection=0 :=by
  unfold effectiveReader
  calc
    _=fullKernelFrame.transpose*activeKernel p.val*fullComplementProjection-
      fullKernelFrame.transpose*activeKernel p.val*(complementGreen p*activeKernel p.val*fullComplementProjection):=by noncomm_ring
    _=0:=by rw [complementGreen_left,sub_self]

theorem effectiveKernel_generated (p : complementRegular) :
    effectiveReader p*activeKernel p.val*fullKernelFrame=effectiveKernel p :=by
  unfold effectiveReader effectiveKernel
  noncomm_ring

theorem effectiveKernel_origin : effectiveKernel complementOrigin=0 :=by
  rw [←effectiveKernel_generated]
  change effectiveReader complementOrigin*activeKernel 0*fullKernelFrame=0
  rw [mul_assoc,fullKernel_origin,mul_zero]


/-- The complementary field is returned by its own source equation. -/
theorem complement_response (p : complementRegular) (field forcing : Fin 289→ℂ)
    (supported : fullComplementProjection*ᵥfield=field)
    (equation : fullComplementProjection*ᵥ(activeKernel p.val*ᵥfield)=fullComplementProjection*ᵥforcing) :
    field=complementGreen p*ᵥforcing :=by
  have returned:=congrArg (fun v=>complementGreen p*ᵥv) equation
  simp only [Matrix.mulVec_mulVec,←mul_assoc,complementGreen_right_support] at returned
  have recovered : (complementGreen p*activeKernel p.val)*ᵥfield=field :=by
    calc
      _=(complementGreen p*activeKernel p.val)*ᵥ(fullComplementProjection*ᵥfield):=by rw [supported]
      _=(complementGreen p*activeKernel p.val*fullComplementProjection)*ᵥfield:=by rw [Matrix.mulVec_mulVec]
      _=field:=by rw [complementGreen_left,supported]
  rw [recovered] at returned
  exact returned



def frozenTensor (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  fullKernelFrame.transpose*activeKernel p*fullKernelFrame-
    fullKernelFrame.transpose*activeKernel p*fullInverse*activeKernel p*fullKernelFrame

theorem effectiveKernel_complete_return (p : complementRegular) :
    effectiveKernel p=frozenTensor p.val-
      fullKernelFrame.transpose*(activeKernel p.val-activeKernel 0)*(complementGreen p-fullInverse)*
        (activeKernel p.val-activeKernel 0)*fullKernelFrame:=by
  have leftZero : fullKernelFrame.transpose*activeKernel 0=0:=by
    have h:=congrArg Matrix.transpose fullKernel_origin
    have symmetric : (activeKernel 0).transpose=activeKernel 0:=by
      simpa only [neg_zero] using activeKernel_reflect (0:Fin 4→ℂ)
    rw [Matrix.transpose_mul,Matrix.transpose_zero,symmetric] at h
    exact h
  have leftDelta : fullKernelFrame.transpose*(activeKernel p.val-activeKernel 0)=
      fullKernelFrame.transpose*activeKernel p.val:=by rw [mul_sub,leftZero,sub_zero]
  have rightDelta : (activeKernel p.val-activeKernel 0)*fullKernelFrame=activeKernel p.val*fullKernelFrame:=by
    rw [sub_mul,fullKernel_origin,sub_zero]
  rw [leftDelta]
  simp only [mul_assoc]
  rw [rightDelta]
  unfold effectiveKernel frozenTensor
  noncomm_ring


def fullInverseTerms : List SourceTerm:=(componentInverseTerms 0++componentInverseTerms 1)++componentInverseTerms 2

theorem fullInverse_generated (p : Fin 4→ℂ) : sourceMatrix fullInverseTerms p=fullInverse:=by
  have checked : fullInverseTerms.all (fun a=>decide (a.powers.total=0))=true:=by decide +kernel
  have degree : ∀a∈fullInverseTerms,a.powers.total=0:=by
    intro a ha
    exact of_decide_eq_true (List.all_eq_true.mp checked a ha)
  have scaled:=PreparationVacuumMixedControl.sourceMatrix_homogeneous fullInverseTerms 0 degree (0:ℂ) p
  have constant : sourceMatrix fullInverseTerms p=sourceMatrix fullInverseTerms 0:=by
    simpa only [zero_smul,pow_zero,one_smul] using scaled.symm
  calc
    _=sourceMatrix fullInverseTerms 0:=constant
    _=(sourceMatrix (componentInverseTerms 0) 0+sourceMatrix (componentInverseTerms 1) 0)+
        sourceMatrix (componentInverseTerms 2) 0:=
      (sourceMatrix_append (componentInverseTerms 0++componentInverseTerms 1) (componentInverseTerms 2) 0).trans
        (congrArg (fun M=>M+sourceMatrix (componentInverseTerms 2) 0)
          (sourceMatrix_append (componentInverseTerms 0) (componentInverseTerms 1) 0))
    _=fullInverse:=by
      change componentInverse 0+componentInverse 1+componentInverse 2=fullInverse
      rw [fullInverse,Fin.sum_univ_three]

private def fullLeadingTermsAtoms : List SourceAtom := [
  (⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(-25/54:ℚ)⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(-25/54:ℚ)⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(-25/54:ℚ)⟩⟩),
  (⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-25/18:ℚ)⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(-12/335:ℚ)⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(-12/335:ℚ)⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(-12/335:ℚ)⟩⟩),
  (⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(10/99:ℚ)⟩⟩),
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
private def fullLeadingTermsCodes : List ℕ := [
  0,1,2,3,7544,7545,7546,7547,15088,15089,15090,15091,15092,15119,15120,15121,15122,15123,
  15150,22607,22608,22609,22610,22611,22628,22629,22630,22639,22640,22667,30129,30152,30182,30183,30184,30185]
def fullLeadingTerms : List SourceTerm := decodeTerms fullLeadingTermsAtoms fullLeadingTermsCodes

private def fullHigherTermsAtoms : List SourceAtom := [
  (⟨0,0,0,4⟩,⟨⟨0,0⟩,⟨0,(5/9:ℚ)⟩⟩),
  (⟨0,0,2,2⟩,⟨⟨0,0⟩,⟨0,(81755/82008:ℚ)⟩⟩),
  (⟨0,0,4,0⟩,⟨⟨0,0⟩,⟨0,(5/24:ℚ)⟩⟩),
  (⟨0,2,0,2⟩,⟨⟨0,0⟩,⟨0,(58975/82008:ℚ)⟩⟩),
  (⟨0,2,2,0⟩,⟨⟨0,0⟩,⟨0,(5/18:ℚ)⟩⟩),
  (⟨0,4,0,0⟩,⟨⟨0,0⟩,⟨0,(5/72:ℚ)⟩⟩),
  (⟨1,0,2,1⟩,⟨⟨(27/17:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨1,2,0,1⟩,⟨⟨(27/17:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨2,0,0,2⟩,⟨⟨0,0⟩,⟨0,(-12/25:ℚ)⟩⟩),
  (⟨2,0,2,0⟩,⟨⟨0,0⟩,⟨0,(-87/425:ℚ)⟩⟩),
  (⟨2,2,0,0⟩,⟨⟨0,0⟩,⟨0,(-36/425:ℚ)⟩⟩),
  (⟨4,0,0,0⟩,⟨⟨0,0⟩,⟨0,(324/3125:ℚ)⟩⟩)]
private def fullHigherTermsCodes : List ℕ := [
  0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,
  18,19,20,21,22,23,3468,3469,3470,3471,3472,3473,3474,3475,3476,3477,3478,3479,
  3480,3481,3482,3483,3484,3485,3486,3487,3488,3489,3490,3491]
def fullHigherTerms : List SourceTerm := decodeTerms fullHigherTermsAtoms fullHigherTermsCodes

def leadingTensor (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix fullLeadingTerms p
def higherTensor (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix fullHigherTerms p

private theorem full_reflected (p : Fin 4→ℂ) : sourceMatrix (reflectedTerms fullKernelTerms) p=fullKernelFrame.transpose:=by
  rw [reflectedTerms_value,fullKernel_generated]

private def fullResidualTermsAtoms : List SourceAtom := [
  (⟨1,1,0,0⟩,⟨⟨0,0⟩,⟨(36/125:ℚ),0⟩⟩),
  (⟨1,0,1,0⟩,⟨⟨0,0⟩,⟨(-36/125:ℚ),0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-108/625:ℚ)⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(108/625:ℚ)⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨(2/3:ℚ),0⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨(2/3:ℚ),0⟩⟩),
  (⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨(-36/125:ℚ),0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(4/5:ℚ)⟩⟩),
  (⟨0,1,1,0⟩,⟨⟨0,0⟩,⟨(2/3:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,(1/5:ℚ)⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,(-1/5:ℚ)⟩⟩),
  (⟨0,1,1,0⟩,⟨⟨0,0⟩,⟨(-2/3:ℚ),0⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨(-2/3:ℚ),0⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨(-2/3:ℚ),0⟩⟩),
  (⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨(36/125:ℚ),0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨0,(1/5:ℚ)⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨0,(-1/5:ℚ)⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨0,(-2/5:ℚ)⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨0,0⟩,⟨(-2/3:ℚ),0⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨0,0⟩,⟨(2/3:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,(-2/5:ℚ)⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(2/5:ℚ)⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(-2/5:ℚ)⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,-4⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,2⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(-12/25:ℚ),0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,-2⟩,⟨0,0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,2⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,2⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(12/25:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(6/25:ℚ),0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(6/25:ℚ),0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(12/25:ℚ),0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,2⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(-12/25:ℚ),0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(12/25:ℚ),0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(-12/25:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(12/25:ℚ),0⟩⟩)]
private def fullResidualTermsCodes : List ℕ := [
  98838,98876,109821,109859,164732,164770,175715,175753,230626,230627,230628,230664,230665,230666,241611,241612,241649,241650,
  296523,296561,307506,307544,362413,362417,362451,362455,373400,373401,373402,373438,373439,373440,428313,428351,439296,439334,
  494207,494208,494245,494246,505191,505192,505229,505230,560103,560141,571086,571124,625997,626035,636980,647963,647964,648001,
  658947,680909,680910,680947,691894,691895,691933,702878,702916,713861,713899,724844,724838,724882,757790,757791,757828,757829,
  790776,801711,801712,823720,823714,834666,900597,944488,966527,966602,977582,977576,999546,999547,1010455,1010533,1032457,1032494,
  1043474,1043475,1065438,1065432,1076385,1076425,1098313,1098387,1109283,1109291,1131247,1131248,1142238,1142315,1164243,1164279,1175213,1175214,
  1197177,1197185,1208168,1208207]
def fullResidualTerms : List SourceTerm := decodeTerms fullResidualTermsAtoms fullResidualTermsCodes

private def fullInverseResidualTermsAtoms : List SourceAtom := [
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨0,(-5/72:ℚ)⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨0,0⟩,⟨(-25/136:ℚ),0⟩⟩),
  (⟨1,1,0,0⟩,⟨⟨0,(-45/136:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨0,0⟩,⟨(25/136:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/72:ℚ)⟩⟩),
  (⟨1,0,1,0⟩,⟨⟨0,(45/136:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(-5/72:ℚ)⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨(-6/11:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(5/72:ℚ)⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨(5/11:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨(-3/11:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨(-5/11:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨0,(-25/48:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨0,(-5/16:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨0,(-5/24:ℚ)⟩,⟨0,0⟩⟩),
  (⟨2,0,0,0⟩,⟨⟨0,(9/40:ℚ)⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/72:ℚ)⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨0,(5225/9112:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨(-1/4:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨1,0,1,0⟩,⟨⟨0,0⟩,⟨(27/340:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨(-39/67:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨0,(-14825/27336:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨(1/4:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨1,0,1,0⟩,⟨⟨0,0⟩,⟨(-27/340:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨(34/67:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨0,(25/268:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨(-15/67:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨0,(125/804:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨(-25/67:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨0,(5/16:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨0,(5/24:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨0,(5/48:ℚ)⟩,⟨0,0⟩⟩),
  (⟨2,0,0,0⟩,⟨⟨0,(-27/200:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨(-1/4:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨0,(-5225/9112:ℚ)⟩,⟨0,0⟩⟩),
  (⟨1,1,0,0⟩,⟨⟨0,0⟩,⟨(-27/340:ℚ),0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨(-39/67:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨(1/4:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨0,(14825/27336:ℚ)⟩,⟨0,0⟩⟩),
  (⟨1,1,0,0⟩,⟨⟨0,0⟩,⟨(27/340:ℚ),0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨(34/67:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨0,(-25/268:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨(-15/67:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨0,(-125/804:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨(-25/67:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨0,(24805/54672:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨(3/67:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨0,(-24805/54672:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨(3/67:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨(-36/67:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/72:ℚ)⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨(31/67:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨(-15/67:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨(-25/67:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,(5/12:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨0,0⟩,⟨0,(-71/408:ℚ)⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(-179/540:ℚ),0⟩⟩),
  (⟨1,0,1,0⟩,⟨⟨(-111/340:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,1,1,0⟩,⟨⟨(-25/72:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(25/108:ℚ),0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(-179/540:ℚ),0⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨0,0⟩,⟨0,(71/408:ℚ)⟩⟩),
  (⟨1,1,0,0⟩,⟨⟨(111/340:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨(-25/72:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨(25/72:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,1,1,0⟩,⟨⟨(25/72:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(-179/540:ℚ),0⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨(-25/72:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨(25/72:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,(5/24:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,(-5/134:ℚ)⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-5/198:ℚ),0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(5/198:ℚ),0⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨(15925/13668:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,(5/12:ℚ)⟩,⟨0,0⟩⟩),
  (⟨1,0,1,0⟩,⟨⟨0,0⟩,⟨0,(9/68:ℚ)⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,(-5/67:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨(1775/1224:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,(-5/24:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨(1975/4824:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨(-25/18:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨(-25/36:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨(-25/36:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨2,0,0,0⟩,⟨⟨(3/5:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,(5/12:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨(-15925/13668:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨1,1,0,0⟩,⟨⟨0,0⟩,⟨0,(-9/68:ℚ)⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,(-5/67:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,(-5/12:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨(1775/1224:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨1,1,0,0⟩,⟨⟨0,0⟩,⟨0,(9/68:ℚ)⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨(-1975/4824:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,(5/72:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,(-25/72:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,(-5/12:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,(5/6:ℚ)⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(25/54:ℚ),0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-25/54:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,(5/72:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,(-25/72:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,(-5/36:ℚ)⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-25/324:ℚ),0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,(25/36:ℚ)⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(25/324:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,(-5/72:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,(25/72:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,(5/12:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,(-5/12:ℚ)⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-5/12:ℚ),0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,(5/18:ℚ)⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(25/162:ℚ),0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(5/162:ℚ),0⟩⟩)]
private def fullInverseResidualTermsCodes : List ℕ := [
  301716,301717,301718,301833,301834,335243,335244,335245,335359,335361,502866,502867,502984,536393,536394,536511,637084,670609,
  704018,704019,704020,704021,704134,704135,704136,704137,737546,905167,905168,905169,905283,905286,905285,938695,938696,938697,
  938811,938814,938813,1039271,1039387,1039388,1072797,1072913,1072914,1106310,1139847,1139848,1139849,1139850,1139963,1139964,1139965,1139966,
  1307471,1307472,1307473,1307590,1307588,1307589,1340999,1341000,1341001,1341118,1341116,1341117,1441575,1441692,1441691,1475101,1475218,1475217,
  1508615,1508627,1508621,1508744,1508743,1508737,1542153,1542124,1542129,1542269,1542270,1542245,1709775,1709742,1709892,1743301,1743302,1743419,
  1843992,1877517,1910926,1944451,1944452,1944453,1944567,1944569,1977978,1977979,1978094,2011504,2011505,2011506,2011621,2011622,2045031,2045032,
  2045147,2045148,2078557,2078551,2078673,2112082,2145607,2145723,2179132,2179248,2212647,2246181,2246298,2246299,2313229,2313346,2313348,2346757,
  2346758,2346759,2346873,2346876,2346875,2413809,2413806,2413807,2413925,2413923,2447334,2447442,2447444,2514382,2514490,2514491,2547907,2548023,
  2548020,2648480,2648481,2648482,2648483,2648596,2648597,2648598,2648599,2682008,2682009,2682010,2682127,2682125,2682126,2749060,2749061,2749062,
  2749177,2749178,2883159,2883271,2883275,2950440,2950557,2950674,3051247,3051248,3084536,3084653,3084750,3151585,3151700,3151818,3252391,3252393,
  3285681,3285796,3285894,3352734,3352851,3352952,3453308,3453309,3453426,3453427,3486836,3486953,3487048,3553879,3553994,3554096,3587410,3587363,
  3587527,3587528,3654461,3654462,3654577,3654579,3687981,3688096,3688192]
def fullInverseResidualTerms : List SourceTerm := decodeTerms fullInverseResidualTermsAtoms fullInverseResidualTermsCodes

private theorem full_residual_certificate :
    fastNormalizeTerms (productTerms activeTerms fullKernelTerms++negativeTerms fullResidualTerms)=[]:=by decide +kernel

theorem fullResidual_generated (p : Fin 4→ℂ) : sourceMatrix fullResidualTerms p=activeKernel p*fullKernelFrame:=by
  have h:=normalization_equal _ _ full_residual_certificate p
  simpa only [productTerms_value,fullKernel_generated,activeKernel] using h.symm

private theorem full_inverse_residual_certificate :
    fastNormalizeTerms (productTerms fullInverseTerms fullResidualTerms++negativeTerms fullInverseResidualTerms)=[]:=by decide +kernel

theorem fullInverseResidual_generated (p : Fin 4→ℂ) :
    sourceMatrix fullInverseResidualTerms p=fullInverse*(activeKernel p*fullKernelFrame):=by
  have h:=normalization_equal _ _ full_inverse_residual_certificate p
  simpa only [productTerms_value,fullInverse_generated,fullResidual_generated] using h.symm

private theorem full_residual_reflected (p : Fin 4→ℂ) :
    sourceMatrix (reflectedTerms fullResidualTerms) p=fullKernelFrame.transpose*activeKernel p:=by
  rw [reflectedTerms_value,fullResidual_generated,Matrix.transpose_mul,activeKernel_reflect]

private theorem full_tensor_certificate :
    fastNormalizeTerms ((productTerms (reflectedTerms fullKernelTerms) fullResidualTerms++
      negativeTerms (productTerms (reflectedTerms fullResidualTerms) fullInverseResidualTerms))++
      negativeTerms (fullLeadingTerms++fullHigherTerms))=[]:=by decide +kernel

theorem frozenTensor_generated (p : Fin 4→ℂ) : frozenTensor p=leadingTensor p+higherTensor p:=by
  have h:=normalization_equal _ _ full_tensor_certificate p
  simp only [sourceMatrix_append,negativeTerms_value,productTerms_value,fullResidual_generated,
    fullInverseResidual_generated,full_reflected,full_residual_reflected] at h
  simpa only [frozenTensor,leadingTensor,higherTensor,sub_eq_add_neg,mul_assoc] using h

theorem leading_degrees : fullLeadingTerms.all (fun a=>decide (a.powers.total=1 ∨ a.powers.total=2))=true:=by decide +kernel
theorem higher_degrees : fullHigherTerms.all (fun a=>decide (a.powers.total=3 ∨ a.powers.total=4))=true:=by decide +kernel

theorem effectiveKernel_source_tensor (p : complementRegular) : effectiveKernel p=
    leadingTensor p.val+higherTensor p.val-
      fullKernelFrame.transpose*(activeKernel p.val-activeKernel 0)*(complementGreen p-fullInverse)*
        (activeKernel p.val-activeKernel 0)*fullKernelFrame:=by
  rw [effectiveKernel_complete_return,frozenTensor_generated]



open PreparationVacuumMixedControl
open scoped Matrix.Norms.Operator

def inverseBudget : ℝ:=1+(termsPrice fullInverseTerms:ℝ)
def sourceRadius : ℝ:=(4*inverseBudget*variationBudget)⁻¹

theorem inverseBudget_ge_one : 1 ≤ inverseBudget :=by
  have h : (0:ℝ) ≤ (termsPrice fullInverseTerms:ℝ):=by exact_mod_cast termsPrice_nonneg fullInverseTerms
  unfold inverseBudget;linarith

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

theorem fullComplementProjection_price : ‖fullComplementProjection‖ ≤ 1:=by
  simpa only [fullComplementProjection] using projection_price fullComplementFlag

private theorem projectionComplement_price : ‖(1:Matrix (Fin 289) (Fin 289) ℂ)-fullComplementProjection‖ ≤ 1 :=by
  have identity : (1:Matrix (Fin 289) (Fin 289) ℂ)=Matrix.diagonal (fun _=>1):=rfl
  rw [identity,fullComplementProjection,projectionMatrix,Matrix.diagonal_sub,Matrix.linfty_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro i
  split_ifs <;> norm_num

theorem fullInverse_price : ‖fullInverse‖ ≤ (termsPrice fullInverseTerms:ℝ) :=by
  have checked : fullInverseTerms.all (fun a=>decide (a.powers.total=0))=true:=by decide +kernel
  have homogeneous : ∀a∈fullInverseTerms,a.powers.total=0:=by
    intro a ha
    exact of_decide_eq_true (List.all_eq_true.mp checked a ha)
  simpa only [pow_zero,mul_one,fullInverse_generated] using
    sourceMatrix_homogeneous_price fullInverseTerms 0 homogeneous 0 0 le_rfl (fun i=>by simp)

theorem originInverse_price : ‖originInverse‖ ≤ inverseBudget :=by
  unfold originInverse inverseBudget
  calc
    _ ≤ ‖fullInverse‖+‖(1:Matrix (Fin 289) (Fin 289) ℂ)-fullComplementProjection‖:=norm_add_le _ _
    _ ≤ (termsPrice fullInverseTerms:ℝ)+1:=add_le_add fullInverse_price projectionComplement_price
    _= _ :=by ring

theorem complement_delta_price (p : Fin 4→ℂ) (r : ℝ) (nonneg : 0 ≤ r) (small : r ≤ 1)
    (bound : ∀i,‖p i‖ ≤ r) : ‖complementKernel p-complementKernel 0‖ ≤ variationBudget*r :=by
  have positiveBudget : 0 ≤ variationBudget:=by linarith [variationBudget_ge_one]
  have factor : complementKernel p-complementKernel 0=
      fullComplementProjection*(activeKernel p-activeKernel 0)*fullComplementProjection :=by
    unfold complementKernel
    noncomm_ring
  rw [factor]
  calc
    _ ≤ (‖fullComplementProjection‖*‖activeKernel p-activeKernel 0‖)*‖fullComplementProjection‖:=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*(variationBudget*r))*1:=by
      gcongr
      · exact fullComplementProjection_price
      · exact activeKernel_delta_price p r nonneg small bound
      · exact fullComplementProjection_price
    _= _ :=by ring

theorem source_neumann_price (p : Fin 4→ℂ) (bound : ∀i,‖p i‖ ≤ sourceRadius) :
    ‖originInverse*(complementKernel p-complementKernel 0)‖ ≤ (1/4:ℝ) :=by
  have b:=inverseBudget_ge_one
  have k:=variationBudget_ge_one
  calc
    _ ≤ ‖originInverse‖*‖complementKernel p-complementKernel 0‖:=norm_mul_le _ _
    _ ≤ inverseBudget*(variationBudget*sourceRadius):=mul_le_mul originInverse_price
      (complement_delta_price p sourceRadius sourceRadius_pos.le sourceRadius_le_one bound)
      (norm_nonneg _) (by linarith)
    _=1/4:=by
      have bn : inverseBudget≠0:=by linarith
      have kn : variationBudget≠0:=by linarith
      unfold sourceRadius
      field_simp [bn,kn]

theorem sourceRadius_regular (p : Fin 4→ℂ) (bound : ∀i,‖p i‖ ≤ sourceRadius) : p∈complementRegular :=by
  have small : ‖-(originInverse*(complementKernel p-complementKernel 0))‖<1:=by
    rw [norm_neg]
    have h:=source_neumann_price p bound
    linarith
  have step : IsUnit (1+originInverse*(complementKernel p-complementKernel 0)):=by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one small
  have origin : IsUnit (complementKernel 0):=
    ⟨⟨complementKernel 0,originInverse,originInverse_right,originInverse_left⟩,rfl⟩
  have factor : complementKernel 0*(1+originInverse*(complementKernel p-complementKernel 0))=complementKernel p:=by
    calc
      _=complementKernel 0+(complementKernel 0*originInverse)*(complementKernel p-complementKernel 0):=by noncomm_ring
      _= _ :=by rw [originInverse_right,one_mul];abel
  have unit:=origin.mul step
  rw [factor] at unit
  exact (Matrix.isUnit_iff_isUnit_det _).mp unit

def controlledPoint (p : Fin 4→ℂ) (bound : ∀i,‖p i‖ ≤ sourceRadius) : complementRegular:=
  ⟨p,sourceRadius_regular p bound⟩

theorem complement_full_inverse_price (p : Fin 4→ℂ) (bound : ∀i,‖p i‖ ≤ sourceRadius) :
    ‖(complementKernel p)⁻¹‖ ≤ 2*inverseBudget :=by
  have unit:=sourceRadius_regular p bound
  have inverse : (complementKernel p)⁻¹=originInverse-
      (originInverse*(complementKernel p-complementKernel 0))*(complementKernel p)⁻¹ :=by
    have old:=originInverse_left
    have new:=Matrix.mul_nonsing_inv (complementKernel p) unit
    calc
      _=(originInverse*complementKernel 0)*(complementKernel p)⁻¹:=by rw [old,one_mul]
      _=originInverse*(complementKernel p*(complementKernel p)⁻¹)-
          (originInverse*(complementKernel p-complementKernel 0))*(complementKernel p)⁻¹:=by noncomm_ring
      _= _ :=by rw [new,mul_one]
  have triangle : ‖(complementKernel p)⁻¹‖ ≤ inverseBudget+(1/4:ℝ)*‖(complementKernel p)⁻¹‖:=by
    calc
      _=‖originInverse-(originInverse*(complementKernel p-complementKernel 0))*(complementKernel p)⁻¹‖:=congrArg norm inverse
      _ ≤ ‖originInverse‖+‖(originInverse*(complementKernel p-complementKernel 0))*(complementKernel p)⁻¹‖:=norm_sub_le _ _
      _ ≤ inverseBudget+(1/4:ℝ)*‖(complementKernel p)⁻¹‖:=by
        gcongr
        · exact originInverse_price
        · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (source_neumann_price p bound) (norm_nonneg _))
  have b:=inverseBudget_ge_one
  linarith

theorem complementGreen_price (p : Fin 4→ℂ) (bound : ∀i,‖p i‖ ≤ sourceRadius) :
    ‖complementGreen (controlledPoint p bound)‖ ≤ 2*inverseBudget :=by
  have positiveBudget : 0 ≤ inverseBudget:=by linarith [inverseBudget_ge_one]
  unfold complementGreen
  change ‖fullComplementProjection*(complementKernel p)⁻¹*fullComplementProjection‖ ≤ _
  calc
    _ ≤ (‖fullComplementProjection‖*‖(complementKernel p)⁻¹‖)*‖fullComplementProjection‖:=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*(2*inverseBudget))*1:=by
      gcongr
      · exact fullComplementProjection_price
      · exact complement_full_inverse_price p bound
      · exact fullComplementProjection_price
    _= _ :=by ring


theorem inversePrice_exact : termsPrice fullInverseTerms=(3267130962160409/14460684885900:ℚ):=by decide +kernel

theorem sourceRadius_exact : sourceRadius=(1355689208053125/4462200029129218450003:ℝ):=by
  rw [sourceRadius,inverseBudget,variationBudget,inversePrice_exact,PreparationVacuumMixedControl.variationPrice_exact]
  norm_num



theorem complementGreen_delta (p : complementRegular) :
    complementGreen p-fullInverse=-(complementGreen p*(activeKernel p.val-activeKernel 0)*fullInverse):=by
  have originRight : fullComplementProjection*activeKernel 0*fullInverse=fullComplementProjection:=by
    have h:=complementGreen_right complementOrigin
    rw [complementGreen_origin] at h
    exact h
  have originReturn : complementGreen p*activeKernel 0*fullInverse=complementGreen p:=by
    calc
      _=(complementGreen p*fullComplementProjection)*activeKernel 0*fullInverse:=by rw [complementGreen_right_support]
      _=complementGreen p*(fullComplementProjection*activeKernel 0*fullInverse):=by noncomm_ring
      _=complementGreen p:=by rw [originRight,complementGreen_right_support]
  have currentReturn : complementGreen p*activeKernel p.val*fullInverse=fullInverse:=by
    calc
      _=complementGreen p*activeKernel p.val*(fullComplementProjection*fullInverse):=by rw [fullInverse_left_support]
      _=(complementGreen p*activeKernel p.val*fullComplementProjection)*fullInverse:=by noncomm_ring
      _=fullInverse:=by rw [complementGreen_left,fullInverse_left_support]
  rw [mul_sub,sub_mul,currentReturn,originReturn]
  abel

theorem complementGreen_delta_price (p : Fin 4→ℂ) (r : ℝ) (nonneg : 0 ≤ r) (cap : r ≤ sourceRadius)
    (bound : ∀i,‖p i‖ ≤ r) :
    ‖complementGreen (controlledPoint p (fun i=>(bound i).trans cap))-fullInverse‖ ≤
      2*inverseBudget^2*variationBudget*r:=by
  rw [complementGreen_delta,norm_neg]
  have inverseBound : ‖fullInverse‖ ≤ inverseBudget:=by
    have h:=fullInverse_price
    unfold inverseBudget
    linarith
  have b:=inverseBudget_ge_one
  have k:=variationBudget_ge_one
  calc
    _ ≤ (‖complementGreen (controlledPoint p (fun i=>(bound i).trans cap))‖*‖activeKernel p-activeKernel 0‖)*‖fullInverse‖:=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ((2*inverseBudget)*(variationBudget*r))*inverseBudget:=by
      gcongr
      · exact complementGreen_price p _
      · exact activeKernel_delta_price p r nonneg (cap.trans sourceRadius_le_one) bound
    _= _ :=by ring



def kernelBudget : ℝ:=(termsPrice fullKernelTerms:ℝ)
def higherBudget : ℝ:=(termsPrice fullHigherTerms:ℝ)
def effectiveErrorBudget : ℝ:=higherBudget+2*kernelBudget^2*inverseBudget^2*variationBudget^3

theorem kernelBudget_nonneg : 0 ≤ kernelBudget:=by unfold kernelBudget;exact_mod_cast termsPrice_nonneg fullKernelTerms
theorem higherBudget_nonneg : 0 ≤ higherBudget:=by unfold higherBudget;exact_mod_cast termsPrice_nonneg fullHigherTerms

theorem fullKernel_price : ‖fullKernelFrame‖ ≤ kernelBudget ∧ ‖fullKernelFrame.transpose‖ ≤ kernelBudget:=by
  have checked : fullKernelTerms.all (fun a=>decide (a.powers.total=0))=true:=by decide +kernel
  have reflected : (reflectedTerms fullKernelTerms).all (fun a=>decide (a.powers.total=0))=true:=by decide +kernel
  have samePrice : termsPrice (reflectedTerms fullKernelTerms)=termsPrice fullKernelTerms:=by decide +kernel
  constructor
  · have h:=sourceMatrix_homogeneous_price fullKernelTerms 0
      (fun a ha=>of_decide_eq_true (List.all_eq_true.mp checked a ha)) (0:Fin 4→ℂ) 0 le_rfl (fun i=>by simp)
    simpa only [fullKernel_generated,pow_zero,mul_one,kernelBudget] using h
  · have h:=sourceMatrix_homogeneous_price (reflectedTerms fullKernelTerms) 0
      (fun a ha=>of_decide_eq_true (List.all_eq_true.mp reflected a ha)) (0:Fin 4→ℂ) 0 le_rfl (fun i=>by simp)
    simpa only [full_reflected,pow_zero,mul_one,samePrice,kernelBudget] using h

theorem higherTensor_price (p : Fin 4→ℂ) (r : ℝ) (nonneg : 0 ≤ r) (small : r ≤ 1) (bound : ∀i,‖p i‖ ≤ r) :
    ‖higherTensor p‖ ≤ higherBudget*r^3:=by
  have power : r^4 ≤ r^3:=by nlinarith [mul_nonneg (sub_nonneg.mpr small) (pow_nonneg nonneg 3)]
  have termBound (a : SourceTerm) (ha : a∈fullHigherTerms) : ‖a.matrix p‖ ≤ (coefficientPrice a.coefficient:ℝ)*r^3:=by
    have degree:=of_decide_eq_true (List.all_eq_true.mp higher_degrees a ha)
    have price:=sourceTerm_price a p r nonneg bound
    rcases degree with degree|degree
    · simpa only [degree] using price
    · rw [degree] at price
      exact price.trans (mul_le_mul_of_nonneg_left power (by exact_mod_cast coefficientPrice_nonneg a.coefficient))
  change ‖sourceMatrix fullHigherTerms p‖ ≤ (termsPrice fullHigherTerms:ℝ)*r^3
  generalize fullHigherTerms=selected at termBound ⊢
  induction selected with
  | nil=>simp [sourceMatrix,termsPrice]
  | cons a rest ih=>
    have first:=termBound a (by simp)
    have tail : ‖sourceMatrix rest p‖ ≤ (termsPrice rest:ℝ)*r^3:=by
      apply ih
      intro b hb
      exact termBound b (by simp [hb])
    rw [sourceMatrix_cons]
    calc
      _ ≤ ‖a.matrix p‖+‖sourceMatrix rest p‖:=norm_add_le _ _
      _ ≤ (coefficientPrice a.coefficient:ℝ)*r^3+(termsPrice rest:ℝ)*r^3:=add_le_add first tail
      _=(termsPrice (a::rest):ℝ)*r^3:=by
        change _=((coefficientPrice a.coefficient+termsPrice rest:ℚ):ℝ)*r^3
        push_cast
        ring

theorem effectiveKernel_leading_price (p : Fin 4→ℂ) (r : ℝ) (nonneg : 0 ≤ r) (cap : r ≤ sourceRadius)
    (bound : ∀i,‖p i‖ ≤ r) :
    ‖effectiveKernel (controlledPoint p (fun i=>(bound i).trans cap))-leadingTensor p‖ ≤ effectiveErrorBudget*r^3:=by
  let point:=controlledPoint p (fun i=>(bound i).trans cap)
  have equation:=effectiveKernel_source_tensor point
  have difference : effectiveKernel point-leadingTensor p=higherTensor p-
      fullKernelFrame.transpose*(activeKernel p-activeKernel 0)*(complementGreen point-fullInverse)*
        (activeKernel p-activeKernel 0)*fullKernelFrame:=by
    rw [equation]
    change (leadingTensor p+higherTensor p-_)-leadingTensor p=higherTensor p-_
    abel
  have k:=kernelBudget_nonneg
  have b:=inverseBudget_ge_one
  have v:=variationBudget_ge_one
  have h:=higherBudget_nonneg
  have delta:=activeKernel_delta_price p r nonneg (cap.trans sourceRadius_le_one) bound
  have green:=complementGreen_delta_price p r nonneg cap bound
  change ‖effectiveKernel point-leadingTensor p‖ ≤ _
  rw [difference]
  calc
    _ ≤ ‖higherTensor p‖+‖fullKernelFrame.transpose*(activeKernel p-activeKernel 0)*(complementGreen point-fullInverse)*
        (activeKernel p-activeKernel 0)*fullKernelFrame‖:=norm_sub_le _ _
    _ ≤ higherBudget*r^3+
        (((‖fullKernelFrame.transpose‖*‖activeKernel p-activeKernel 0‖)*‖complementGreen point-fullInverse‖)*
          ‖activeKernel p-activeKernel 0‖)*‖fullKernelFrame‖:=by
      apply add_le_add (higherTensor_price p r nonneg (cap.trans sourceRadius_le_one) bound)
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))) (norm_nonneg _))
    _ ≤ higherBudget*r^3+(((kernelBudget*(variationBudget*r))*(2*inverseBudget^2*variationBudget*r))*
        (variationBudget*r))*kernelBudget:=by
      gcongr
      · exact fullKernel_price.2
      · exact fullKernel_price.1
    _=effectiveErrorBudget*r^3:=by unfold effectiveErrorBudget;ring

theorem effectiveErrorBudget_nonneg : 0 ≤ effectiveErrorBudget:=by
  have h:=higherBudget_nonneg
  have k:=variationBudget_ge_one
  unfold effectiveErrorBudget
  positivity

theorem kernelPrice_exact : termsPrice fullKernelTerms=(72/5:ℚ):=by decide +kernel
theorem higherPrice_exact : termsPrice fullHigherTerms=(4200156368/32034375:ℚ):=by decide +kernel


end LowEnergy.PreparationVacuumFullOriginResponse
