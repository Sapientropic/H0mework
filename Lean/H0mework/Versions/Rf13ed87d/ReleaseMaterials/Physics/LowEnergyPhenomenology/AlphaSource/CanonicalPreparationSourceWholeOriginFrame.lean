import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceEffectiveLeading

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWholeOrigin
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedEffective
open PreparationVacuumMixedFieldReturn SourcePropagationNativeActionHessian
open scoped Matrix BigOperators
attribute [local irreducible] originalJacobi originalChange originalInverse activeKernel kernelFrame

def wholeOriginTerms : List SourceTerm := [
  ⟨74,0,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨74,2,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨98,0,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨98,2,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨76,0,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨76,2,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨100,0,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨100,2,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨80,0,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨80,2,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨104,0,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨104,2,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨82,0,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨82,2,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨106,0,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨106,2,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨86,1,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨86,3,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨110,1,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨110,3,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨110,4,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨88,1,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨88,3,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨112,1,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨112,3,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨112,4,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨92,1,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨92,3,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨116,1,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨116,3,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨116,4,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨94,1,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨94,3,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨118,1,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨118,3,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨118,4,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩]
def wholeActiveOriginTerms : List SourceTerm := [
  ⟨21,1,⟨0,0,0,0⟩,⟨⟨0,-3/5⟩,⟨0,0⟩⟩⟩,
  ⟨21,3,⟨0,0,0,0⟩,⟨⟨0,-3/5⟩,⟨0,0⟩⟩⟩,
  ⟨21,4,⟨0,0,0,0⟩,⟨⟨0,3/10⟩,⟨0,0⟩⟩⟩,
  ⟨34,1,⟨0,0,0,0⟩,⟨⟨0,3/5⟩,⟨0,0⟩⟩⟩,
  ⟨34,3,⟨0,0,0,0⟩,⟨⟨0,3/5⟩,⟨0,0⟩⟩⟩,
  ⟨34,4,⟨0,0,0,0⟩,⟨⟨0,-3/10⟩,⟨0,0⟩⟩⟩,
  ⟨79,1,⟨0,0,0,0⟩,⟨⟨-2,0⟩,⟨0,0⟩⟩⟩,
  ⟨79,3,⟨0,0,0,0⟩,⟨⟨-2,0⟩,⟨0,0⟩⟩⟩,
  ⟨79,4,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨83,3,⟨0,0,0,0⟩,⟨⟨-2,0⟩,⟨0,0⟩⟩⟩,
  ⟨85,1,⟨0,0,0,0⟩,⟨⟨-2,0⟩,⟨0,0⟩⟩⟩,
  ⟨85,4,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨89,0,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨89,2,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨91,0,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨91,2,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨95,0,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨95,2,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨97,0,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨97,2,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨101,4,⟨0,0,0,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨103,4,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨107,4,⟨0,0,0,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨109,4,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩]
def wholeNullOriginTerms : List SourceTerm := [
  ⟨114,1,⟨0,0,0,0⟩,⟨⟨-2,0⟩,⟨0,0⟩⟩⟩,
  ⟨114,3,⟨0,0,0,0⟩,⟨⟨-2,0⟩,⟨0,0⟩⟩⟩,
  ⟨114,4,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩]
def dualKernelTerms : List SourceTerm := [
  ⟨89,0,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨91,0,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨95,1,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨97,1,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨101,2,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨103,2,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨107,2,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨109,2,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩]
def canonicalOriginMixTerms : List SourceTerm := [
  ⟨0,3,⟨0,0,0,0⟩,⟨⟨-2,0⟩,⟨0,0⟩⟩⟩,
  ⟨1,1,⟨0,0,0,0⟩,⟨⟨-2,0⟩,⟨0,0⟩⟩⟩,
  ⟨1,4,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩]
def dualOriginMixTerms : List SourceTerm := [
  ⟨0,0,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨1,0,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨0,2,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨1,2,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨2,4,⟨0,0,0,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩]
def wholeSelectorTerms : List SourceTerm := [
  ⟨0,74,⟨0,0,0,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨0,80,⟨0,0,0,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨2,74,⟨0,0,0,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨2,80,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨1,86,⟨0,0,0,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨1,92,⟨0,0,0,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨3,86,⟨0,0,0,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨3,92,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨4,92,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨4,110,⟨0,0,0,0⟩,⟨⟨0,1/2⟩,⟨0,0⟩⟩⟩]
def fiveProjectionTerms : List SourceTerm := [
  ⟨0,0,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨1,1,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨2,2,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨3,3,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨4,4,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩]

def wholeOriginFrame : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix wholeOriginTerms 0
def wholeActiveOriginFrame : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix wholeActiveOriginTerms 0
def wholeNullOriginFrame : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix wholeNullOriginTerms 0
def dualKernelFrame : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix dualKernelTerms 0
def wholeOriginSelector : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix wholeSelectorTerms 0
def fiveProjection : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix fiveProjectionTerms 0

private theorem whole_kernel_certificate :
    fastNormalizeTerms (productTerms (originTerms originalJacobiTerms) wholeOriginTerms)=[]:=by decide +kernel

theorem whole_origin_native_kernel : nativeFourierHessian nativeHessian 0*wholeOriginFrame=0:=by
  have h:=normalization_equal (productTerms (originTerms originalJacobiTerms) wholeOriginTerms) [] (by simpa only [negativeTerms,List.map_nil,List.append_nil] using whole_kernel_certificate) (0:Fin 4→ℂ)
  rw [productTerms_value,originTerms_generated,sourceMatrix_nil] at h
  simpa only [nativeActionFourierHessian_original,originalJacobi,wholeOriginFrame] using h

private theorem whole_transport_certificate :
    fastNormalizeTerms (productTerms (originTerms originalInverseTerms) wholeOriginTerms++
      negativeTerms (wholeActiveOriginTerms++wholeNullOriginTerms))=[]:=by decide +kernel

theorem whole_origin_transport : originalInverse 0*wholeOriginFrame=wholeActiveOriginFrame+wholeNullOriginFrame:=by
  have h:=normalization_equal _ _ whole_transport_certificate (0:Fin 4→ℂ)
  rw [productTerms_value,originTerms_generated,sourceMatrix_append] at h
  simpa only [originalInverse,wholeOriginFrame,wholeActiveOriginFrame,wholeNullOriginFrame] using h

theorem whole_origin_reconstruction : originalChange 0*(wholeActiveOriginFrame+wholeNullOriginFrame)=wholeOriginFrame:=by
  rw [←whole_origin_transport,←mul_assoc,original_change_inverse,one_mul]

private theorem whole_split_certificate :
    fastNormalizeTerms ((productTerms kernelTerms canonicalOriginMixTerms++productTerms dualKernelTerms dualOriginMixTerms)++
      negativeTerms wholeActiveOriginTerms)=[]:=by decide +kernel

theorem whole_origin_two_three : wholeActiveOriginFrame=
    kernelFrame 0*sourceMatrix canonicalOriginMixTerms 0+dualKernelFrame*sourceMatrix dualOriginMixTerms 0:=by
  have h:=normalization_equal _ _ whole_split_certificate (0:Fin 4→ℂ)
  rw [sourceMatrix_append,productTerms_value,productTerms_value] at h
  simpa only [wholeActiveOriginFrame,kernelFrame,dualKernelFrame] using h.symm

private theorem dual_kernel_certificate :
    fastNormalizeTerms (productTerms (originTerms activeTerms) dualKernelTerms)=[]:=by decide +kernel

theorem dual_origin_kernel : activeKernel 0*dualKernelFrame=0:=by
  have h:=normalization_equal (productTerms (originTerms activeTerms) dualKernelTerms) [] (by simpa only [negativeTerms,List.map_nil,List.append_nil] using dual_kernel_certificate) (0:Fin 4→ℂ)
  rw [productTerms_value,originTerms_generated,sourceMatrix_nil] at h
  simpa only [activeKernel,dualKernelFrame] using h

private theorem whole_selector_certificate :
    fastNormalizeTerms (productTerms wholeSelectorTerms wholeOriginTerms++negativeTerms fiveProjectionTerms)=[]:=by decide +kernel

theorem whole_origin_coordinates : wholeOriginSelector*wholeOriginFrame=fiveProjection:=by
  have h:=normalization_equal _ _ whole_selector_certificate (0:Fin 4→ℂ)
  simpa only [productTerms_value,wholeOriginSelector,wholeOriginFrame,fiveProjection] using h

def fiveVector (coefficients : Fin 5→ℂ) : Fin 289→ℂ:=fun i=>if h : i.val<5 then coefficients ⟨i.val,h⟩ else 0

theorem fiveProjection_vector (coefficients : Fin 5→ℂ) : fiveProjection*ᵥfiveVector coefficients=fiveVector coefficients:=by
  funext i
  simp [fiveProjection,fiveProjectionTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_mulVec,
    Matrix.add_mulVec,Powers.value,coefficientValue,fiveVector]
  split_ifs with h
  · rcases i with ⟨i,hi⟩
    change i<5 at h
    interval_cases i <;> simp_all
  · have h0 : i≠0:=by intro h;subst i;norm_num at h
    have h1 : i≠1:=by intro h;subst i;norm_num at h
    have h2 : i≠2:=by intro h;subst i;norm_num at h
    have h3 : i≠3:=by intro h;subst i;norm_num at h
    have h4 : i≠4:=by intro h;subst i;norm_num at h
    simp [h0,h1,h2,h3,h4]

theorem whole_origin_independent (left right : Fin 5→ℂ)
    (same : wholeOriginFrame*ᵥfiveVector left=wholeOriginFrame*ᵥfiveVector right) : left=right:=by
  have h:=congrArg (fun v=>wholeOriginSelector*ᵥv) same
  simp only [Matrix.mulVec_mulVec,whole_origin_coordinates,fiveProjection_vector] at h
  funext i
  have hi:=congrFun h (⟨i.val,by omega⟩:Fin 289)
  simpa only [fiveVector,dif_pos i.isLt] using hi

end LowEnergy.PreparationVacuumWholeOrigin
