import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceMixedPrincipal
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceStaticNativeMode
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationOriginalHessianReturn

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMixedPrincipal
open PreparationVacuumOriginalGreenFeedback SourcePropagationNativeActionHessian
open PreparationVacuumPhysicalFieldChannel PreparationVacuumMixedFieldReturn
open scoped Matrix BigOperators
attribute [local irreducible] nativeHessian originalJacobi originalChange originalReadback originalRowLift

def nativeJetFrame (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=originalChange p*jetFrame p
def nativeKernelFrame (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=originalChange p*kernelFrame p
def nativeTestFrame (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=reflectedKernelFrame p*originalReadback p

theorem nativeTest_same_source (p : Fin 4→ℂ) : nativeTestFrame p=(nativeKernelFrame (-p)).transpose :=by
  rw [nativeTestFrame,kernel_reflected,originalReadback,nativeKernelFrame,Matrix.transpose_mul]

theorem nativeJet_actual (time space : ℂ) :
    nativeFourierHessian nativeHessian (planeMomentum time space)*nativeJetFrame (planeMomentum time space)=
      originalRowLift (planeMomentum time space)*(activeKernel (planeMomentum time space)*jetFrame (planeMomentum time space)) :=by
  rw [nativeActionFourierHessian_original,nativeJetFrame]
  calc
    _=(originalJacobi (planeMomentum time space)*originalChange (planeMomentum time space)*activeProjection)*jetFrame (planeMomentum time space) :=by
      rw [mul_assoc,sourceFrame_active,mul_assoc]
    _= _ :=by rw [original_active_intertwiner,mul_assoc]

theorem nativeJet_whole_residual (time space : ℂ) :
    nativeFourierHessian nativeHessian (planeMomentum time space)*nativeJetFrame (planeMomentum time space)=
      originalRowLift (planeMomentum time space)*
        (sourceMatrix quadraticTerms (planeMomentum time space)+sourceMatrix cubicTerms (planeMomentum time space)) :=by
  rw [nativeJet_actual,sourceFrame_residual]

/-- Actual whole-field pairing of two restrictions of the original occurrence. -/
theorem native_principal_generated (time space : ℂ) :
    nativeTestFrame (planeMomentum time space)*nativeFourierHessian nativeHessian (planeMomentum time space)*
      nativeJetFrame (planeMomentum time space)=sourcePrincipal time space :=by
  rw [mul_assoc,nativeJet_actual,nativeTestFrame]
  have inverse : originalReadback (planeMomentum time space)*originalRowLift (planeMomentum time space)=1 :=by
    rw [originalReadback,originalRowLift,←Matrix.transpose_mul,original_inverse_change,Matrix.transpose_one]
  rw [←mul_assoc,mul_assoc (reflectedKernelFrame _) (originalReadback _) _,inverse,mul_one]
  simpa only [mul_assoc] using sourcePrincipal_generated time space

def firstCharacteristic (time space : ℂ) : ℂ :=time^2+space^2/3
def secondCharacteristic (time space : ℂ) : ℂ :=time^2-(594/1675:ℂ)*space^2

theorem sourcePrincipal_first (time space : ℂ) :
    sourcePrincipal time space 0 0=(-25/18:ℂ)*rootTwo*rootFifteen*firstCharacteristic time space :=by
  norm_num [sourcePrincipal,principalTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
    Powers.value,planeMomentum,coefficientValue,Fin.ext_iff,firstCharacteristic]
  ring

theorem sourcePrincipal_second (time space : ℂ) :
    sourcePrincipal time space 1 1=(10/99:ℂ)*rootTwo*rootFifteen*secondCharacteristic time space :=by
  norm_num [sourcePrincipal,principalTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
    Powers.value,planeMomentum,coefficientValue,Fin.ext_iff,secondCharacteristic]
  ring

theorem sourcePrincipal_cross (time space : ℂ) :
    sourcePrincipal time space 0 1=0 ∧ sourcePrincipal time space 1 0=0 :=by
  norm_num [sourcePrincipal,principalTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
    Powers.value,planeMomentum,coefficientValue,Fin.ext_iff]

theorem firstCharacteristic_physical (energy momentum : ℝ) :
    firstCharacteristic (-Complex.I*(energy:ℂ)) (Complex.I*(momentum:ℂ))=
      -((energy:ℂ)^2+(momentum:ℂ)^2/3) :=by
  unfold firstCharacteristic
  ring_nf
  simp [Complex.I_sq]
  ring

theorem secondCharacteristic_physical (energy momentum : ℝ) :
    secondCharacteristic (-Complex.I*(energy:ℂ)) (Complex.I*(momentum:ℂ))=
      -(energy:ℂ)^2+(594/1675:ℂ)*(momentum:ℂ)^2 :=by
  unfold secondCharacteristic
  ring_nf
  simp [Complex.I_sq]
  ring

def originTerms (terms : List SourceTerm) : List SourceTerm :=
  terms.filter (fun a=>decide (a.powers.total=0))

private theorem originTerm_zero (a : SourceTerm) (off : a.powers.total≠0) : a.matrix 0=0 :=by
  have vanishing : a.powers.value 0=0 :=by
    have total : a.powers.temporal+a.powers.first+a.powers.second+a.powers.third≠0:=off
    simp only [Powers.value,Pi.zero_apply]
    by_cases t : a.powers.temporal=0
    · by_cases x : a.powers.first=0
      · by_cases y : a.powers.second=0
        · have z : a.powers.third≠0:=by omega
          simp [z]
        · simp [y]
      · simp [x]
    · simp [t]
  simp [SourceTerm.matrix,vanishing]

theorem originTerms_generated (terms : List SourceTerm) : sourceMatrix (originTerms terms) 0=sourceMatrix terms 0 :=by
  induction terms with
  | nil=>rfl
  | cons a rest ih=>
    simp only [originTerms,List.filter_cons] at ih ⊢
    split_ifs with on
    · rw [sourceMatrix_cons,ih,sourceMatrix_cons]
    · rw [ih,sourceMatrix_cons,originTerm_zero a (by simpa using on),zero_add]
def nativeOriginTerms : List SourceTerm := [
  ⟨21,0,⟨0,0,0,0⟩,⟨⟨0,3/10⟩,⟨0,0⟩⟩⟩,
  ⟨34,0,⟨0,0,0,0⟩,⟨⟨0,-3/10⟩,⟨0,0⟩⟩⟩,
  ⟨88,0,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨92,0,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨110,0,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨118,0,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨217,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,1/5⟩⟩⟩,
  ⟨230,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,-1/5⟩⟩⟩,
  ⟨21,1,⟨0,0,0,0⟩,⟨⟨0,3/10⟩,⟨0,0⟩⟩⟩,
  ⟨34,1,⟨0,0,0,0⟩,⟨⟨0,-3/10⟩,⟨0,0⟩⟩⟩,
  ⟨88,1,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨94,1,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨112,1,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨118,1,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨217,1,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,1/5⟩⟩⟩,
  ⟨230,1,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,-1/5⟩⟩⟩
]

private theorem native_origin_certificate :
    fastNormalizeTerms (productTerms (originTerms originalChangeTerms) kernelTerms++negativeTerms nativeOriginTerms)=[] :=by decide +kernel

theorem native_origin_generated : nativeKernelFrame 0=sourceMatrix nativeOriginTerms 0 :=by
  have h:=normalization_equal _ _ native_origin_certificate 0
  rw [productTerms_value,originTerms_generated] at h
  simpa only [nativeKernelFrame,originalChange,kernelFrame] using h

def nativeCombination (a b : ℂ) : Fin 289→ℂ:=
  nativeKernelFrame 0*ᵥ(Pi.single 0 a+Pi.single 1 b)

theorem nativeCombination_gauge_entries (a b : ℂ) :
    nativeCombination a b (gaugeSlot 1 0)=(3/10:ℂ)*rootTwo*(a+b) ∧
    nativeCombination a b (gaugeSlot 1 1)=0 ∧
    nativeCombination a b (gaugeSlot 2 0)=0 ∧
    nativeCombination a b (gaugeSlot 2 1)=-(3/10:ℂ)*rootTwo*(a+b) :=by
  rw [nativeCombination,native_origin_generated,Matrix.mulVec_add,Matrix.mulVec_single,Matrix.mulVec_single]
  norm_num [sourceMatrix,nativeOriginTerms,SourceTerm.matrix,Matrix.single_apply,Powers.value,
    coefficientValue,gaugeSlot,Fin.ext_iff]
  constructor <;> ring

theorem nativeCombination_gauge_minor (a b : ℂ) :
    nativeCombination a b (gaugeSlot 1 0)*nativeCombination a b (gaugeSlot 2 1)-
      nativeCombination a b (gaugeSlot 1 1)*nativeCombination a b (gaugeSlot 2 0)=
        -(9/50:ℂ)*(a+b)^2 :=by
  rcases nativeCombination_gauge_entries a b with ⟨h10,h11,h20,h21⟩
  rw [h10,h11,h20,h21]
  have two : rootTwo^2=2:=by
    unfold rootTwo
    norm_cast
    norm_num [Real.sq_sqrt]
  linear_combination (norm := ring_nf) (-(9/100:ℂ)*(a+b)^2)*two

def staticWeightTerms : List SourceTerm := [
  ⟨0,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨-27/625,0⟩⟩⟩,
  ⟨1,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨-67/120,0⟩⟩⟩]

private theorem static_decomposition_certificate :
    fastNormalizeTerms (productTerms kernelTerms staticWeightTerms++
      negativeTerms (originTerms channelNumeratorTerms))=[] :=by decide +kernel

theorem static_kernel_decomposition :
    kernelFrame 0*ᵥ(Pi.single 0 (-(27/625:ℂ)*rootFifteen)+Pi.single 1 (-(67/120:ℂ)*rootFifteen))=
      channelNumerator 0 :=by
  have h:=normalization_equal _ _ static_decomposition_certificate 0
  rw [productTerms_value,originTerms_generated] at h
  have weights : (fun i=>sourceMatrix staticWeightTerms 0 i 0)=
      (Pi.single 0 (-(27/625:ℂ)*rootFifteen)+Pi.single 1 (-(67/120:ℂ)*rootFifteen) : Fin 289→ℂ) :=by
    ext i
    norm_num [staticWeightTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,Powers.value,
      coefficientValue,Pi.single_apply,eq_comm]
  have result:=congrArg (fun A : Matrix (Fin 289) (Fin 289) ℂ=>fun i=>A i 0) h
  change kernelFrame 0*ᵥ(fun i=>sourceMatrix staticWeightTerms 0 i 0)=_ at result
  rw [weights] at result
  convert! result using 1

theorem static_native_decomposition :
    nativeCombination (-(27/625:ℂ)*rootFifteen) (-(67/120:ℂ)*rootFifteen)=
      channelNativeNumerator 0 :=by
  rw [nativeCombination,nativeKernelFrame,←Matrix.mulVec_mulVec,static_kernel_decomposition]
  rw [channelNativeNumerator]
  have axisZero : staticAxis 0=0:=by ext i;fin_cases i <;> rfl
  rw [axisZero]

/-- The exact raw gauge restriction supplies this necessary one-Lie factorization condition. -/
theorem nativeCombination_singleLie_condition (a b : ℂ) (polarization : Fin 4→ℂ) (charge : Fin 12→ℂ)
    (shape : ∀mu index,nativeCombination a b (gaugeSlot mu index)=polarization mu*charge index) : a+b=0 :=by
  have minor:=nativeCombination_gauge_minor a b
  simp only [shape] at minor
  have zero : polarization 1*charge 0*(polarization 2*charge 1)-
      polarization 1*charge 1*(polarization 2*charge 0)=0:=by ring
  rw [zero] at minor
  have square : (a+b)^2=0:=by
    have factor:=mul_eq_zero.mp minor.symm
    exact factor.resolve_left (by norm_num)
  by_contra h
  exact (pow_ne_zero 2 h) square

end LowEnergy.PreparationVacuumMixedPrincipal
