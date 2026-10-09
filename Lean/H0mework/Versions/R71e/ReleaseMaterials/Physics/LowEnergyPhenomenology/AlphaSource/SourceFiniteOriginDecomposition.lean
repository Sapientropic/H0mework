import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeOriginPrimitiveReturn
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFinitePoleCoefficients

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFiniteOriginCovariance
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativeOriginPhaseWard
open PreparationPhysicalFinitePoleVertices PreparationVacuumFullOriginResponse PreparationVacuumPhysicalCharacteristic
open PreparationVacuumOriginalGreenFeedback PreparationVacuumSoftPoleSelection
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open SourcePropagationNativeActionHessian Electromagnetic.CanonicalCoframe
open SourceQuantumScalarChart StageNineHolonomicField StageNineLorentzConnectionVariation
open FullQuantum.StateGreen CanonicalGradedSpatialSource
open scoped Matrix BigOperators
attribute [local irreducible] fullNativeOrigin slowFastFrame sourcePoleCoordinates nativeBranchVector

private def originSelector : List SourceTerm := [⟨0,0,⟨0,0,0,0⟩,1⟩,⟨0,1,⟨0,0,0,0⟩,1⟩]

/-- The literal independent matter and dual remainder is retained for every original finite pole coordinate. -/
def sourceFiniteOriginRemainderTerms : List SourceTerm := [
⟨74,2,⟨0,0,0,0⟩,1⟩,
  ⟨74,3,⟨0,0,0,0⟩,1⟩,
  ⟨76,2,⟨0,0,0,0⟩,-1⟩,
  ⟨76,3,⟨0,0,0,0⟩,-1⟩,
  ⟨80,2,⟨0,0,0,0⟩,1⟩,
  ⟨80,3,⟨0,0,0,0⟩,-1⟩,
  ⟨82,2,⟨0,0,0,0⟩,-1⟩,
  ⟨82,3,⟨0,0,0,0⟩,1⟩,
  ⟨86,4,⟨0,0,0,0⟩,1⟩,
  ⟨88,4,⟨0,0,0,0⟩,-1⟩,
  ⟨92,0,⟨0,0,0,0⟩,1⟩,
  ⟨92,4,⟨0,0,0,0⟩,1⟩,
  ⟨94,0,⟨0,0,0,0⟩,-1⟩,
  ⟨94,4,⟨0,0,0,0⟩,-1⟩,
  ⟨98,2,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨98,3,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨100,2,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨100,3,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨104,2,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨104,3,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨106,2,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨106,3,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨110,0,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨110,4,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨112,0,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨112,4,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨116,4,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨118,4,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩]

private theorem origin_certificate :
    fastNormalizeTerms (productTerms fullNativeOriginTerms slowFastFrameTerms++
      negativeTerms (productTerms sourceNativeOriginActionTerms originSelector++sourceFiniteOriginRemainderTerms))=[] := by
  decide +kernel

def sourceFiniteOriginAmplitude (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : ℂ :=
  sourcePoleCoordinates branch epsilon s n 0+sourcePoleCoordinates branch epsilon s n 1

def sourceFiniteOriginRemainder (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 289→ℂ :=
  sourceMatrix sourceFiniteOriginRemainderTerms 0*ᵥsourcePoleCoordinates branch epsilon s n

/-- The finite origin's full field is not equated to the soft endpoint: its entire matter/dual remainder is explicit. -/
theorem sourceFiniteOrigin_decomposition (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    sourcePoleOriginField branch epsilon s n=
      sourceFiniteOriginAmplitude branch epsilon s n • nativeBranchVector 0+sourceFiniteOriginRemainder branch epsilon s n := by
  have generated:=normalization_equal _ _ origin_certificate (0:Fin 4→ℂ)
  rw [productTerms_value,sourceMatrix_append,productTerms_value,←fullNativeOrigin_generated,slowFastFrame_constant] at generated
  have selected (v : Fin 289→ℂ) : sourceMatrix originSelector 0*ᵥv=(v 0+v 1) • Pi.single 0 1 := by
    norm_num [originSelector,sourceMatrix,SourceTerm.matrix,Powers.value,coefficientValue,
      Matrix.add_mulVec,Matrix.single_mulVec,Matrix.zero_mulVec,
      QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero]
    ext i
    simp [Pi.single_apply]
    split_ifs <;> simp_all
  have endpoint : sourceMatrix sourceNativeOriginActionTerms 0*ᵥPi.single 0 1=nativeBranchVector 0 := by
    rw [Matrix.mulVec_single_one,sourceNativeOriginAction_generated]
    rfl
  rw [sourcePoleOriginField,generated,Matrix.add_mulVec,←Matrix.mulVec_mulVec,selected,Matrix.mulVec_smul,endpoint]
  rfl

private theorem remainder_support : sourceFiniteOriginRemainderTerms.all
    (fun t=>decide (73≤t.row.val ∧ t.row.val<121))=true := by decide +kernel

private theorem matrix_outside (terms : List SourceTerm) (i j : Fin 289)
    (outside : ∀t∈terms,t.row≠i) : sourceMatrix terms 0 i j=0 := by
  induction terms with
  | nil=>rfl
  | cons t rest ih=>
    rw [sourceMatrix_cons,Matrix.add_apply]
    have term : t.matrix 0 i j=0 := by
      simp only [SourceTerm.matrix,Matrix.single_apply]
      exact if_neg (fun h=>outside t List.mem_cons_self h.1)
    rw [term,ih (fun a ha=>outside a (List.mem_cons_of_mem _ ha)),zero_add]

theorem sourceFiniteOriginRemainder_outside (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (i : Fin 289) (outside : (i.val < (73 : ℕ)) ∨ ((121 : ℕ) ≤ i.val)) : sourceFiniteOriginRemainder branch epsilon s n i=0 := by
  have row (j : Fin 289) : sourceMatrix sourceFiniteOriginRemainderTerms 0 i j=0 := by
    apply matrix_outside
    intro t member equal
    have support:=of_decide_eq_true (List.all_eq_true.mp remainder_support t member)
    have value:=congrArg Fin.val equal
    omega
  simp only [sourceFiniteOriginRemainder,Matrix.mulVec,dotProduct,row,zero_mul,Finset.sum_const_zero]

def sourceOriginPart (imaginary : Bool) (z : ℂ) : ℝ := if imaginary then z.im else z.re

def sourceFiniteOriginPart (imaginary : Bool) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Field289 :=
  fun i=>sourceOriginPart imaginary (sourcePoleOriginField branch epsilon s n i)

def sourceFiniteOriginRemainderPart (imaginary : Bool) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Field289 :=
  fun i=>sourceOriginPart imaginary (sourceFiniteOriginRemainder branch epsilon s n i)

theorem sourceFiniteOriginPart_decomposition (imaginary : Bool) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    sourceFiniteOriginPart imaginary branch epsilon s n=
      sourceOriginPart imaginary (sourceFiniteOriginAmplitude branch epsilon s n) • sourceNativeOriginReal 0+
        sourceFiniteOriginRemainderPart imaginary branch epsilon s n := by
  funext i
  have real:=congrFun (sourceNativeOriginImag_zero 0) i
  change (nativeBranchVector 0 i).im=0 at real
  cases imaginary <;>
    simp [sourceFiniteOriginPart,sourceFiniteOriginRemainderPart,sourceOriginPart,sourceFiniteOrigin_decomposition,
      Pi.smul_apply,smul_eq_mul,Complex.mul_re,Complex.mul_im,real,sourceNativeOriginReal]

/-- The complete remainder has no scalar, gauge, geometry or auxiliary field; its independent primal/dual values remain. -/
theorem sourceFiniteOriginRemainder_fields (imaginary : Bool) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    let f:=sourceFiniteOriginRemainderPart imaginary branch epsilon s n
    fieldScalar f=0 ∧ fieldGauge f=0 ∧ fieldCoframe f=0 ∧ fieldLorentz f=0 ∧
      fieldGravityB f=0 ∧ fieldMultiplier f=0 ∧ fieldGaugeB f=0 := by
  have zero (i : Fin 289) (outside : (i.val < (73 : ℕ)) ∨ ((121 : ℕ) ≤ i.val)) :
      sourceFiniteOriginRemainderPart imaginary branch epsilon s n i=0 := by
    rw [sourceFiniteOriginRemainderPart,sourceFiniteOriginRemainder_outside _ _ _ _ i outside]
    cases imaginary <;> rfl
  have scalar (j : Fin 9) := zero (scalarSlot j) (by simp only [scalarSlot,Fin.val_mk];omega)
  have gauge (mu : Fin 4) (a : Fin 12) := zero (gaugeSlot mu a) (by simp only [gaugeSlot,Fin.val_mk];omega)
  have coframe (a mu : Fin 4) := zero (coframeSlot a mu) (by simp only [coframeSlot,Fin.val_mk];omega)
  have lorentz (mu : Fin 4) (a : Fin 6) := zero (lorentzSlot mu a) (by simp only [lorentzSlot,Fin.val_mk];omega)
  have gravity (pair a : Fin 6) := zero (gravitySlot pair a) (by simp only [gravitySlot,Fin.val_mk];omega)
  have multiplier (pair a : Fin 6) := zero (multiplierSlot pair a) (by simp only [multiplierSlot,Fin.val_mk];omega)
  have auxiliary (pair : Fin 6) (a : Fin 12) := zero (gaugeBSlot pair a) (by simp only [gaugeBSlot,Fin.val_mk];omega)
  simp only []
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [fieldScalar,scalar,zero_smul,Finset.sum_const_zero]
  · funext mu
    simp only [fieldGauge,gauge,zero_smul,Finset.sum_const_zero,Pi.zero_apply]
  · exact funext fun a=>funext fun mu=>coframe a mu
  · exact funext fun mu=>funext fun a=>lorentz mu a
  · exact funext fun pair=>funext fun a=>gravity pair a
  · exact funext fun pair=>funext fun a=>multiplier pair a
  · exact funext fun pair=>funext fun a=>auxiliary pair a

/-- The original action-field reader itself, before any Hamiltonian or mixed-Hessian restriction, discards exactly this generated remainder. -/
theorem sourceFiniteOriginPart_field (imaginary : Bool) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    PreparationVacuumMixedFieldReturn.sourceField (sourceFiniteOriginPart imaginary branch epsilon s n)=
      PreparationVacuumMixedFieldReturn.sourceField (sourceOriginPart imaginary (sourceFiniteOriginAmplitude branch epsilon s n) • sourceNativeOriginReal 0) := by
  have zero:=sourceFiniteOriginRemainder_fields imaginary branch epsilon s n
  rw [sourceFiniteOriginPart_decomposition]
  unfold PreparationVacuumMixedFieldReturn.sourceField
  congr 1
  · have add (f g : Field289) : fieldCoframe (f+g)=fieldCoframe f+fieldCoframe g := rfl
    rw [add,zero.2.2.1,add_zero]
  · have add (f g : Field289) : fieldLorentz (f+g)=fieldLorentz f+fieldLorentz g := rfl
    rw [add,zero.2.2.2.1,add_zero]
  · funext mu
    rw [fieldGauge_add,zero.2.1]
    simp only [Pi.zero_apply,add_zero]
  · rw [fieldScalar_add,zero.1,add_zero]

end LowEnergy.PreparationPhysicalFiniteOriginCovariance
