import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeCurrent.SourceFlow
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeCurrent.Reader

/-! A true finite-coframe current family generates its boundary, both
propagating legs and local primitive-contact terms in a single derivative. -/
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeCurrent
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open StateGreen CoframeResponse QuantizationCheck.Fermion Fermion
noncomputable section
attribute [local instance] Fermion.fullIndexOrder
local instance currentIndex : DecidableEq Quantum.Index := Classical.decEq _
local instance currentReal : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _

def matrixReadLinear (w : Quantum.Index → ℂ) : SourceMatrix →ₗ[ℂ] ℂ where
  toFun M := modePair w (M*ᵥw)
  map_add' A B := by simp [Matrix.add_mulVec,modePair,mul_add,Finset.sum_add_distrib]
  map_smul' c A := by simp [Matrix.smul_mulVec,modePair_smul_right]

def matrixRead (w : Quantum.Index → ℂ) : SourceMatrix →L[ℂ] ℂ where
  toLinearMap := matrixReadLinear w
  cont := by
    change Continuous (fun M : SourceMatrix => modePair w (M*ᵥw))
    unfold modePair Matrix.mulVec dotProduct
    fun_prop

def currentMatrix (point : BasePoint) (k : Fin 3 → ℝ) (reader : LorentzianCoframe)
    (t : ℝ) (e : LorentzianCoframe) : SourceMatrix :=
  weightMatrix e*primalMatrix (coframeConfiguration e) point k (-t)*currentForce point k reader e*
    primalMatrix (coframeConfiguration e) point k t

def currentMatrixDirection (point : BasePoint) (k : Fin 3 → ℝ)
    (direction reader : LorentzianCoframe) (t : ℝ) : SourceMatrix :=
  weightDirection point direction*primalMatrix actual point k (-t)*currentForce point k reader (actual.coframe point)*
      primalMatrix actual point k t+
    weightMatrix (actual.coframe point)*sourceFlowVariation point k direction (-t)*
      currentForce point k reader (actual.coframe point)*primalMatrix actual point k t+
    weightMatrix (actual.coframe point)*primalMatrix actual point k (-t)*
      currentForceDirection point k direction reader*primalMatrix actual point k t+
    weightMatrix (actual.coframe point)*primalMatrix actual point k (-t)*
      currentForce point k reader (actual.coframe point)*sourceFlowVariation point k direction t

theorem currentMatrix_parameter (point : BasePoint) (k : Fin 3 → ℝ)
    (direction reader : LorentzianCoframe) (t : ℝ) :
    HasDerivAt (fun epsilon => currentMatrix point k reader t (coframePath point direction epsilon))
      (currentMatrixDirection point k direction reader t) 0 := by
  have generated := (((weight_parameter point direction).mul (original_flow_parameter point k direction (-t))).mul
    (currentForce_parameter point k direction reader)).mul (original_flow_parameter point k direction t)
  unfold currentMatrix currentMatrixDirection
  simp only [Pi.mul_apply,coframePath_zero,coframeConfiguration_actual] at generated
  convert! generated using 1
  simp only [Matrix.add_mul,add_assoc]

def currentWord (point : BasePoint) (k : Fin 3 → ℝ) (reader : LorentzianCoframe)
    (t : ℝ) (e : LorentzianCoframe) : Module.End ℂ (Fock Quantum.Index) :=
  quantize (weightMatrix e)*quantize (primalMatrix (coframeConfiguration e) point k (-t)*
    currentForce point k reader e*primalMatrix (coframeConfiguration e) point k t)

theorem currentWord_read (point : BasePoint) (k : Fin 3 → ℝ) (reader : LorentzianCoframe)
    (t : ℝ) (e : LorentzianCoframe) :
    read (preparedVector point) (currentWord point k reader t e)=
      matrixRead (preparedVector point) (currentMatrix point k reader t e) := by
  rw [currentWord,StateResponse.read_four_word]
  change _=modePair (preparedVector point) (currentMatrix point k reader t e*ᵥpreparedVector point)
  simp only [currentMatrix,Matrix.mul_assoc]

def currentValue (point : BasePoint) (k : Fin 3 → ℝ) (reader : LorentzianCoframe)
    (t : ℝ) (e : LorentzianCoframe) : ℂ :=
  -4*read (preparedVector point) (currentWord point k reader t e)

def currentResponse (point : BasePoint) (k : Fin 3 → ℝ)
    (direction reader : LorentzianCoframe) (t : ℝ) : ℂ :=
  -4*matrixRead (preparedVector point) (currentMatrixDirection point k direction reader t)

theorem currentValue_parameter (point : BasePoint) (k : Fin 3 → ℝ)
    (direction reader : LorentzianCoframe) (t : ℝ) :
    HasDerivAt (fun epsilon => currentValue point k reader t (coframePath point direction epsilon))
      (currentResponse point k direction reader t) 0 := by
  have generated := ((matrixRead (preparedVector point)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (currentMatrix_parameter point k direction reader t)
  have multiplied := generated.const_mul (-4 : ℂ)
  simp only [currentValue,currentWord_read,currentResponse]
  exact multiplied

theorem real_current_parameter (point : BasePoint) (k : Fin 3 → ℝ)
    (direction reader : LorentzianCoframe) (t : ℝ) :
    HasDerivAt (fun epsilon => (currentValue point k reader t (coframePath point direction epsilon)).re)
      (currentResponse point k direction reader t).re 0 :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (currentValue_parameter point k direction reader t)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeCurrent
