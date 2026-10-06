import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeCurrent.Current

/-! The derivative is of the original independent-dual current family.
The whole boundary-weighted CAR response word returns to the same Stage10. -/
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeCurrent
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open StateGreen CoframeResponse QuantizationCheck.Fermion Fermion YangMills.FullPairing
open DiracExteriorMatterAction
noncomputable section
attribute [local instance] Fermion.fullIndexOrder
local instance nativeIndex : DecidableEq Quantum.Index := Classical.decEq _

def currentInsertion (point : BasePoint) (k : Fin 3 → ℝ) (reader : LorentzianCoframe)
    (e : LorentzianCoframe) : Mother :=
  Quantum.operatorMatrix.toLinearEquiv.symm (onShellCurrent point k reader e)

theorem currentInsertion_matrix (point : BasePoint) (k : Fin 3 → ℝ) (reader e : LorentzianCoframe) :
    Quantum.operatorMatrix (currentInsertion point k reader e)=onShellCurrent point k reader e :=
  Quantum.operatorMatrix.toLinearEquiv.apply_symm_apply _

theorem currentForce_original (point : BasePoint) (k : Fin 3 → ℝ) (reader e : LorentzianCoframe)
    (regular : StageNineCurrentCoframeMatterTemporalPrincipal.coframeTemporalPrincipalScalar e≠0) :
    Quantum.operatorMatrix (temporalForce (coframeConfiguration e) point (currentInsertion point k reader e))=
      currentForce point k reader e := by
  simp only [temporalForce,coframeConfiguration,map_smul,Quantum.matrix_composition,currentInsertion_matrix]
  rw [← principal_inverse_original e regular]
  rfl

theorem currentWord_original (point : BasePoint) (k : Fin 3 → ℝ) (reader e : LorentzianCoframe)
    (regular : StageNineCurrentCoframeMatterTemporalPrincipal.coframeTemporalPrincipalScalar e≠0) (t : ℝ) :
    boundaryWord (coframeConfiguration e) point k t (currentInsertion point k reader e)=
      currentWord point k reader t e := by
  simp only [boundaryWord,Quantum.matrix_composition,currentForce_original point k reader e regular]
  rw [← weightMatrix_original point e]
  change _=quantize (weightMatrix e)*quantize
    (primalMatrix (coframeConfiguration e) point k (-t)*currentForce point k reader e*
      primalMatrix (coframeConfiguration e) point k t)
  rw [Matrix.mul_assoc]
  rfl

def rawCurrent (point : BasePoint) (k : Fin 3 → ℝ) (reader : LorentzianCoframe)
    (t : ℝ) (e : LorentzianCoframe) : ℂ :=
  ((|e.det| : ℝ) : ℂ)*canonicalDual (coframeConfiguration e) point k t (actual.conjugateMatter point)
    (currentInsertion point k reader e (primal (coframeConfiguration e) point k t (actual.matter point)))

theorem rawCurrent_generated (point : BasePoint) (k : Fin 3 → ℝ) (reader e : LorentzianCoframe)
    (regular : StageNineCurrentCoframeMatterTemporalPrincipal.coframeTemporalPrincipalScalar e≠0) (t : ℝ) :
    rawCurrent point k reader t e=currentValue point k reader t e := by
  have generated := original_dual_full_CAR (coframeConfiguration e) point k t (currentInsertion point k reader e)
  rw [currentWord_original point k reader e regular t] at generated
  exact generated

theorem rawCurrent_parameter (point : BasePoint) (k : Fin 3 → ℝ)
    (direction reader : LorentzianCoframe) (t : ℝ) :
    HasDerivAt (fun epsilon => rawCurrent point k reader t (coframePath point direction epsilon))
      (currentResponse point k direction reader t) 0 := by
  apply (currentValue_parameter point k direction reader t).congr_of_eventuallyEq
  filter_upwards [coframePath_eventually_noncharacteristic point direction] with epsilon regular
  exact rawCurrent_generated point k reader (coframePath point direction epsilon) regular t

def responseWord (point : BasePoint) (k : Fin 3 → ℝ) (direction reader : LorentzianCoframe)
    (t : ℝ) : Module.End ℂ (Fock Quantum.Index) :=
  quantize (weightDirection point direction)*quantize (primalMatrix actual point k (-t)*
      currentForce point k reader (actual.coframe point)*primalMatrix actual point k t)+
    quantize (weightMatrix (actual.coframe point))*quantize (sourceFlowVariation point k direction (-t)*
      currentForce point k reader (actual.coframe point)*primalMatrix actual point k t)+
    quantize (weightMatrix (actual.coframe point))*quantize (primalMatrix actual point k (-t)*
      currentForceDirection point k direction reader*primalMatrix actual point k t)+
    quantize (weightMatrix (actual.coframe point))*quantize (primalMatrix actual point k (-t)*
      currentForce point k reader (actual.coframe point)*sourceFlowVariation point k direction t)

theorem responseWord_read (point : BasePoint) (k : Fin 3 → ℝ) (direction reader : LorentzianCoframe)
    (t : ℝ) :
    read (preparedVector point) (responseWord point k direction reader t)=
      matrixRead (preparedVector point) (currentMatrixDirection point k direction reader t) := by
  simp only [responseWord,map_add,StateResponse.read_four_word,currentMatrixDirection,Matrix.mul_assoc]
  rfl

theorem rawCurrent_parameter_native (point : BasePoint) (k : Fin 3 → ℝ)
    (direction reader : LorentzianCoframe) (t : ℝ) :
    HasDerivAt (fun epsilon => rawCurrent point k reader t (coframePath point direction epsilon))
      (-4*Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer point)
        (Stage9DEF.Compatibility.responseMatrix (pairedMother 1
          (sourceWordMother (responseWord point k direction reader t))))) 0 := by
  rw [source_word_readback,responseWord_read]
  exact rawCurrent_parameter point k direction reader t

theorem rawRealCurrent_parameter_native (point : BasePoint) (k : Fin 3 → ℝ)
    (direction reader : LorentzianCoframe) (t : ℝ) :
    HasDerivAt (fun epsilon => (rawCurrent point k reader t (coframePath point direction epsilon)).re)
      (-4*Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer point)
        (Stage9DEF.Compatibility.responseMatrix (pairedMother 1
          (sourceWordMother (responseWord point k direction reader t))))).re 0 :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (rawCurrent_parameter_native point k direction reader t)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeCurrent
