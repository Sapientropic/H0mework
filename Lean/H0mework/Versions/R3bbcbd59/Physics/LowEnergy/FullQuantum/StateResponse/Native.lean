import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.StateResponse.Transport
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.StateResponse.Impulse

/-! The connected full word and the derivative of an actual Fock pulse return
through the original Stage10 reader only after complete composition. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.StateResponse
open QuantizationCheck.Fermion Fermion StateGreen ProofFreeRicherAnholonomicSource
open YangMills.FullPairing
noncomputable section
attribute [local instance] Fermion.fullIndexOrder
local instance : Fintype (Finset Quantum.Index) := Fintype.ofFinite _
local instance : CompleteSpace (Fock Quantum.Index) :=
  inferInstanceAs (CompleteSpace (Finset Quantum.Index → ℂ))
local instance : NormedAlgebra ℚ (Fock Quantum.Index →L[ℂ] Fock Quantum.Index) :=
  NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (Fock Quantum.Index →L[ℂ] Fock Quantum.Index) :=
  NormedAlgebra.restrictScalars ℝ ℂ _

def sourceConnectedWord (point : BasePoint) (momentum : Fin 3 → ℝ) (t s : ℝ) (A B : SourceMatrix) :
    Module.End ℂ (Fock Quantum.Index) :=
  sourceObservable point momentum t A*sourceObservable point momentum s B-
    read (preparedVector point) (sourceObservable point momentum s B) • sourceObservable point momentum t A

theorem sourceConnectedWord_read (point : BasePoint) (momentum : Fin 3 → ℝ) (t s : ℝ) (A B : SourceMatrix) :
    read (preparedVector point) (sourceConnectedWord point momentum t s A B)=
      sourceConnected point momentum t s A B := by
  rw [sourceConnectedWord,map_sub,map_smul]
  simp only [sourceConnected,smul_eq_mul]
  congr 1
  exact mul_comm _ _

def sourceReader (point : BasePoint) (word : Module.End ℂ (Fock Quantum.Index)) : ℂ :=
  Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer point)
    (Stage9DEF.Compatibility.responseMatrix (pairedMother 1 (sourceWordMother word)))

theorem sourceReader_generated (point : BasePoint) (word : Module.End ℂ (Fock Quantum.Index)) :
    sourceReader point word=read (preparedVector point) word := source_word_readback point word

theorem sourceConnected_native (point : BasePoint) (momentum : Fin 3 → ℝ) (t s : ℝ) (A B : SourceMatrix) :
    sourceReader point (sourceConnectedWord point momentum t s A B)=
      Matrix.trace (occupation point*heisenberg point momentum t A*(1-occupation point)*
        heisenberg point momentum s B) := by
  rw [sourceReader_generated,sourceConnectedWord_read]
  exact sourceConnected_generated point momentum t s A B

section Boundary
local instance : DecidableEq Quantum.Index := Classical.decEq _

theorem sourceConnected_boundary (point : BasePoint) (momentum : Fin 3 → ℝ) (t s : ℝ) (A B : SourceMatrix) :
    sourceConnected point momentum t s A B=
      PreparedWeight.boundaryDeterminant (preparedVector point)
        (PreparedWeight.wholeCompression (sourceConnectedWord point momentum t s A B)) := by
  rw [← sourceConnectedWord_read]
  exact source_word_boundary point _
end Boundary

def sourcePulseRead (point : BasePoint) (momentum : Fin 3 → ℝ) (t s : ℝ)
    (R B : SourceMatrix) (epsilon : ℝ) : ℂ :=
  sourceReader point (pulseObservable (heisenberg point momentum s R)
    (heisenberg point momentum t B) epsilon).toLinearMap

theorem sourcePulseRead_generated (point : BasePoint) (momentum : Fin 3 → ℝ) (t s : ℝ)
    (R B : SourceMatrix) (epsilon : ℝ) :
    sourcePulseRead point momentum t s R B epsilon=
      pulseRead (preparedVector point) (heisenberg point momentum s R)
        (heisenberg point momentum t B) epsilon := by
  exact sourceReader_generated point _

theorem sourcePulseRead_derivative (point : BasePoint) (momentum : Fin 3 → ℝ) (t s : ℝ)
    (R B : SourceMatrix) :
    HasDerivAt (sourcePulseRead point momentum t s R B)
      (sourceReader point (sourceKuboWord point momentum t s R B)) 0 := by
  have generated := pulseRead_derivative (preparedVector point)
    (heisenberg point momentum s R) (heisenberg point momentum t B)
  have identity : sourcePulseRead point momentum t s R B=
      pulseRead (preparedVector point) (heisenberg point momentum s R) (heisenberg point momentum t B) :=
    funext (sourcePulseRead_generated point momentum t s R B)
  rw [identity,sourceReader_generated]
  simpa only [sourceKuboWord,sourceObservable_generated,kuboWord] using generated

theorem sourcePulseRead_connected (point : BasePoint) (momentum : Fin 3 → ℝ) (t s : ℝ)
    (R B : SourceMatrix) :
    HasDerivAt (sourcePulseRead point momentum t s R B)
      (Complex.I*(sourceConnected point momentum s t R B-sourceConnected point momentum t s B R)) 0 := by
  rw [← sourceKubo_generated,← sourceReader_generated]
  exact sourcePulseRead_derivative point momentum t s R B

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.StateResponse
