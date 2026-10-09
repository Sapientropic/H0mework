import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.StateResponse.Transfer
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.StateResponse.Native

/-! Finite momentum transfer words act on all sectors before the incoming
zero block is returned to the same original mother operator and Stage10 state. -/
set_option autoImplicit false
open scoped Matrix InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.StateResponse
open QuantizationCheck.Fermion Fermion StateGreen ProofFreeRicherAnholonomicSource
open YangMills.FullPairing
noncomputable section
variable {ι : Type*} [Fintype ι]

abbrev zeroBlock (A : Matrix (Fin 3×ι) (Fin 3×ι) ℂ) : Matrix ι ι ℂ :=
  fun i j => A (0,i) (0,j)

theorem zeroBlock_pair (A : Matrix (Fin 3×ι) (Fin 3×ι) ℂ) (w : ι → ℂ) :
    modePair (modeVector 0 w) (A*ᵥmodeVector 0 w)=modePair w (zeroBlock A*ᵥw) := by
  simp [modePair,modeVector,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,zeroBlock,Fin.sum_univ_three]

attribute [local instance] transferIndexOrder

def transferCompression (word : Module.End ℂ (Fock (Fin 3×ι))) : Matrix ι ι ℂ :=
  zeroBlock (PreparedWeight.wholeCompression word)

theorem transferCompression_read (word : Module.End ℂ (Fock (Fin 3×ι))) (w : ι → ℂ) :
    read (modeVector 0 w) word=modePair w (transferCompression word*ᵥw) := by
  change pairing (oneParticle (modeVector 0 w)) (word (oneParticle (modeVector 0 w)))=_
  rw [← PreparedWeight.wholeCompression_pair]
  exact zeroBlock_pair _ _

local instance : DecidableEq Quantum.Index := Classical.decEq _

def transferMother (word : Module.End ℂ (Fock (Fin 3×Quantum.Index))) : Mother :=
  Quantum.operatorMatrix.toLinearEquiv.symm (transferCompression word)

def transferNativeRead (point : BasePoint) (word : Module.End ℂ (Fock (Fin 3×Quantum.Index))) : ℂ :=
  Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer point)
    (Stage9DEF.Compatibility.responseMatrix (pairedMother 1 (transferMother word)))

theorem transferMother_pair (point : BasePoint) (word : Module.End ℂ (Fock (Fin 3×Quantum.Index))) :
    read (modeVector 0 (preparedVector point)) word=
      inner ℂ (prepared point) (operator (transferMother word) (prepared point)) := by
  rw [transferCompression_read,← preparedMatter_original point,operator_coordinates,
    natural_inner,← Quantum.coordinatePair_full]
  change modePair (preparedVector point) (transferCompression word*ᵥpreparedVector point)=
    modePair (preparedVector point) (Quantum.coordinates (transferMother word (preparedMatter point)))
  rw [← Quantum.matrix_action]
  have restored : Quantum.operatorMatrix (transferMother word)=transferCompression word :=
    Quantum.operatorMatrix.toLinearEquiv.apply_symm_apply _
  rw [restored]
  rfl

theorem transferNativeRead_generated (point : BasePoint)
    (word : Module.End ℂ (Fock (Fin 3×Quantum.Index))) :
    transferNativeRead point word=read (modeVector 0 (preparedVector point)) word := by
  rw [transferNativeRead,source_gram,transferMother_pair]
  congr 1
  simp [operator]

theorem source_transfer_response (point : BasePoint) (T B Rplus Rminus : SourceMatrix) :
    transferNativeRead point
      (connectedWord (modeVector 0 (preparedVector point)) (transferReader B Rplus Rminus) (transferForce T)-
        connectedWord (modeVector 0 (preparedVector point)) (transferForce T) (transferReader B Rplus Rminus))=
      modePair (preparedVector point) ((B*Rplus*T)*ᵥpreparedVector point)-
        modePair (preparedVector point) ((T*Rminus*B)*ᵥpreparedVector point) := by
  rw [transferNativeRead_generated]
  exact transfer_response _ _ _ _ _

theorem transfer_source_unit (point : BasePoint) :
    modePair (modeVector 0 (preparedVector point)) (modeVector 0 (preparedVector point))=1 := by
  rw [modeVector_pair,if_pos rfl,preparedVector_unit]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.StateResponse
