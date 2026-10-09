import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.FullAlgebra
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Received

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Spec
open Propagation.Interface Load.Source Collision
open scoped Matrix
noncomputable section

-- Products here specify the original whole carrier; numerical evaluation uses its proved small restrictions.
def free : MatrixQ (PairController × Fin 2) (PairController × Fin 2) := qkron computedPCQ freeEnvironmentQ
def parent : MatrixQ (PairController × Fin 2) (PairController × Fin 2) := qkron computedParentPCQ (qidentity (Fin 2))
def recovery : MatrixQ (PairController × Fin 2) (PairController × Fin 2) := qkron computedRecoveryPCQ recoveryEnvironmentQ
def receivedWord : MatrixQ (PairController × Fin 2) (PairController × Fin 2) := qmultiply (qmultiply recovery computedLoadQ) parent

def sharedPC : MatrixQ (PairController × PairController) (PairController × PairController) := qkron computedPCQ computedPCQ
def supply : MatrixQ Current.FullIndex Current.FullIndex :=
  qkron (qmultiply sharedPC (partialSwapQ PairController SquareRoot.Full.cosine SquareRoot.Full.sine)) freeEnvironmentQ
def weak : MatrixQ Current.FullIndex Current.FullIndex :=
  qkron (qmultiply sharedPC (partialSwapQ PairController SquareRoot.Full.sine SquareRoot.Full.cosine)) freeEnvironmentQ
def load : MatrixQ Current.FullIndex Current.FullIndex := localMatrixQ computedLoadQ computedPCQ

theorem free_value : qvalue free=PCExecution.free := by
  simp only [free,qvalue_kron,computedPCQ_value,freeEnvironmentQ_value,PCExecution.free]

theorem parent_value : qvalue parent=PCExecution.parent := by
  simp only [parent,qvalue_kron,computedParentPCQ_value,qvalue_identity,PCExecution.parent]

theorem recovery_value : qvalue recovery=PCExecution.recovery := by
  simp only [recovery,qvalue_kron,computedRecoveryPCQ_value,recoveryEnvironmentQ_value,PCExecution.recovery]

theorem receivedWord_value : qvalue receivedWord=LoadExecution.receivedWord := by
  simp only [receivedWord,qvalue_multiply,recovery_value,computedLoadQ_value,parent_value,LoadExecution.receivedWord]

theorem sharedPC_value : qvalue sharedPC=PCExecution.sharedPC := by
  simp only [sharedPC,qvalue_kron,computedPCQ_value,PCExecution.sharedPC]

theorem supply_value : qvalue supply=PCExecution.supply := by
  simp only [supply,qvalue_kron,qvalue_multiply,sharedPC_value,partialSwapQ_value,
    SquareRoot.Full.cosine_cast,SquareRoot.Full.sine_cast,freeEnvironmentQ_value,
    PCExecution.supply,Supply.nativeExchangePolynomial]

theorem weak_value : qvalue weak=PCExecution.weak := by
  simp only [weak,qvalue_kron,qvalue_multiply,sharedPC_value,partialSwapQ_value,
    SquareRoot.Full.cosine_cast,SquareRoot.Full.sine_cast,freeEnvironmentQ_value,
    PCExecution.weak,Supply.weakExchangePolynomial]

theorem load_value : qvalue load=LoadExecution.load := by
  simp only [load,localMatrixQ_value,computedLoadQ_value,computedPCQ_value,LoadExecution.load]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Spec
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
