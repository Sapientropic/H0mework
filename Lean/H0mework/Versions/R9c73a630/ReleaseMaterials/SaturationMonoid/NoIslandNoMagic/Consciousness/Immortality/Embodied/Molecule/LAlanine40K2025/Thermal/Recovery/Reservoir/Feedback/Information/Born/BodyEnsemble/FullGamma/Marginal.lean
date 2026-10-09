import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BodyEnsemble.Value.Holevo
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime.PointerReadouts

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble

open PhyslibCoherence
open scoped Matrix ComplexOrder
noncomputable section
attribute [local irreducible] Current.loadPulse Current.pulse Live.State.joint
  sourceTarget receivedState firstState

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pointer_marginal_of_state (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1) :
    ((matrixState rho positive normalized).relabel pointerIncidence.symm).traceLeft.m =
      Powered.Dynamics.controllerReduce
        (rho.submatrix pointerIncidence.symm pointerIncidence.symm) := by
  ext i j
  rfl

theorem body_marginal_of_state (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1) :
    ((matrixState rho positive normalized).relabel pointerIncidence.symm).traceRight.m =
      bodyRead rho := by
  ext i j
  change (∑ a : Fin 2, rho (pointerIncidence.symm (i, a))
    (pointerIncidence.symm (j, a))) = _
  simp [bodyRead, Fin.sum_univ_two, pointerIncidence]
  rfl

def originalQuantumJoint : MState PointerIndex :=
  matrixState receivedState.joint receivedState.positive receivedState.normalized

def originalQuantumProduct : MState (Current.FullIndex × Fin 2) :=
  originalQuantumJoint.relabel pointerIncidence.symm

theorem originalQuantumProduct_pointer :
    originalQuantumProduct.traceLeft.m =
      Pointer.Runtime.pointerMatrix receivedState.joint := by
  exact pointer_marginal_of_state _ _ _

theorem originalQuantumProduct_body :
    originalQuantumProduct.traceRight.m = bodyRead receivedState.joint := by
  exact body_marginal_of_state _ _ _

theorem originalQuantumProduct_body_state :
    originalQuantumProduct.traceRight = originalQuantumBody := by
  apply MState.ext_m
  rw [originalQuantumProduct_body]
  rfl

def originalQuantumPointer : MState (Fin 2) :=
  matrixState (Pointer.Runtime.pointerMatrix receivedState.joint)
    (Pointer.Runtime.pointerMatrix_positive receivedState)
    (Pointer.Runtime.pointerMatrix_trace receivedState)

theorem originalQuantumProduct_pointer_state :
    originalQuantumProduct.traceLeft = originalQuantumPointer := by
  apply MState.ext_m
  rw [originalQuantumProduct_pointer]
  rfl

omit [DecidableEq ι] in
private theorem pointer_matrix_diag_zero (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    (Powered.Dynamics.controllerReduce
      (rho.submatrix pointerIncidence.symm pointerIncidence.symm)) 0 0 =
      rho.toBlocks₁₁.trace := by
  change (∑ i : ι, rho (Sum.inl i) (Sum.inl i)) = _
  rfl

omit [DecidableEq ι] in
private theorem pointer_matrix_diag_one (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    (Powered.Dynamics.controllerReduce
      (rho.submatrix pointerIncidence.symm pointerIncidence.symm)) 1 1 =
      rho.toBlocks₂₂.trace := by
  change (∑ i : ι, rho (Sum.inr i) (Sum.inr i)) = _
  rfl

theorem originalQuantumPointer_weights :
    originalQuantumPointer.m 0 0 = (p0 : ℂ) ∧
      originalQuantumPointer.m 1 1 = (p1 : ℂ) := by
  constructor
  · rw [show originalQuantumPointer.m 0 0 =
        (Pointer.Runtime.pointerMatrix receivedState.joint) 0 0 from rfl]
    exact (pointer_matrix_diag_zero receivedState.joint).trans (by
      simpa only [sigma0, Resource.loadBlock] using sigma0_trace)
  · rw [show originalQuantumPointer.m 1 1 =
        (Pointer.Runtime.pointerMatrix receivedState.joint) 1 1 from rfl]
    exact (pointer_matrix_diag_one receivedState.joint).trans (by
      simpa only [sigma1, Resource.suppliedBlock] using sigma1_trace)

theorem originalQuantumMutualInformation_eq :
    qMutualInfo originalQuantumProduct =
      Quantum.spectralEntropy (Pointer.Runtime.pointerMatrix receivedState.joint)
        (Pointer.Runtime.pointerMatrix_positive receivedState)
        (Pointer.Runtime.pointerMatrix_trace receivedState) +
      Quantum.spectralEntropy (bodyRead receivedState.joint)
        original_body_positive original_body_trace -
      Quantum.spectralEntropy receivedState.joint receivedState.positive
        receivedState.normalized := by
  unfold qMutualInfo
  rw [originalQuantumProduct_pointer_state, originalQuantumProduct_body_state]
  rw [show Sᵥₙ originalQuantumProduct = Sᵥₙ originalQuantumJoint from
      Sᵥₙ_relabel _ _]
  simp only [originalQuantumPointer, originalQuantumBody, originalQuantumJoint,
    matrixState_entropy]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
