import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate.Rotation

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
open Propagation.Interface Load.Source Fixed Contraction
open scoped Matrix
noncomputable section

def ordinaryRootRotatedQ (a b : Basis) (ordered : a < b) : MatrixQ LoadPrimitive.NativeIndex LoadPrimitive.NativeIndex :=
  rotateQ (qkron (onePCQ a b ordered) freeEnvironmentQ) (rootOrdinaryQ a b ordered)

theorem ordinary_root_rotated (a b : Basis) (ordered : a < b) :
    (Spec.rotatedRoot computedRootQ).submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b)=ordinaryRootRotatedQ a b ordered := by
  have kept : Preserves pceOrbit (qvalue computedRootQ) := by rw [computedRootQ_value]; exact finite_root_preserves
  have h := rotateQ_source s(a,b) (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne) computedRootQ kept
  have address : (fun i => (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne i).val)=Scaled.Order.orbitPCE a b := rfl
  rw [address,ordinary_free_restriction a b ordered,ordinary_root_restriction a b ordered] at h
  exact h

def diagonalRootRotatedQ (a : Fin 97) : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  rotateQ (qkron (oneDiagonalQ a.castSucc) freeEnvironmentQ) (rootDiagonalQ a)

theorem diagonal_root_rotated (a : Fin 97) :
    (Spec.rotatedRoot computedRootQ).submatrix (Scaled.Order.diagonalPCE a.castSucc) (Scaled.Order.diagonalPCE a.castSucc)=diagonalRootRotatedQ a := by
  have kept : Preserves pceOrbit (qvalue computedRootQ) := by rw [computedRootQ_value]; exact finite_root_preserves
  have h := rotateQ_source s(a.castSucc,a.castSucc) (Scaled.Order.diagonalPCEEquiv a.castSucc) computedRootQ kept
  have address : (fun i => (Scaled.Order.diagonalPCEEquiv a.castSucc i).val)=Scaled.Order.diagonalPCE a.castSucc := rfl
  have root : computedRootQ.submatrix (Scaled.Order.diagonalPCE a.castSucc) (Scaled.Order.diagonalPCE a.castSucc)=rootDiagonalQ a := by
    apply qvalue_injective
    rw [qvalue_submatrix,computedRootQ_value,rootDiagonalQ_value]
  rw [address,diagonal_free_restriction,root] at h
  exact h

def donorRootRotatedQ : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  rotateQ (qkron (oneDiagonalQ 97) freeEnvironmentQ) rootDonorQ

theorem donor_root_rotated :
    (Spec.rotatedRoot computedRootQ).submatrix (Scaled.Order.diagonalPCE 97) (Scaled.Order.diagonalPCE 97)=donorRootRotatedQ := by
  have kept : Preserves pceOrbit (qvalue computedRootQ) := by rw [computedRootQ_value]; exact finite_root_preserves
  have h := rotateQ_source s((97 : Basis),97) (Scaled.Order.diagonalPCEEquiv 97) computedRootQ kept
  have address : (fun i => (Scaled.Order.diagonalPCEEquiv 97 i).val)=Scaled.Order.diagonalPCE 97 := rfl
  have root : computedRootQ.submatrix (Scaled.Order.diagonalPCE 97) (Scaled.Order.diagonalPCE 97)=rootDonorQ := by
    apply qvalue_injective
    rw [qvalue_submatrix,computedRootQ_value,rootDonorQ_value]
  rw [address,diagonal_free_restriction,root] at h
  exact h

def ordinaryComplementRotatedQ (a b : Basis) (ordered : a < b) : MatrixQ LoadPrimitive.NativeIndex LoadPrimitive.NativeIndex :=
  rotateQ (qkron (onePCQ a b ordered) freeEnvironmentQ) (complementOrdinaryQ a b ordered)

theorem ordinary_complement_rotated (a b : Basis) (ordered : a < b) :
    (Spec.rotatedRoot computedComplementQ).submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b)=ordinaryComplementRotatedQ a b ordered := by
  have kept : Preserves pceOrbit (qvalue computedComplementQ) := by rw [computedComplementQ_value]; exact finite_complement_preserves
  have h := rotateQ_source s(a,b) (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne) computedComplementQ kept
  have address : (fun i => (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne i).val)=Scaled.Order.orbitPCE a b := rfl
  rw [address,ordinary_free_restriction a b ordered,ordinary_complement_restriction a b ordered] at h
  exact h

def diagonalComplementRotatedQ (a : Fin 97) : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  rotateQ (qkron (oneDiagonalQ a.castSucc) freeEnvironmentQ) (complementDiagonalQ a)

theorem diagonal_complement_rotated (a : Fin 97) :
    (Spec.rotatedRoot computedComplementQ).submatrix (Scaled.Order.diagonalPCE a.castSucc) (Scaled.Order.diagonalPCE a.castSucc)=diagonalComplementRotatedQ a := by
  have kept : Preserves pceOrbit (qvalue computedComplementQ) := by rw [computedComplementQ_value]; exact finite_complement_preserves
  have h := rotateQ_source s(a.castSucc,a.castSucc) (Scaled.Order.diagonalPCEEquiv a.castSucc) computedComplementQ kept
  have address : (fun i => (Scaled.Order.diagonalPCEEquiv a.castSucc i).val)=Scaled.Order.diagonalPCE a.castSucc := rfl
  have root : computedComplementQ.submatrix (Scaled.Order.diagonalPCE a.castSucc) (Scaled.Order.diagonalPCE a.castSucc)=complementDiagonalQ a := by
    apply qvalue_injective
    rw [qvalue_submatrix,computedComplementQ_value,complementDiagonalQ_value]
  rw [address,diagonal_free_restriction,root] at h
  exact h

def donorComplementRotatedQ : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  rotateQ (qkron (oneDiagonalQ 97) freeEnvironmentQ) complementDonorQ

theorem donor_complement_rotated :
    (Spec.rotatedRoot computedComplementQ).submatrix (Scaled.Order.diagonalPCE 97) (Scaled.Order.diagonalPCE 97)=donorComplementRotatedQ := by
  have kept : Preserves pceOrbit (qvalue computedComplementQ) := by rw [computedComplementQ_value]; exact finite_complement_preserves
  have h := rotateQ_source s((97 : Basis),97) (Scaled.Order.diagonalPCEEquiv 97) computedComplementQ kept
  have address : (fun i => (Scaled.Order.diagonalPCEEquiv 97 i).val)=Scaled.Order.diagonalPCE 97 := rfl
  have root : computedComplementQ.submatrix (Scaled.Order.diagonalPCE 97) (Scaled.Order.diagonalPCE 97)=complementDonorQ := by
    apply qvalue_injective
    rw [qvalue_submatrix,computedComplementQ_value,complementDonorQ_value]
  rw [address,diagonal_free_restriction,root] at h
  exact h

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
