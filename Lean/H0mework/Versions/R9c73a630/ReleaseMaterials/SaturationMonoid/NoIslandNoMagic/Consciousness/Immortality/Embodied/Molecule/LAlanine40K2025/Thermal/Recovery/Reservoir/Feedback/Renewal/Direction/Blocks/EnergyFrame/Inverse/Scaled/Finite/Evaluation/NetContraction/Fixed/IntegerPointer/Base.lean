import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerRoot.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.ConcreteOrdinary.Energy
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix BigOperators Matrix.Norms.L2Operator

variable {α β : Type*}

def intNeg (A : MatrixInt α β) : MatrixInt α β := ⟨-A.re,-A.im⟩

def intFourBlocks (A B C D : MatrixInt α α) : MatrixInt (α ⊕ α) (α ⊕ α) :=
  ⟨Matrix.fromBlocks A.re B.re C.re D.re,
    Matrix.fromBlocks A.im B.im C.im D.im⟩

def bodyLiftIdentityInt [DecidableEq β] (A : MatrixInt (α × Fin 2) (α × Fin 2)) :
    MatrixInt (Leg α β) (Leg α β) :=
  ⟨fun i j => if i.1.2=j.1.2 then A.re (i.1.1,i.2) (j.1.1,j.2) else 0,
   fun i j => if i.1.2=j.1.2 then A.im (i.1.1,i.2) (j.1.1,j.2) else 0⟩

def donorLiftIdentityInt [DecidableEq α] (A : MatrixInt (β × Fin 2) (β × Fin 2)) :
    MatrixInt (Leg α β) (Leg α β) :=
  ⟨fun i j => if i.1.1=j.1.1 then A.re (i.1.2,i.2) (j.1.2,j.2) else 0,
   fun i j => if i.1.1=j.1.1 then A.im (i.1.2,i.2) (j.1.2,j.2) else 0⟩

def roleBlocksInt (A B : MatrixInt (Leg α β) (Leg α β)) :
    MatrixInt (Role α β) (Role α β) :=
  ⟨fun i j => match i,j with
      | (.inl x,e),(.inl y,f) => A.re (x,e) (y,f)
      | (.inr x,e),(.inr y,f) => B.re (x,e) (y,f)
      | _,_ => 0,
   fun i j => match i,j with
      | (.inl x,e),(.inl y,f) => A.im (x,e) (y,f)
      | (.inr x,e),(.inr y,f) => B.im (x,e) (y,f)
      | _,_ => 0⟩

variable [Fintype α]

def rotateInt (U R : MatrixInt α α) : MatrixInt α α :=
  multiply (multiply U R) (adjoint U)

def sourceFirstRootInt : MatrixInt LoadPrimitive.NativeIndex LoadPrimitive.NativeIndex :=
  submatrix (gramInt (SquareRoot.Full.allOrdinary (0 : Basis) (1 : Basis) (by decide)).1)
    tripleIndex tripleIndex

def sourceFirstComplementInt : MatrixInt LoadPrimitive.NativeIndex LoadPrimitive.NativeIndex :=
  submatrix (gramInt (SquareRoot.Full.allOrdinary (0 : Basis) (1 : Basis) (by decide)).2)
    tripleIndex tripleIndex

def sourceDonorRootInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  submatrix (gramInt SquareRoot.Full.paidDonor.1)
    SquareRoot.Full.pairIndex SquareRoot.Full.pairIndex

def sourceDonorComplementInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  submatrix (gramInt SquareRoot.Full.paidDonor.2)
    SquareRoot.Full.pairIndex SquareRoot.Full.pairIndex

def sourceFirstFreeInt : MatrixInt LoadPrimitive.NativeIndex LoadPrimitive.NativeIndex :=
  quantize (qkron (onePCQ (0 : Basis) (1 : Basis) (by decide)) freeEnvironmentQ)

def sourceDonorFreeInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  quantize (qkron (oneDiagonalQ 97) freeEnvironmentQ)

def sourceFirstRootRotatedInt := rotateInt sourceFirstFreeInt sourceFirstRootInt

def sourceFirstComplementRotatedInt := rotateInt sourceFirstFreeInt sourceFirstComplementInt

def sourceDonorRootRotatedInt := rotateInt sourceDonorFreeInt sourceDonorRootInt

def sourceDonorComplementRotatedInt := rotateInt sourceDonorFreeInt sourceDonorComplementInt

def sourceFirstRootRoleInt : MatrixInt OrdinaryFull OrdinaryFull :=
  roleBlocksInt
    (bodyLiftIdentityInt sourceFirstRootRotatedInt)
    (donorLiftIdentityInt sourceDonorRootRotatedInt)

def sourceFirstComplementRoleInt : MatrixInt OrdinaryFull OrdinaryFull :=
  roleBlocksInt
    (bodyLiftIdentityInt sourceFirstComplementRotatedInt)
    (donorLiftIdentityInt sourceDonorComplementRotatedInt)

def sourceFirstPointerInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    (OrdinaryFull ⊕ OrdinaryFull) :=
  intFourBlocks sourceFirstRootRoleInt (intNeg sourceFirstComplementRoleInt)
    sourceFirstComplementRoleInt sourceFirstRootRoleInt


end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
