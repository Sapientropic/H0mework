import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerPulses.Consumer
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Contraction Load.Source
def pairFin : (Fin 2 × Fin 2) ≃ Fin 4 := finProdFinEquiv

def nativeFin : LoadPrimitive.NativeIndex ≃ Fin 8 :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin 2))).trans finProdFinEquiv

def ordinaryFullFin : OrdinaryFull ≃ Fin 32 :=
  let body : ((Fin 2 × Fin 2) × Fin 2) ≃ Fin 8 := nativeFin
  let pair : (((Fin 2 × Fin 2) × Fin 2) ⊕ ((Fin 2 × Fin 2) × Fin 2)) ≃ Fin 16 :=
    (Equiv.sumCongr body body).trans finSumFinEquiv
  (Equiv.prodCongr pair (Equiv.refl (Fin 2))).trans finProdFinEquiv

def pointerFin : (OrdinaryFull ⊕ OrdinaryFull) ≃ Fin 64 :=
  (Equiv.sumCongr ordinaryFullFin ordinaryFullFin).trans finSumFinEquiv

structure IntTable (n m : Nat) where
  re : Vector (Vector Int m) n
  im : Vector (Vector Int m) n

theorem int_table_ext {n m : Nat} {A B : IntTable n m}
    (hRe : A.re=B.re) (hIm : A.im=B.im) : A=B := by
  cases A
  cases B
  cases hRe
  cases hIm
  rfl

def toTable {α β : Type*} {n m : Nat} (A : MatrixInt α β)
    (ra : α ≃ Fin n) (cb : β ≃ Fin m) : IntTable n m :=
  ⟨Vector.ofFn (fun i => Vector.ofFn (fun j => A.re (ra.symm i) (cb.symm j))),
   Vector.ofFn (fun i => Vector.ofFn (fun j => A.im (ra.symm i) (cb.symm j)))⟩

def fromTable {α β : Type*} {n m : Nat} (T : IntTable n m)
    (ra : α ≃ Fin n) (cb : β ≃ Fin m) : MatrixInt α β :=
  ⟨fun i j => (T.re.get (ra i)).get (cb j),
   fun i j => (T.im.get (ra i)).get (cb j)⟩

theorem from_to_table {α β : Type*} {n m : Nat} (A : MatrixInt α β)
    (ra : α ≃ Fin n) (cb : β ≃ Fin m) :
    fromTable (toTable A ra cb) ra cb=A := by
  cases A with
  | mk re im =>
    simp [fromTable,toTable]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
