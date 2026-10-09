import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate.Exchange

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
open Propagation.Interface Load.Source Fixed Contraction
open scoped Matrix

variable {α β : Type*}
abbrev Leg (α β : Type*) := (α × β) × Fin 2
abbrev Role (α β : Type*) := ((α × β) ⊕ (α × β)) × Fin 2

def roleAddress (f : α → PairController) (g : β → PairController) : Role α β → Current.FullIndex
  | (.inl (a,b),e) => ((f a,g b),e)
  | (.inr (a,b),e) => ((g b,f a),e)

def bodyLiftQ (U : MatrixQ (α × Fin 2) (α × Fin 2)) (V : MatrixQ β β) : MatrixQ (Leg α β) (Leg α β) :=
  fun i j => Scalar.multiply (U (i.1.1,i.2) (j.1.1,j.2)) (V i.1.2 j.1.2)

def donorLiftQ (U : MatrixQ (β × Fin 2) (β × Fin 2)) (V : MatrixQ α α) : MatrixQ (Leg α β) (Leg α β) :=
  fun i j => Scalar.multiply (V i.1.1 j.1.1) (U (i.1.2,i.2) (j.1.2,j.2))

def roleBlocksQ (A B : MatrixQ (Leg α β) (Leg α β)) : MatrixQ (Role α β) (Role α β)
  | (.inl i,e),(.inl j,f) => A (i,e) (j,f)
  | (.inr i,e),(.inr j,f) => B (i,e) (j,f)
  | _,_ => (0,0)

theorem scalar_multiply_comm (a b : Scalar.QComplex) : Scalar.multiply a b=Scalar.multiply b a := by
  apply Prod.ext <;> simp only [Scalar.multiply] <;> ring

theorem qzero_of_separated (A : MatrixQ (PairController × Fin 2) (PairController × Fin 2))
    (kept : Preserves pceOrbit (qvalue A)) (i j : PairController × Fin 2) (different : pceOrbit i ≠ pceOrbit j) :
    A i j=(0,0) := by
  apply LoadPrimitive.scalar_value_injective
  have zero := kept i j different
  simpa only [qvalue,Scalar.value,Rat.cast_zero,zero_add,mul_zero] using zero

theorem qpc_zero_of_separated (A : MatrixQ PairController PairController)
    (kept : Preserves pcOrbit (qvalue A)) (i j : PairController) (different : pcOrbit i ≠ pcOrbit j) :
    A i j=(0,0) := by
  apply LoadPrimitive.scalar_value_injective
  have zero := kept i j different
  simpa only [qvalue,Scalar.value,Rat.cast_zero,zero_add,mul_zero] using zero

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
