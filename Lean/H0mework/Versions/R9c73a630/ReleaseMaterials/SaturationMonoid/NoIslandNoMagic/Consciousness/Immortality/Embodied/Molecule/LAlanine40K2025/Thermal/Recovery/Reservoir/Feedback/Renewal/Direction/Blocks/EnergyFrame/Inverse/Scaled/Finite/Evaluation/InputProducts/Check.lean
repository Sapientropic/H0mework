import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Residual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

def realDot (r i a b : List Int) : Int := Rows.dot r a-Rows.dot i b
def imagDot (r i a b : List Int) : Int := Rows.dot r b+Rows.dot i a

def ProductCheck (r i : List Int) (A B : List (List Int)) (c e : List Int) (p d : Int) : Prop :=
  ∀ j : Basis, |p*realDot r i (Rows.rowAt A j) (Rows.rowAt B j)-d*Rows.read c j|+
    |p*imagDot r i (Rows.rowAt A j) (Rows.rowAt B j)-d*Rows.read e j| ≤ d

theorem checked_product_entry (r i : List Int) (A B : List (List Int)) (c e : List Int) (p d : Int)
    (rLength : r.length=98) (iLength : i.length=98)
    (aLengths : ∀ j : Basis, (Rows.rowAt A j).length=98)
    (bLengths : ∀ j : Basis, (Rows.rowAt B j).length=98)
    (checked : ProductCheck r i A B c e p d) (j : Basis) :
    |p*((∑ k : Basis, Rows.read r k*Rows.read (Rows.rowAt A j) k)-
      (∑ k : Basis, Rows.read i k*Rows.read (Rows.rowAt B j) k))-d*Rows.read c j|+
    |p*((∑ k : Basis, Rows.read r k*Rows.read (Rows.rowAt B j) k)+
      (∑ k : Basis, Rows.read i k*Rows.read (Rows.rowAt A j) k))-d*Rows.read e j| ≤ d := by
  have h := checked j
  simp only [realDot,imagDot,Rows.dot_eq_sum _ _ rLength (aLengths j),Rows.dot_eq_sum _ _ iLength (bLengths j),
    Rows.dot_eq_sum _ _ rLength (bLengths j),Rows.dot_eq_sum _ _ iLength (aLengths j)] at h
  exact h

theorem checked_product (R I A B C D : List (List Int)) (p d : Int)
    (rLengths : ∀ i : Basis, (Rows.rowAt R i).length=98)
    (iLengths : ∀ i : Basis, (Rows.rowAt I i).length=98)
    (aLengths : ∀ j : Basis, (Rows.rowAt A j).length=98)
    (bLengths : ∀ j : Basis, (Rows.rowAt B j).length=98)
    (checked : ∀ i : Basis, ProductCheck (Rows.rowAt R i) (Rows.rowAt I i) A B (Rows.rowAt C i) (Rows.rowAt D i) p d) :
    ∀ i j : Basis,
      |p*(Rows.rowMatrix (n := 98) R*Rows.columnMatrix (n := 98) A-Rows.rowMatrix (n := 98) I*Rows.columnMatrix (n := 98) B) i j-d*Rows.rowMatrix (n := 98) C i j|+
      |p*(Rows.rowMatrix (n := 98) R*Rows.columnMatrix (n := 98) B+Rows.rowMatrix (n := 98) I*Rows.columnMatrix (n := 98) A) i j-d*Rows.rowMatrix (n := 98) D i j| ≤ d := by
  intro i j
  exact checked_product_entry _ _ _ _ _ _ _ _ (rLengths i) (iLengths i) aLengths bLengths (checked i) j

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
