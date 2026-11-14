import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Ports.Branch.Cost

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ProductSource
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)

theorem product_distributes (point : Nat → Bool) (flag : Bool) (indices : List Nat) :
    Parity.eval (fun i => flag && point i) indices=(flag && Parity.eval point indices) := by
  induction indices with
  | nil => cases flag <;> rfl
  | cons i rest ih =>
      simp only [Parity.eval,ih]
      cases flag <;> cases point i <;> cases Parity.eval point rest <;> rfl

def pairs (width : Nat) : List (Nat × Nat) := (List.range width).product (List.range width)

theorem pairs_length (width : Nat) : (pairs width).length=width*width := by
  simp [pairs,List.product,List.length_flatMap]

theorem pairs_mem (width i j : Nat) : (i,j) ∈ pairs width ↔ i < width ∧ j < width := by simp [pairs]

def index (frame : Frame) (i j : Nat) : Nat := frame.ports.size+(pairs frame.ports.size).idxOf (i,j)

def multiplyRow (frame : Frame) (i : Nat) (row : Row) : Row :=
  ⟨row.vars.map (index frame i) ++ if row.rhs then [i] else [],false⟩

theorem parity_append (point : Nat → Bool) (first second : List Nat) :
    Parity.eval point (first++second)=(Parity.eval point first ^^ Parity.eval point second) := by
  induction first with
  | nil => simp [Parity.eval]
  | cons i rest ih => simp only [List.cons_append,Parity.eval,ih,Bool.xor_assoc]

def rows (frame : Frame) (basis : List Row) : List Row :=
  (List.range frame.ports.size).flatMap (fun i => basis.map (multiplyRow frame i))

theorem rows_length (frame : Frame) (basis : List Row) : (rows frame basis).length=frame.ports.size*basis.length := by
  simp [rows,List.length_flatMap,List.length_map]

end SaturationMonoid.ComplexityProjection.SATSource.ProductSource
