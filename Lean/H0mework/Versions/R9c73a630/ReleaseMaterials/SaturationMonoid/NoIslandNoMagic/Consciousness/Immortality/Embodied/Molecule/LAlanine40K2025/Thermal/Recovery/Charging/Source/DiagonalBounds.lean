import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefillField.GramEnergy

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Charging.SourceBounds

open Propagation.Interface Propagation.Source Recovery.SourcePrimitive
open scoped Matrix ComplexOrder
noncomputable section

elab "lalanineRechargeDiagonal%" : term => do
  let rows ← sourceMatrixRows
  let values := (List.range 98).map fun i =>
    let row := rows[i * (197 - i) / 2]!
    1000 * row[5]! + row[8]!
  return Lean.toExpr values.toArray

def cachedDiagonal : Array ℤ := lalanineRechargeDiagonal%
def diagonalAt (i : Basis) : ℤ := cachedDiagonal[i.val]!

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem diagonal_exact : ∀ i : Basis, diagonalAt i = activeNumerator electronicSource i i := by decide

set_option maxRecDepth 4096 in
theorem source_trace_positive_integer : (0 : ℤ) < ∑ i : Basis, diagonalAt i := by decide

def gramUpperMargin : ℤ :=
  ∑ i : Basis, (2 * 1000000000000000 - (2 * diagonalAt i - sourceCachedGershDiagonal i)) *
    sourceCachedDensityRowMass i

set_option maxRecDepth 4096 in
theorem gramUpperMargin_positive : 0 < gramUpperMargin := by decide

theorem source_trace_positive : 0 < (activeMatrix electronicSource).trace.re := by
  have positive : (0 : ℝ) < (∑ i : Basis, diagonalAt i : ℤ) / (1000000000000000 : ℝ) :=
    div_pos (Int.cast_pos.mpr source_trace_positive_integer) (by norm_num)
  convert positive using 1
  simp only [Matrix.trace, Matrix.diag, activeMatrix, Complex.re_sum, Complex.div_re,
    Complex.intCast_re, Complex.intCast_im, Int.cast_sum, Finset.sum_div, diagonal_exact]
  norm_num
  congr 1
  ext i
  ring

end
end LAlanine40K2025.Thermal.Recovery.Charging.SourceBounds
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
