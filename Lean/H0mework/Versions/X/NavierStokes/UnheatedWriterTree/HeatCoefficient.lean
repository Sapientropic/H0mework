import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.HeatGrowth

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatCoefficient
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open NativeUnheatedTreeRieszKernel (Wave E)
open NativeUnheatedSexticLatticePower NativeUnheatedTreeHeatTopology
open NativeUnheatedTreeHeatEvaluation NativeUnheatedTreeHeatGrowth
noncomputable section

def coefficient (nu : Viscosity) : (tree : Tree) → Wave → Index tree → ℝ
  | .leaf, _, _ => 1
  | .fork left right, k, index => symbol nu index.1 (k-index.1)*
      coefficient nu left index.1 index.2.1*coefficient nu right (k-index.1) index.2.2

def product (input : Wave → ℝ) : (tree : Tree) → Wave → Index tree → ℝ
  | .leaf, k, _ => input k
  | .fork left right, k, index => product input left index.1 index.2.1*product input right (k-index.1) index.2.2

theorem coefficient_nonnegative (nu : Viscosity) (tree : Tree) (k : Wave) (index : Index tree) :
    0 ≤ coefficient nu tree k index := by
  induction tree generalizing k with
  | leaf => exact zero_le_one
  | fork left right first last =>
    exact mul_nonneg (mul_nonneg (symbol_nonnegative nu _ _) (first _ _)) (last _ _)

theorem term_factor (nu : Viscosity) (input : E) (tree : Tree) (k : Wave) (index : Index tree) :
    term nu input tree k index = coefficient nu tree k index*
      product (fun p => mass p^(-(2/7 : ℝ)/2)*|input p|) tree k index := by
  induction tree generalizing k with
  | leaf => exact (one_mul _).symm
  | fork left right first last =>
    change symbol nu index.1 (k-index.1)*term nu input left index.1 index.2.1*
      term nu input right (k-index.1) index.2.2 = _
    rw [first, last]
    change _ = (symbol nu index.1 (k-index.1)*coefficient nu left index.1 index.2.1*
      coefficient nu right (k-index.1) index.2.2)*
      (product (fun p => mass p^(-(2/7 : ℝ)/2)*|input p|) left index.1 index.2.1*
        product (fun p => mass p^(-(2/7 : ℝ)/2)*|input p|) right (k-index.1) index.2.2)
    ring

theorem coefficient_grow (nu : Viscosity) (tree : Tree) (leaf : Leaf tree)
    (k : Wave) (index : Index tree) (inside : Wave) :
    coefficient nu (grow tree leaf) k (indexEquiv tree leaf (index,inside)) =
      coefficient nu tree k index*symbol nu inside (wave tree k index leaf-inside) := by
  induction tree generalizing k with
  | leaf =>
    change symbol nu inside (k-inside)*1*1 = 1*symbol nu inside (k-inside)
    ring
  | fork left right first last =>
    cases leaf with
    | inl address =>
      change symbol nu index.1 (k-index.1)*
        coefficient nu (grow left address) index.1 (indexEquiv left address (index.2.1,inside))*
        coefficient nu right (k-index.1) index.2.2 = _
      rw [first]
      change _ = (symbol nu index.1 (k-index.1)*coefficient nu left index.1 index.2.1*
        coefficient nu right (k-index.1) index.2.2)*symbol nu inside (wave left index.1 index.2.1 address-inside)
      ring
    | inr address =>
      change symbol nu index.1 (k-index.1)*coefficient nu left index.1 index.2.1*
        coefficient nu (grow right address) (k-index.1) (indexEquiv right address (index.2.2,inside)) = _
      rw [last]
      change _ = (symbol nu index.1 (k-index.1)*coefficient nu left index.1 index.2.1*
        coefficient nu right (k-index.1) index.2.2)*symbol nu inside (wave right (k-index.1) index.2.2 address-inside)
      ring

def rootCoefficient (nu : Viscosity) (tree : Tree) (k : Wave) (index : Index tree) : ℝ :=
  (2*Real.pi)⁻¹*mass k^(-(1/2 : ℝ))*coefficient nu tree k index

theorem root_nonnegative (nu : Viscosity) (tree : Tree) (k : Wave) (index : Index tree) :
    0 ≤ rootCoefficient nu tree k index := by
  unfold rootCoefficient
  positivity [mass_positive k, coefficient_nonnegative nu tree k index]

theorem root_grow (nu : Viscosity) (tree : Tree) (leaf : Leaf tree)
    (k : Wave) (index : Index tree) (inside : Wave) :
    rootCoefficient nu (grow tree leaf) k (indexEquiv tree leaf (index,inside)) =
      rootCoefficient nu tree k index*symbol nu inside (wave tree k index leaf-inside) := by
  unfold rootCoefficient
  rw [coefficient_grow]
  ring

theorem root_initial (nu : Viscosity) (k p : Wave) :
    rootCoefficient nu (.fork .leaf .leaf) k (p,(PUnit.unit,PUnit.unit)) =
      NativeUnheatedTreeLocalHeat.cap nu/(mass p+mass (k-p)) := by
  change (2*Real.pi)⁻¹*mass k^(-(1/2 : ℝ))*(symbol nu p (k-p)*1*1) = _
  unfold symbol factor
  rw [add_sub_cancel]
  have powers : mass k^(-(1/2 : ℝ))*mass k^(1/2 : ℝ) = 1 := by
    rw [← Real.rpow_add (mass_positive k), neg_add_cancel, Real.rpow_zero]
  calc
    _ = ((2*Real.pi)⁻¹*(2*Real.pi))*(mass k^(-(1/2 : ℝ))*mass k^(1/2 : ℝ))*
        NativeUnheatedTreeLocalHeat.cap nu/(mass p+mass (k-p)) := by ring
    _ = _ := by rw [powers, inv_mul_cancel₀ (by positivity : (2*Real.pi) ≠ 0), one_mul, one_mul]

theorem original_pair (nu : Viscosity) (k p : Wave) :
    (NativeUnheatedStressPairEvolution.decay nu p (k-p))⁻¹ ≤
      rootCoefficient nu (.fork .leaf .leaf) k (p,(PUnit.unit,PUnit.unit)) := by
  rw [root_initial]
  exact NativeUnheatedTreeLocalHeat.inverse_mass nu p (k-p)

theorem original_step (nu : Viscosity) (tree : Tree) (leaf : Leaf tree)
    (k : Wave) (index : Index tree) (inside : Wave) (z : ℂ) (rate : ℝ)
    (i j output : ThreeDimensionalPeriodicCoarseFilterCore.Coordinate)
    (paid : ‖z‖ ≤ rootCoefficient nu tree k index)
    (lower : NativeUnheatedStressPairEvolution.decay nu inside (wave tree k index leaf-inside) ≤ rate) :
    ‖rate⁻¹ • (z*NativeUnheatedTriadChannels.pressure (wave tree k index leaf) i j output)‖ ≤
      rootCoefficient nu (grow tree leaf) k (indexEquiv tree leaf (index,inside)) := by
  rw [root_grow, ← mul_smul_comm, norm_mul]
  have generated := NativeUnheatedTreeLocalHeat.pressure_rate_bound nu rate inside
    (wave tree k index leaf-inside) i j output lower
  rw [add_sub_cancel] at generated
  simpa only [symbol, factor, add_sub_cancel] using
    mul_le_mul paid generated (norm_nonneg _) (root_nonnegative nu tree k index)

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatCoefficient
