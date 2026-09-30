import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.HeatCoefficient
import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.HeatLeafOrder

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatPacket
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open NativeUnheatedTreeRieszKernel (Wave E)
open NativeUnheatedTreeHeatTopology NativeUnheatedTreeHeatEvaluation NativeUnheatedTreeHeatGrowth
open NativeUnheatedTreeHeatCoefficient NativeUnheatedTreeTime
noncomputable section

structure Alignment (nu : Viscosity) {n : ℕ} {I : Type}
    (nodes : Wave → I → Fin (n+1) → Slot) (raw : Wave → I → ℂ) where
  tree : Tree
  count : leaves tree = n+1
  order : Fin (n+1) ≃ Leaf tree
  indices : (k : Wave) → I ≃ Index tree
  wave_at : ∀ k index number, wave tree k (indices k index) (order number) = (nodes k index number).1
  coefficient_bound : ∀ k index, ‖raw k index‖ ≤ rootCoefficient nu tree k (indices k index)

variable {nu : Viscosity} {n : ℕ} {I : Type}
variable {nodes : Wave → I → Fin (n+1) → Slot} {raw : Wave → I → ℂ}

def splitNodes (selected : Fin (n+1)) (i j : Coordinate) (k : Wave) (index : I × Wave) : Fin (n+2) → Slot :=
  NativeUnheatedTreeLeaf.slots (nodes k index.1) selected i j index.2

def splitKernel (selected : Fin (n+1)) (i j : Coordinate) (k : Wave) (index : I × Wave) : ℂ :=
  NativeUnheatedTreeNormalForm.normalizer nu (splitNodes (nodes := nodes) selected i j k index)
    (NativeUnheatedTreeLeaf.kernel (raw k index.1) (nodes k index.1) selected i j)

def grow (paid : Alignment nu nodes raw) (selected : Fin (n+1)) (i j : Coordinate) :
    Alignment nu (splitNodes (nodes := nodes) selected i j) (splitKernel (nu := nu) (nodes := nodes) (raw := raw) selected i j) where
  tree := NativeUnheatedTreeHeatGrowth.grow paid.tree (paid.order selected)
  count := (grow_leaves paid.tree (paid.order selected)).trans (congrArg (·+1) paid.count)
  order := NativeUnheatedTreeHeatLeafOrder.label paid.tree paid.order selected
  indices k := (Equiv.prodCongr (paid.indices k) (Equiv.refl Wave)).trans (indexEquiv paid.tree (paid.order selected))
  wave_at k index number := by
    have identity := congrFun (NativeUnheatedTreeHeatLeafOrder.wave_after paid.tree paid.order selected k (paid.indices k index.1) index.2) number
    simp only [paid.wave_at] at identity
    refine identity.trans ?_
    refine Fin.cases ?_ (fun number => Fin.cases ?_ (fun number => ?_) number) number <;> rfl
  coefficient_bound k index := by
    have lower := NativeUnheatedTreeLocalHeat.split_rate_lower nu (nodes k index.1) selected i j index.2
    rw [← paid.wave_at k index.1 selected] at lower
    have bound := original_step nu paid.tree (paid.order selected) k (paid.indices k index.1) index.2
      (raw k index.1) (sumRate nu (splitNodes (nodes := nodes) selected i j k index)) i j (nodes k index.1 selected).2
      (paid.coefficient_bound k index.1) lower
    rw [paid.wave_at] at bound
    exact bound

theorem grow_order (paid : Alignment nu nodes raw) (selected : Fin (n+1)) (i j : Coordinate) :
    (grow paid selected i j).order = NativeUnheatedTreeHeatLeafOrder.label paid.tree paid.order selected := rfl

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatPacket
