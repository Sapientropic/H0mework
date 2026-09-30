import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.HeatLeafOrder
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuartic.PrimitiveKernel

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeQuarticStart
open NativeUnheatedTreeRieszKernel (Wave)
open ThreeDimensionalPeriodicCoarseFilterCore
open NativeUnheatedTreeHeatTopology (Tree leaves)
open NativeUnheatedTreeHeatGrowth
open NativeUnheatedTreeHeatEvaluation (Index)
noncomputable section

def triad : Tree := .fork (.fork .leaf .leaf) .leaf

def triadOrder : Fin 3 ≃ Leaf triad where
  toFun := ![.inl (.inl PUnit.unit), .inl (.inr PUnit.unit), .inr PUnit.unit]
  invFun := fun address => match address with
    | .inl (.inl _) => 0
    | .inl (.inr _) => 1
    | .inr _ => 2
  left_inv := by intro number; fin_cases number <;> rfl
  right_inv := by rintro ((point | point) | point) <;> cases point <;> rfl

def triadIndices (k : Wave) : (Wave × Wave) ≃ Index triad where
  toFun index := (k-index.1, ((index.2, (PUnit.unit,PUnit.unit)), PUnit.unit))
  invFun index := (k-index.1, index.2.1.1)
  left_inv index := by ext <;> simp
  right_inv := by
    rintro ⟨a,⟨b,point,point'⟩,point''⟩
    cases point; cases point'; cases point''
    simp
    rfl

def tree (slot : Fin 3) : Tree := grow triad (triadOrder slot)

theorem count (slot : Fin 3) : leaves (tree slot) = 4 :=
  grow_leaves triad (triadOrder slot)

def outerPermutation : Fin 4 ≃ Fin 4 where
  toFun := ![2,3,0,1]
  invFun := ![2,3,0,1]
  left_inv := by intro number; fin_cases number <;> rfl
  right_inv := by intro number; fin_cases number <;> rfl

def permutation (slot : Fin 3) : Fin 4 ≃ Fin 4 := if slot=2 then outerPermutation else Equiv.refl _

def order (slot : Fin 3) : Fin 4 ≃ Leaf (tree slot) :=
  (permutation slot).trans (NativeUnheatedTreeHeatLeafOrder.label triad triadOrder slot)

def indices (slot : Fin 3) (k : Wave) : NativeUnheatedQuarticAllSlots.Index ≃ Index (tree slot) :=
  (Equiv.prodCongr (triadIndices k) (Equiv.refl Wave)).trans (indexEquiv triad (triadOrder slot))

theorem triad_wave (k : Wave) (index : Wave × Wave) (number : Fin 3) :
    wave triad k (triadIndices k index) (triadOrder number) = ![index.2,k-index.1-index.2,index.1] number := by
  fin_cases number
  · rfl
  · rfl
  · change k-(k-index.1) = index.1
    abel

theorem wave_at (slot : Fin 3) (k : Wave) (index : NativeUnheatedQuarticAllSlots.Index)
    (i j outside l m : Coordinate) (number : Fin 4) :
    wave (tree slot) k (indices slot k index) (order slot number) =
      (NativeUnheatedQuarticAllSlots.slots slot k i j outside l m index number).1 := by
  have generated := congrFun (NativeUnheatedTreeHeatLeafOrder.wave_after triad triadOrder slot k
    (triadIndices k index.1) index.2) (permutation slot number)
  change wave (tree slot) k (indices slot k index) (order slot number) = _ at generated
  have original : (fun number => wave triad k (triadIndices k index.1) (triadOrder number)) =
      ![index.1.2,k-index.1.1-index.1.2,index.1.1] := funext (triad_wave k index.1)
  have after := congrArg (fun f : Fin 3 → Wave =>
    (Fin.cons index.2 (Fin.cons (f slot-index.2) (fun number => f (slot.succAbove number))) : Fin 4 → Wave)
      (permutation slot number)) original
  exact generated.trans (after.trans (by fin_cases slot <;> fin_cases number <;> rfl))

def coordinates (slot : Fin 3) (i j outside l m : Coordinate) : Fin 4 → Coordinate :=
  ![![l,m,j,outside], ![l,m,i,outside], ![i,j,l,m]] slot

theorem slots_at (slot : Fin 3) (k : Wave) (index : NativeUnheatedQuarticAllSlots.Index)
    (i j outside l m : Coordinate) :
    (fun number => (wave (tree slot) k (indices slot k index) (order slot number), coordinates slot i j outside l m number)) =
      NativeUnheatedQuarticAllSlots.slots slot k i j outside l m index := by
  funext number
  apply Prod.ext
  · exact wave_at slot k index i j outside l m number
  · fin_cases slot <;> fin_cases number <;> rfl

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeQuarticStart
