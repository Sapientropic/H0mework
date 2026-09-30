import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.HeatEvaluation

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatGrowth
open NativeUnheatedTreeRieszKernel (Wave E)
open NativeUnheatedTreeHeatTopology NativeUnheatedTreeHeatEvaluation
noncomputable section

def Leaf : Tree → Type
  | .leaf => PUnit
  | .fork left right => Leaf left ⊕ Leaf right

def wave : (tree : Tree) → Wave → Index tree → Leaf tree → Wave
  | .leaf, k, _, _ => k
  | .fork left _, _, index, .inl leaf => wave left index.1 index.2.1 leaf
  | .fork _ right, k, index, .inr leaf => wave right (k-index.1) index.2.2 leaf

def grow : (tree : Tree) → Leaf tree → Tree
  | .leaf, _ => .fork .leaf .leaf
  | .fork left right, .inl leaf => .fork (grow left leaf) right
  | .fork left right, .inr leaf => .fork left (grow right leaf)

theorem grow_leaves (tree : Tree) (leaf : Leaf tree) : leaves (grow tree leaf) = leaves tree+1 := by
  induction tree with
  | leaf => rfl
  | fork left right first last =>
    cases leaf with
    | inl address => simp only [grow, leaves, first]; omega
    | inr address => simp only [grow, leaves, last]; omega

def indexEquiv : (tree : Tree) → (leaf : Leaf tree) → Index tree × Wave ≃ Index (grow tree leaf)
  | .leaf, _ =>
    { toFun := fun index => (index.2, (PUnit.unit, PUnit.unit))
      invFun := fun index => (PUnit.unit, index.1)
      left_inv := fun index => by cases index with | mk point k => cases point; rfl
      right_inv := fun index => by rcases index with ⟨k,point,point'⟩; cases point; cases point'; rfl }
  | .fork left right, .inl leaf => by
    let e := indexEquiv left leaf
    exact
      { toFun := fun index => (index.1.1, (e (index.1.2.1,index.2),index.1.2.2))
        invFun := fun index => ((index.1, ((e.symm index.2.1).1,index.2.2)),(e.symm index.2.1).2)
        left_inv := fun index => by simp only [Equiv.symm_apply_apply]; rfl
        right_inv := fun index => by simp only [Prod.mk.eta, Equiv.apply_symm_apply]; rfl }
  | .fork left right, .inr leaf => by
    let e := indexEquiv right leaf
    exact
      { toFun := fun index => (index.1.1, (index.1.2.1,e (index.1.2.2,index.2)))
        invFun := fun index => ((index.1, (index.2.1,(e.symm index.2.2).1)),(e.symm index.2.2).2)
        left_inv := fun index => by simp only [Equiv.symm_apply_apply]; rfl
        right_inv := fun index => by simp only [Prod.mk.eta, Equiv.apply_symm_apply]; rfl }

def first : (tree : Tree) → (leaf : Leaf tree) → Leaf (grow tree leaf)
  | .leaf, _ => .inl PUnit.unit
  | .fork left _, .inl leaf => .inl (first left leaf)
  | .fork _ right, .inr leaf => .inr (first right leaf)

def second : (tree : Tree) → (leaf : Leaf tree) → Leaf (grow tree leaf)
  | .leaf, _ => .inr PUnit.unit
  | .fork left _, .inl leaf => .inl (second left leaf)
  | .fork _ right, .inr leaf => .inr (second right leaf)

theorem first_wave (tree : Tree) (leaf : Leaf tree) (k : Wave) (index : Index tree) (inside : Wave) :
    wave (grow tree leaf) k (indexEquiv tree leaf (index,inside)) (first tree leaf) = inside := by
  induction tree generalizing k with
  | leaf => rfl
  | fork left right leftProof rightProof =>
    cases leaf with
    | inl address => exact leftProof address index.1 index.2.1
    | inr address => exact rightProof address (k-index.1) index.2.2

theorem second_wave (tree : Tree) (leaf : Leaf tree) (k : Wave) (index : Index tree) (inside : Wave) :
    wave (grow tree leaf) k (indexEquiv tree leaf (index,inside)) (second tree leaf) = wave tree k index leaf-inside := by
  induction tree generalizing k with
  | leaf => rfl
  | fork left right leftProof rightProof =>
    cases leaf with
    | inl address => exact leftProof address index.1 index.2.1
    | inr address => exact rightProof address (k-index.1) index.2.2

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatGrowth
