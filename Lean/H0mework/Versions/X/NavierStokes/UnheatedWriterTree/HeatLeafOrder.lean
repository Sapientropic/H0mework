import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.HeatGrowth

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatLeafOrder
open NativeUnheatedTreeRieszKernel (Wave)
open NativeUnheatedTreeHeatTopology NativeUnheatedTreeHeatEvaluation NativeUnheatedTreeHeatGrowth
noncomputable section

def insertEquiv : (tree : Tree) → (selected : Leaf tree) → Leaf tree ⊕ PUnit ≃ Leaf (grow tree selected)
  | .leaf, _ => Equiv.refl _
  | .fork left right, .inl selected =>
    (Equiv.sumAssoc (Leaf left) (Leaf right) PUnit).trans
      ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm (Leaf right) PUnit)).trans
        ((Equiv.sumAssoc (Leaf left) PUnit (Leaf right)).symm.trans
          (Equiv.sumCongr (insertEquiv left selected) (Equiv.refl _))))
  | .fork left right, .inr selected =>
    (Equiv.sumAssoc (Leaf left) (Leaf right) PUnit).trans
      (Equiv.sumCongr (Equiv.refl _) (insertEquiv right selected))

theorem insert_first (tree : Tree) (selected : Leaf tree) :
    insertEquiv tree selected (.inl selected) = first tree selected := by
  induction tree with
  | leaf => cases selected; rfl
  | fork left right leftProof rightProof =>
    cases selected with
    | inl address => exact congrArg Sum.inl (leftProof address)
    | inr address => exact congrArg Sum.inr (rightProof address)

theorem insert_second (tree : Tree) (selected : Leaf tree) :
    insertEquiv tree selected (.inr PUnit.unit) = second tree selected := by
  induction tree with
  | leaf => rfl
  | fork left right leftProof rightProof =>
    cases selected with
    | inl address => exact congrArg Sum.inl (leftProof address)
    | inr address => exact congrArg Sum.inr (rightProof address)

def other (tree : Tree) (selected original : Leaf tree) : Leaf (grow tree selected) :=
  insertEquiv tree selected (.inl original)

theorem wave_other (tree : Tree) (selected original : Leaf tree) (different : original ≠ selected)
    (k : Wave) (index : Index tree) (inside : Wave) :
    wave (grow tree selected) k (indexEquiv tree selected (index,inside)) (other tree selected original) =
      wave tree k index original := by
  induction tree generalizing k with
  | leaf => cases selected; cases original; exact (different rfl).elim
  | fork left right leftProof rightProof =>
    cases selected with
    | inl address =>
      cases original with
      | inl original => exact leftProof address original (fun same => different (congrArg Sum.inl same)) index.1 index.2.1
      | inr original => rfl
    | inr address =>
      cases original with
      | inl original => rfl
      | inr original => exact rightProof address original (fun same => different (congrArg Sum.inr same)) (k-index.1) index.2.2

theorem first_ne_second (tree : Tree) (selected : Leaf tree) : first tree selected ≠ second tree selected := by
  intro same
  have distinct := (insertEquiv tree selected).injective ((insert_first tree selected).trans (same.trans (insert_second tree selected).symm))
  cases distinct

variable {n : ℕ}

def pivot (selected : Fin (n+1)) : Fin (n+1) ≃ Fin (n+1) :=
  (finSuccEquiv n).trans (finSuccEquiv' selected).symm

def label (tree : Tree) (order : Fin (n+1) ≃ Leaf tree) (selected : Fin (n+1)) :
    Fin (n+2) ≃ Leaf (grow tree (order selected)) :=
  (finSuccEquiv' (1 : Fin (n+2))).trans
    ((Equiv.optionCongr ((pivot selected).trans order)).trans
      ((Equiv.optionEquivSumPUnit (Leaf tree)).trans (insertEquiv tree (order selected))))

theorem label_first (tree : Tree) (order : Fin (n+1) ≃ Leaf tree) (selected : Fin (n+1)) :
    label tree order selected 0 = first tree (order selected) := by
  have zero : finSuccEquiv' (1 : Fin (n+2)) 0 = some (0 : Fin (n+1)) :=
    finSuccEquiv'_below (i := (1 : Fin (n+2))) (m := (0 : Fin (n+1))) (by change (0 : ℕ) < 1; decide)
  simp only [label, Equiv.trans_apply, zero, Equiv.optionCongr_apply, Option.map_some, pivot,
    finSuccEquiv_zero, finSuccEquiv'_symm_none, Equiv.optionEquivSumPUnit_some, insert_first]

theorem label_second (tree : Tree) (order : Fin (n+1) ≃ Leaf tree) (selected : Fin (n+1)) :
    label tree order selected 1 = second tree (order selected) := by
  simp only [label, Equiv.trans_apply, finSuccEquiv'_at, Equiv.optionCongr_apply, Option.map_none,
    Equiv.optionEquivSumPUnit_none, insert_second]

theorem label_other (tree : Tree) (order : Fin (n+1) ≃ Leaf tree) (selected : Fin (n+1)) (number : Fin n) :
    label tree order selected number.succ.succ = other tree (order selected) (order (selected.succAbove number)) := by
  have later : finSuccEquiv' (1 : Fin (n+2)) number.succ.succ = some number.succ :=
    finSuccEquiv'_above (by change 1 ≤ number.val+1; omega)
  simp only [label, Equiv.trans_apply, later, Equiv.optionCongr_apply, Option.map_some, pivot,
    finSuccEquiv_succ, finSuccEquiv'_symm_some, Equiv.optionEquivSumPUnit_some, other]

theorem wave_after (tree : Tree) (order : Fin (n+1) ≃ Leaf tree) (selected : Fin (n+1))
    (k : Wave) (index : Index tree) (inside : Wave) :
    (fun number => wave (grow tree (order selected)) k (indexEquiv tree (order selected) (index,inside))
      (label tree order selected number)) =
    Fin.cons inside (Fin.cons (wave tree k index (order selected)-inside)
      (fun number => wave tree k index (order (selected.succAbove number)))) := by
  funext number
  refine Fin.cases ?_ (fun number => Fin.cases ?_ (fun number => ?_) number) number
  · simpa only [Fin.cons_zero, label_first] using first_wave tree (order selected) k index inside
  · simpa only [Fin.cons_succ, Fin.cons_zero, Fin.cons_one, show (0 : Fin (n+1)).succ = 1 by rfl, label_second] using
      second_wave tree (order selected) k index inside
  · simp only [Fin.cons_succ, label_other]
    exact wave_other tree (order selected) (order (selected.succAbove number))
      (fun same => Fin.succAbove_ne selected number (order.injective same)) k index inside

theorem slots_after (tree : Tree) (order : Fin (n+1) ≃ Leaf tree) (selected : Fin (n+1))
    (k : Wave) (index : Index tree) (inside : Wave)
    (coordinates : Fin (n+1) → ThreeDimensionalPeriodicCoarseFilterCore.Coordinate)
    (u v : ThreeDimensionalPeriodicCoarseFilterCore.Coordinate) :
    (fun number => (wave (grow tree (order selected)) k (indexEquiv tree (order selected) (index,inside))
        (label tree order selected number),
      (Fin.cons u (Fin.cons v (fun number => coordinates (selected.succAbove number))) :
        Fin (n+2) → ThreeDimensionalPeriodicCoarseFilterCore.Coordinate) number)) =
    NativeUnheatedTreeLeaf.slots (fun number => (wave tree k index (order number), coordinates number)) selected u v inside := by
  funext number
  refine Fin.cases ?_ (fun number => Fin.cases ?_ (fun number => ?_) number) number
  · apply Prod.ext
    · simpa only [Fin.cons_zero, NativeUnheatedTreeLeaf.slots] using
        congrFun (wave_after tree order selected k index inside) 0
    · rfl
  · apply Prod.ext
    · simpa only [Fin.cons_succ, Fin.cons_zero, NativeUnheatedTreeLeaf.slots] using
        congrFun (wave_after tree order selected k index inside) (0 : Fin (n+1)).succ
    · rfl
  · apply Prod.ext
    · simpa only [Fin.cons_succ, NativeUnheatedTreeLeaf.slots] using
        congrFun (wave_after tree order selected k index inside) number.succ.succ
    · rfl

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatLeafOrder
