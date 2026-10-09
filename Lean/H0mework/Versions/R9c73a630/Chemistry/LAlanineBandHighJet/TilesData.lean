import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandHighJet.TilesModel

set_option autoImplicit false
set_option maxRecDepth 65536

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
open WholeBandSource SourceIntegerGrid

structure TileLiterals where
  calls : Array (Array Interval)
  hull : Array Interval
  center : Array ℤ
  deriving Inhabited

open Lean Elab Term Command in
elab "generateTileLiterals" : command => liftTermElabM do
  let mut refs : List Expr := []
  for t in [:64] do
    let ids := (Array.range 32).map fun i =>
      64*(8*(t/16)+i/4)+32*((t/8)%2)+2*(2*(t%8)+(i/2)%2)+i%2
    let calls ← ids.mapM coordinateLiterals
    let hull := calls.foldl (fun acc row => (Array.range 3).map fun a =>
      (min (acc[a]!).1 (row[a]!).1, max (acc[a]!).2 (row[a]!).2)) calls[0]!
    let center := hull.map fun p => (p.1+p.2)/2
    let name := Name.mkSimple s!"tileLiterals{t}"
    let value := mkApp3 (Lean.mkConst ``TileLiterals.mk)
      (toExpr calls) (toExpr hull) (toExpr center)
    WholeCellSource.declareSource name value
    refs := refs ++ [Lean.mkConst ((← getCurrNamespace) ++ name)]
  WholeCellSource.declareSource `tileLiterals (← Meta.mkArrayLit (Lean.mkConst ``TileLiterals) refs)

generateTileLiterals

noncomputable def literalsAt (t : Tile) : TileLiterals := tileLiterals[t.val]!
noncomputable def rawHull (t : Tile) : Array Interval := (literalsAt t).hull
noncomputable def rawCenter (t : Tile) : Array ℤ := (literalsAt t).center
noncomputable def rawTileCalls (t : Tile) : Array (Array Interval) := (literalsAt t).calls
noncomputable def literalCall (t : Tile) (i : Slot) : Array Interval := (rawTileCalls t)[i.val]!
noncomputable def literalHull (t : Tile) (a : Fin 3) : Interval := (rawHull t)[a.val]!
noncomputable def literalCenter (t : Tile) (a : Fin 3) : ℤ := (rawCenter t)[a.val]!
noncomputable def sourceOrderList : List (Array Interval) :=
  List.ofFn (fun f : FullBandCall => literalCall (tileOf f) (slotOf f))
noncomputable def sourceOrder : Array (Array Interval) :=
  Array.ofFn (fun f : FullBandCall => literalCall (tileOf f) (slotOf f))

open Lean Elab Term Command in
elab "recognizeTileCallSource" : command => liftTermElabM do
  let left := Lean.mkConst ``sourceOrderList
  let right ← Meta.mkAppM ``Array.toList #[Lean.mkConst ``rawCallBoxes]
  let type ← Meta.mkEq left right
  let value ← Meta.mkEqRefl right
  let name := (← getCurrNamespace) ++ `tile_call_source_list
  addDecl (.thmDecl { name, levelParams := [], type, value })

recognizeTileCallSource

theorem tile_call_source_array : sourceOrder = rawCallBoxes := by
  apply Array.toList_inj.mp
  rw [sourceOrder, Array.toList_ofFn]
  exact tile_call_source_list

private theorem ofFn_projection {α : Type} [Inhabited α] {n : Nat}
    (fn : Fin n → α) (original : Array α) (same : Array.ofFn fn = original) (i : Fin n) :
    fn i = original[i.val]! := by
  have inside : i.val < original.size := by rw [← same, Array.size_ofFn]; exact i.isLt
  rw [getElem!_pos original i.val inside]
  subst original
  exact (Array.getElem_ofFn (f := fn) (by rw [Array.size_ofFn]; exact i.isLt)).symm

theorem literalCall_original (f : FullBandCall) :
    literalCall (tileOf f) (slotOf f) = rawCallBoxes[f.val]! :=
  ofFn_projection _ _ tile_call_source_array f

theorem literalCall_tileCall (t : Tile) (i : Slot) :
    literalCall t i = rawCallBoxes[(tileCall t i).val]! := by
  simpa only [tileOf_tileCall, slotOf_tileCall] using literalCall_original (tileCall t i)

theorem literal_hull_fold : ∀ (t : Tile) (a : Fin 3), literalHull t a =
    ((List.ofFn (fun i : Slot => fun b : Fin 3 => (literalCall t i)[b.val]!)).foldl
      mergeBox (fun b => (literalCall t 0)[b.val]!)) a := by decide +kernel

theorem literal_center_midpoint : ∀ (t : Tile) (a : Fin 3),
    literalCenter t a = ((literalHull t a).1+(literalHull t a).2)/2 := by decide +kernel

theorem literal_hull_ordered : ∀ (t : Tile) (a : Fin 3),
    (literalHull t a).1 ≤ (literalHull t a).2 := by decide +kernel

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
