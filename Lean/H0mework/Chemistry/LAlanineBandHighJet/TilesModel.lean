import H0mework.Chemistry.LAlanineBandSource.Literals
import H0mework.Chemistry.LAlanineContinuousMatrix.IntegerGrid

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
open WholeBandSource SourceIntegerGrid

abbrev Tile := Fin 64
abbrev Slot := Fin 32

def tileCall (t : Tile) (i : Slot) : FullBandCall :=
  ⟨64*(8*(t.val/16)+i.val/4)+32*((t.val/8)%2)+2*(2*(t.val%8)+(i.val/2)%2)+i.val%2, by omega⟩
def tileOf (f : FullBandCall) : Tile :=
  ⟨16*(f.val/512)+8*((f.val/32)%2)+(f.val/4)%8,by omega⟩
def slotOf (f : FullBandCall) : Slot :=
  ⟨4*((f.val/64)%8)+2*((f.val/2)%2)+f.val%2,by omega⟩

theorem every_original_call (f : FullBandCall) : tileCall (tileOf f) (slotOf f) = f := by
  apply Fin.ext
  simp only [tileCall,tileOf,slotOf]
  omega

theorem tileOf_tileCall (t : Tile) (i : Slot) : tileOf (tileCall t i) = t := by
  revert t i
  decide +kernel

theorem slotOf_tileCall (t : Tile) (i : Slot) : slotOf (tileCall t i) = i := by
  revert t i
  decide +kernel

theorem tileCall_unique {t u : Tile} {i j : Slot}
    (same : tileCall t i = tileCall u j) : t = u ∧ i = j := by
  constructor
  · simpa only [tileOf_tileCall] using congrArg tileOf same
  · simpa only [slotOf_tileCall] using congrArg slotOf same

def mergeInterval (a b : Interval) : Interval := (min a.1 b.1,max a.2 b.2)
def mergeBox (a b : Fin 3 → Interval) : Fin 3 → Interval := fun axis => mergeInterval (a axis) (b axis)
noncomputable def callIntegers (f : FullBandCall) : Fin 3 → Interval := fun axis => (rawCallBoxes[f.val]!)[axis.val]!
noncomputable def tileHull (t : Tile) : Fin 3 → Interval :=
  (List.ofFn (fun i : Slot => callIntegers (tileCall t i))).foldl mergeBox (callIntegers (tileCall t 0))
noncomputable def tileCenter (t : Tile) (axis : Fin 3) : ℤ :=
  ((tileHull t axis).1+(tileHull t axis).2)/2

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
