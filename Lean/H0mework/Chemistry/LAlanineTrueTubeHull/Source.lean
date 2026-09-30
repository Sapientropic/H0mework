import H0mework.Chemistry.LAlanineTrueTube.SourceData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeHullSource

open Lean Elab Term Command SourceSignedEvaluator SourceRectangle SourceGaussianModel
open Inertia.SourceParsing

/-- Only registered coordinate rows enter the common calculation region. -/
def readCoordinates : TermElabM (Array (Int × Int)) := do
  let whole ← WholeCellSource.verifiedPacket
  let tube ← TrueTubeSource.verifiedPacket
  let first ← WholeCellSource.sourceArray (← field whole "fields") 65
  let second ← WholeCellSource.sourceArray (← field tube "calls") 64
  let boxes ← (first ++ second).mapM fun entry => do
    (← WholeCellSource.sourceArray (← field entry "coordinate_integer_box") 3).mapM
      WholeCellSource.sourceInterval
  return (Array.range 3).map fun axis =>
    boxes.foldl (fun current box => (min current.1 (box[axis]!).1, max current.2 (box[axis]!).2))
      (boxes[0]!)[axis]!

elab "generateTrueTubeCommonHull" : command => liftTermElabM do
  WholeCellSource.declareSource `rawBox (toExpr (← readCoordinates))

generateTrueTubeCommonHull

noncomputable section

def box : Rectangle := fun axis => integerInterval rawBox[axis.val]!

def coordinateHull (axis : Fin 3) : Pair :=
  (((List.finRange 65).map (fun i => WholeCellSource.box i axis)) ++
    ((List.finRange 64).map (fun i => TrueTubeSource.callBox i axis))).foldl
      (fun current next => (min current.1 next.1, max current.2 next.2)) (WholeCellSource.box 0 axis)

theorem box_eq_source_hull : ∀ axis : Fin 3, box axis = coordinateHull axis := by decide +kernel

theorem whole_cells : ∀ i : WholeCellSource.Field, ∀ axis : Fin 3,
    (box axis).1 ≤ (WholeCellSource.box i axis).1 ∧
      (WholeCellSource.box i axis).2 ≤ (box axis).2 := by decide +kernel

theorem call_cells : ∀ c : TrueTubeSource.Call, ∀ axis : Fin 3,
    (box axis).1 ≤ (TrueTubeSource.callBox c axis).1 ∧
      (TrueTubeSource.callBox c axis).2 ≤ (box axis).2 := by decide +kernel

theorem whole_contains (i : WholeCellSource.Field) (x : Point)
    (inside : InRectangle (WholeCellSource.box i) x) : InRectangle box x :=
  fun axis => ⟨(Rat.cast_le.mpr (whole_cells i axis).1).trans (inside axis).1,
    (inside axis).2.trans (Rat.cast_le.mpr (whole_cells i axis).2)⟩

theorem call_contains (c : TrueTubeSource.Call) (x : Point)
    (inside : InRectangle (TrueTubeSource.callBox c) x) : InRectangle box x :=
  fun axis => ⟨(Rat.cast_le.mpr (call_cells c axis).1).trans (inside axis).1,
    (inside axis).2.trans (Rat.cast_le.mpr (call_cells c axis).2)⟩

end
end LAlanine40K2025.BasinRefinement.TrueTubeHullSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
