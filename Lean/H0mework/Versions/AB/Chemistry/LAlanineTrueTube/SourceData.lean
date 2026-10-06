import H0mework.Versions.AB.Chemistry.LAlanineTrueTube.SourceParsing
import H0mework.Versions.AB.Chemistry.LAlanineWholeCell.ReplayModel

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeSource

open Lean Elab Term Command SourceSignedEvaluator SourceRectangle SourceFields WholeCellSource
open Inertia.SourceParsing

elab "generateTrueTubeInputs" : command => liftTermElabM do
  let packet ← verifiedPacket
  let rows ← sourceArray (← field packet "rows") 32
  for key in ["initial", "tube", "endpoint"] do
    let boxes ← rows.mapM fun row => do
      (← sourceArray (← field row (key++"_integer_box")) 3).mapM sourceInterval
    declareSource (Name.mkSimple ("raw"++key++"Boxes")) (toExpr boxes)
  let starts ← rows.mapM fun row => do sourceRational (← field row "elapsed_start")
  let stops ← rows.mapM fun row => do sourceRational (← field row "elapsed_stop")
  let signs ← #[rows[0]!,rows[16]!].mapM fun row => do decode Int (← field row "sign")
  let step ← sourceRational (← field (← field packet "protocol") "step")
  declareSource `rawStarts (toExpr starts)
  declareSource `rawStops (toExpr stops)
  declareSource `rawSigns (toExpr signs)
  declareSource `rawStep (toExpr step)
  let calls ← sourceArray (← field packet "calls") 64
  let callBoxes ← calls.mapM fun current => do
    (← sourceArray (← field current "coordinate_integer_box") 3).mapM sourceInterval
  let callReductions ← calls.mapM fun current => do
    (← sourceArray (← field current "range_reduction_by_group") 94).mapM sourceReduction
  declareSource `rawCallBoxes (toExpr callBoxes)
  declareSource `rawCallReductions (toExpr callReductions)
  let fields ← sourceArray (← field packet "fields") 3
  let boxes ← fields.mapM fun current => do
    (← sourceArray (← field current "coordinate_integer_box") 3).mapM sourceInterval
  let reductions ← fields.mapM fun current => do
    (← sourceArray (← field current "range_reduction_by_group") 94).mapM sourceReduction
  let reports ← fields.mapM fun current => do
    (← sourceArray (← field current "density_integer_intervals") 10).mapM sourceInterval
  declareSource `rawBoxes (toExpr boxes)
  declareSource `rawReductions (toExpr reductions)
  declareSource `rawDensity (toExpr reports)

generateTrueTubeInputs

abbrev Direction := Fin 2
abbrev Step := Fin 16
abbrev Call := Fin 64
abbrev Field := Fin 3

noncomputable section

def rowOffset (d : Direction) (i : Step) : Nat := 16*d.val+i.val
def rowIndex (d : Direction) (i : Step) : Nat := 512+rowOffset d i
def initialCall (d : Direction) (i : Step) : Nat := 1024+2*rowOffset d i
def tubeCall (d : Direction) (i : Step) : Nat := initialCall d i+1
def sign (d : Direction) : ℚ := rawSigns[d.val]!
def stepSize : ℚ := rationalRead rawStep
def elapsedStart (d : Direction) (i : Step) : ℚ := rationalRead rawStarts[rowOffset d i]!
def elapsedStop (d : Direction) (i : Step) : ℚ := rationalRead rawStops[rowOffset d i]!
def initialBox (d : Direction) (i : Step) : Rectangle := fun axis =>
  integerInterval ((rawinitialBoxes[rowOffset d i]!)[axis.val]!)
def tubeBox (d : Direction) (i : Step) : Rectangle := fun axis =>
  integerInterval ((rawtubeBoxes[rowOffset d i]!)[axis.val]!)
def endpointBox (d : Direction) (i : Step) : Rectangle := fun axis =>
  integerInterval ((rawendpointBoxes[rowOffset d i]!)[axis.val]!)
def callBox (c : Call) : Rectangle := fun axis => integerInterval ((rawCallBoxes[c.val]!)[axis.val]!)
def callReductions (c : Call) (g : Group) : Nat × Nat := (rawCallReductions[c.val]!)[g.val]!
def box (f : Field) : Rectangle := fun axis => integerInterval ((rawBoxes[f.val]!)[axis.val]!)
def reductions (f : Field) (g : Group) : Nat × Nat := (rawReductions[f.val]!)[g.val]!
def reportedDensity (f : Field) (j : LowJet) : Pair := integerInterval ((rawDensity[f.val]!)[j.val]!)
def firstTubeField (d : Direction) : Field := ⟨d.val+1, by omega⟩
def recordedField (f : Field) : IntervalParameterMap.FieldBox :=
  ⟨fun axis => reportedDensity f (WholeCellReplay.gradientIndex axis),
    fun axis direction => reportedDensity f (WholeCellReplay.hessianIndex axis direction)⟩

end
end LAlanine40K2025.BasinRefinement.TrueTubeSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
