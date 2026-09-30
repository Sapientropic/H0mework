import H0mework.Chemistry.LAlanineBandSource.Parsing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSource

open Lean Elab Term Command SourceSignedEvaluator SourceRectangle SourceFields WholeCellSource
open Inertia.SourceParsing

elab "generateWholeBandInputs" : command => liftTermElabM do
  let packet ← verifiedPacket
  let calls ← sourceArray (← field packet "calls") 2048
  let boxes ← calls.mapM fun c => do
    (← sourceArray (← field c "coordinate_integer_box") 3).mapM sourceInterval
  let reductions ← calls.mapM fun c => do
    (← sourceArray (← field c "range_reduction_by_group") 94).mapM sourceReduction
  let reports ← calls.mapM fun c => do
    (← sourceArray (← field c "reported_density_integer_intervals") 10).mapM sourceInterval
  declareSource `rawCallBoxes (toExpr boxes)
  declareSource `rawCallReductions (toExpr reductions)
  declareSource `rawCallDensity (toExpr reports)
  let rows ← sourceArray (← field packet "rows") 1024
  for key in ["initial", "tube", "endpoint"] do
    let boxes ← rows.mapM fun r => do
      (← sourceArray (← field r (key++"_integer_box")) 3).mapM sourceInterval
    declareSource (Name.mkSimple ("raw"++key++"Boxes")) (toExpr boxes)
  for (name, key) in [(`rawStarts,"elapsed_start"), (`rawStops,"elapsed_stop")] do
    declareSource name (toExpr (← rows.mapM fun r => do sourceRational (← field r key)))
  declareSource `rawSigns (toExpr (← #[rows[0]!,rows[16]!].mapM fun r => do decode Int (← field r "sign")))
  let protocol ← field packet "protocol"
  declareSource `rawStep (toExpr (← sourceRational (← field protocol "step")))
  declareSource `rawInitialMaxEpsilon (toExpr (← sourceRational (← field protocol "initial_max_epsilon")))
  let cells ← sourceArray (← field packet "cells") 32
  for (name, key) in [(`rawCellV,"v"), (`rawCellLower,"lower"), (`rawCellUpper,"upper")] do
    let values ← cells.mapM fun c => do (← sourceArray (← field c key) 2).mapM sourceRational
    declareSource name (toExpr values)
  for (name, key) in [(`rawKnots,"knots"), (`rawLower,"lower"), (`rawUpper,"upper")] do
    declareSource name (toExpr (← (← sourceArray (← field packet key) 9).mapM sourceRational))

generateWholeBandInputs

abbrev FullBandCell := Fin 32
abbrev Direction := Fin 2
abbrev Step := Fin 16
abbrev FullBandRow := Fin 1024
abbrev FullBandCall := Fin 2048

inductive CallRole
  | initial | tube
  deriving DecidableEq

noncomputable section

def rowAt (c : FullBandCell) (d : Direction) (i : Step) : FullBandRow :=
  ⟨32*c.val+16*d.val+i.val, by omega⟩
def callAt (c : FullBandCell) (d : Direction) (i : Step) (role : CallRole) : FullBandCall :=
  ⟨2*(rowAt c d i).val+(match role with | .initial => 0 | .tube => 1), by cases role <;> dsimp [rowAt] <;> omega⟩
def initialCallAt (c : FullBandCell) (d : Direction) (i : Step) : FullBandCall := callAt c d i .initial
def tubeCallAt (c : FullBandCell) (d : Direction) (i : Step) : FullBandCall := callAt c d i .tube
def cellSegment (c : FullBandCell) : Fin 8 := ⟨c.val/4, by omega⟩
def cellSubsegment (c : FullBandCell) : Fin 4 := ⟨c.val%4, Nat.mod_lt _ (by decide)⟩
def sign (d : Direction) : ℚ := rawSigns[d.val]!
def stepSize : ℚ := rationalRead rawStep
def initialMaxEpsilon : ℚ := rationalRead rawInitialMaxEpsilon
def elapsedStart (c : FullBandCell) (d : Direction) (i : Step) : ℚ := rationalRead rawStarts[(rowAt c d i).val]!
def elapsedStop (c : FullBandCell) (d : Direction) (i : Step) : ℚ := rationalRead rawStops[(rowAt c d i).val]!
def initialBox (c : FullBandCell) (d : Direction) (i : Step) : Rectangle :=
  fun axis => integerInterval ((rawinitialBoxes[(rowAt c d i).val]!)[axis.val]!)
def tubeBox (c : FullBandCell) (d : Direction) (i : Step) : Rectangle :=
  fun axis => integerInterval ((rawtubeBoxes[(rowAt c d i).val]!)[axis.val]!)
def endpointBox (c : FullBandCell) (d : Direction) (i : Step) : Rectangle :=
  fun axis => integerInterval ((rawendpointBoxes[(rowAt c d i).val]!)[axis.val]!)
def callBox (c : FullBandCall) : Rectangle := fun axis => integerInterval ((rawCallBoxes[c.val]!)[axis.val]!)
def callReductions (c : FullBandCall) (g : Group) : Nat × Nat := (rawCallReductions[c.val]!)[g.val]!
def callReportedDensity (c : FullBandCall) (j : LowJet) : Pair := integerInterval ((rawCallDensity[c.val]!)[j.val]!)
def recordedCallField (c : FullBandCall) : IntervalParameterMap.FieldBox :=
  ⟨fun axis => callReportedDensity c (WholeCellReplay.gradientIndex axis),
    fun axis direction => callReportedDensity c (WholeCellReplay.hessianIndex axis direction)⟩
def cellV (c : FullBandCell) (side : Fin 2) : ℚ := rationalRead ((rawCellV[c.val]!)[side.val]!)
def cellLowerCurve (c : FullBandCell) (side : Fin 2) : ℚ := rationalRead ((rawCellLower[c.val]!)[side.val]!)
def cellUpperCurve (c : FullBandCell) (side : Fin 2) : ℚ := rationalRead ((rawCellUpper[c.val]!)[side.val]!)
def knotAt (i : Fin 9) : ℚ := rationalRead rawKnots[i.val]!
def lowerAt (i : Fin 9) : ℚ := rationalRead rawLower[i.val]!
def upperAt (i : Fin 9) : ℚ := rationalRead rawUpper[i.val]!

end
end LAlanine40K2025.BasinRefinement.WholeBandSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
