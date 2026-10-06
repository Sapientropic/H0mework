import H0mework.Versions.AB.Chemistry.LAlanineTrueTube.SourceData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeSource

open Lean Elab Term Command SourceSignedEvaluator SourceRectangle SourceFields TrueTubeSource
open Inertia.SourceParsing

elab "generateTrueTubeCallReports" : command => liftTermElabM do
  let packet ← TrueTubeSource.verifiedPacket
  let calls ← WholeCellSource.sourceArray (← field packet "calls") 64
  let reports ← calls.mapM fun current => do
    (← WholeCellSource.sourceArray (← field current "reported_density_integer_intervals") 10).mapM
      WholeCellSource.sourceInterval
  WholeCellSource.declareSource `rawCallDensity (toExpr reports)

generateTrueTubeCallReports

noncomputable section

def initialCallAt (d : Direction) (i : Step) : Call :=
  ⟨2 * (16 * d.val + i.val), by omega⟩

def tubeCallAt (d : Direction) (i : Step) : Call :=
  ⟨2 * (16 * d.val + i.val) + 1, by omega⟩

def callReportedDensity (c : Call) (j : LowJet) : Pair :=
  integerInterval ((rawCallDensity[c.val]!)[j.val]!)

def recordedCallField (c : Call) : IntervalParameterMap.FieldBox :=
  ⟨fun axis => callReportedDensity c (WholeCellReplay.gradientIndex axis),
    fun axis direction => callReportedDensity c (WholeCellReplay.hessianIndex axis direction)⟩

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
