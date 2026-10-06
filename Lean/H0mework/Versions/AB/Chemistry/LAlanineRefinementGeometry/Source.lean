import H0mework.Versions.AB.Chemistry.LAlanineRefinementGeometry.Parsing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Geometry.Source

open Lean Elab Term Command Inertia.SourceParsing

private def declare (suffix : Name) (value : Expr) : TermElabM Unit := do
  let value ← instantiateMVars value
  let type ← Meta.inferType value
  let name := (← getCurrNamespace) ++ suffix
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

elab "generateCurvedGeometryReadouts" : command => liftTermElabM do
  let packet ← Parsing.verifiedPacket
  let rows ← Parsing.array (← field packet "runs") 5
  declare `runs (← Meta.mkArrayLit (mkConst ``Data.RunReceipt) (← rows.toList.mapM Parsing.run))
  let epsilons ← rows.mapM fun row => do Parsing.positiveHexDyadic (← decode String (← field row "epsilon_hex"))
  declare `epsilonCoordinates (toExpr epsilons)
  let seed ← field packet "seed"
  declare `selectedBasin (toExpr (← decode Nat (← field seed "selected_basin")))
  for (name, key) in [(`sourceRows, "source_rows"), (`incidentPair, "incident_pair")] do
    declare name (toExpr (← Parsing.nats (← field seed key) 2))
  let center ← Parsing.array (← field seed "center") 3
  declare `centerCoordinates (toExpr (← center.mapM rationalPair))
  let basis ← Parsing.array (← field seed "basis") 3
  let basis ← basis.mapM fun row => do
    let row ← Parsing.array row 2
    row.mapM rationalPair
  declare `basisCoordinates (toExpr basis)
  let seedHistory ← decode (Array Json) (← field seed "bracket_history")
  declare `seedLastBucket (toExpr (← decode Nat (← field seedHistory.back! "bucket")))
  let curve ← field packet "curve"
  for (name, key) in [(`curveKnots, "knots"), (`curveLower, "lower"), (`curveUpper, "upper")] do
    let values ← Parsing.array (← field curve key) 9
    declare name (toExpr (← values.mapM rationalPair))
  let endpoints ← Parsing.array (← field curve "endpoints") 2
  for (name, key) in [(`curveEndpointBuckets, "bucket"), (`curveEndpointCoarse, "coarse"), (`curveEndpointFine, "fine")] do
    let values ← endpoints.mapM fun row => do Parsing.nats (← field row key) 9
    declare name (toExpr values)
  let mut ambiguous : Array Nat := #[]
  for row in (← decode (Array Json) (← field curve "history")) do
    if (← decode String (← field row "kind")) == "bisection" then
      for code in (← decode (Array Nat) (← field row "bucket")) do
        if code ≥ 13 then ambiguous := ambiguous.push code
  declare `curveAmbiguousBuckets (toExpr ambiguous)

set_option maxRecDepth 4096 in
generateCurvedGeometryReadouts

def sourcePacketText : String := Parsing.sourceText

noncomputable section

def run (index : Data.RunIndex) : Data.RunReceipt := runs[index.val]!
def domain (index : Data.RunIndex) (slab : Data.Slab) : Data.DomainReceipt := (run index).domains[slab.val]!
def face (index : Data.RunIndex) (side : Data.Face) : Data.FaceReceipt := (run index).faces[side.val]!
def seam (index : Data.RunIndex) (cut : Data.Seam) : Data.SeamReceipt := (run index).seams[cut.val]!
def epsilon (index : Data.RunIndex) : ℚ := rationalRead (epsilonCoordinates[index.val]!)
def center (axis : Fin 3) : ℚ := rationalRead (centerCoordinates[axis.val]!)
def basis (axis : Fin 3) (direction : Fin 2) : ℚ := rationalRead ((basisCoordinates[axis.val]!)[direction.val]!)
def lower (knot : Data.Knot) : ℚ := rationalRead (curveLower[knot.val]!)
def upper (knot : Data.Knot) : ℚ := rationalRead (curveUpper[knot.val]!)

end
end LAlanine40K2025.BasinRefinement.Geometry.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
