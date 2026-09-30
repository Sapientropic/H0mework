import H0mework.Chemistry.LAlanineBasinPartition.SourceData
import H0mework.Chemistry.LAlanineChargeIdentity.SourceParsing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinPartition.SourceReification

open Lean Elab Term Inertia.SourceParsing SourceData

def fieldVector (value : Json) : TermElabM (Array Int) := do
  let row ← decode (Array Int) value
  unless row.size == 8 do throwError "Basin integral field census"
  pure row

def fieldVectorExpr (value : Json) : TermElabM Expr := do
  Meta.mkAppM ``fieldRead #[toExpr (← fieldVector value)]

def bucketCubes (blocks : Array Json) : TermElabM (Expr × Expr) := do
  unless blocks.size == 229 do throwError "Basin original grid block census"
  let mut counts : Array (Array Nat) := #[]
  let mut integrals : Array (Array (Array Int)) := #[]
  for block in blocks do
    let count ← decode (Array Nat) (← field block "bucket_counts")
    let rows ← decode (Array (Array Int)) (← field block "bucket_integer_sums")
    unless count.size == 20 && rows.size == 20 && rows.all (fun row => row.size == 8) do
      throwError "Basin complete disposition census"
    counts := counts.push count
    integrals := integrals.push rows
  return (← Meta.mkAppM ``countRead #[toExpr counts], ← Meta.mkAppM ``cubeRead #[toExpr integrals])

def blockFieldExpr (blocks : Array Json) (key : String) : TermElabM Expr := do
  unless blocks.size == 229 do throwError "Basin integral block census"
  let rows ← blocks.mapM fun block => do fieldVector (← field block key)
  Meta.mkAppM ``blockRead #[toExpr rows]

def bucketFieldExpr (value : Json) : TermElabM Expr := do
  let raw ← decode (Array Json) value
  unless raw.size == 20 do throwError "Basin total disposition census"
  let rows ← raw.mapM fieldVector
  Meta.mkAppM ``bucketRead #[toExpr rows]

def blockWidthExpr (blocks : Array Json) (key : String) (width : Nat) (reader : Name) : TermElabM Expr := do
  let rows ← blocks.mapM fun block => do decode (Array Int) (← field block key)
  unless rows.size == 229 && rows.all (fun row => row.size == width) do throwError "Basin secondary block census"
  Meta.mkAppM reader #[toExpr rows]

def integerVectorExpr (value : Json) (width : Nat) (reader : Name) : TermElabM Expr := do
  let row ← decode (Array Int) value
  unless row.size == width do throwError "Basin integer-vector census"
  Meta.mkAppM reader #[toExpr row]

def attractorScalarExpr (rows : Array Json) (key : String) : TermElabM Expr := do
  let values ← rows.mapM fun row => do decode Int (← field row key)
  Meta.mkAppM ``atomScalarRead #[toExpr values]

def attractorVectorExpr (rows : Array Json) (key : String) : TermElabM Expr := do
  let values ← rows.mapM fun row => do decode (Array Int) (← field row key)
  unless values.all (fun row => row.size == 3) do throwError "Basin attractor axis census"
  Meta.mkAppM ``atomVectorRead #[toExpr values]

end LAlanine40K2025.BasinPartition.SourceReification
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
