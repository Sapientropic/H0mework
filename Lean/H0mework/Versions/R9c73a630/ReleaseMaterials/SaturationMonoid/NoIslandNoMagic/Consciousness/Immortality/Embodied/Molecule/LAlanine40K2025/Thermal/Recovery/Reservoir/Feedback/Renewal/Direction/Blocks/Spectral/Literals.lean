import Lean.Elab.Term
import Lean.ToExpr

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral

/-- Literal integers only: matrix-product and source identities are checked separately by the kernel. -/
elab "spectralRow% " encoded:str : term => do
  let row : List Int ← encoded.getString.splitOn "," |>.mapM fun field => do
    match field.toInt? with
    | some value => pure value
    | none => throwError "spectral integer row"
  return Lean.toExpr row

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
