import H0mework.Chemistry.LAlanineBandSource.Data

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSource

open Lean Elab Term

/-- Read the already registered safe literal, rather than reparsing the complete archive per call. -/
private def callLiteral (name : Name) (index count : Nat) : TermElabM (Array Expr) := do
  let some (.defnInfo info) := (← getEnv).find? name | throwError "registered source literal missing"
  unless info.safety == .safe do throwError "unsafe source material"
  let some calls ← Meta.getArrayLit? info.value | throwError "native source array required"
  unless calls.size == 2048 && index < 2048 do throwError "complete source call census"
  let some row ← Meta.getArrayLit? calls[index]! | throwError "native call row required"
  unless row.size == count do throwError "source coordinate census"
  return row

def coordinateLiterals (index : Nat) : TermElabM (Array (Int × Int)) := do
  (← callLiteral ``rawCallBoxes index 3).mapM fun value => do
    unless value.isAppOfArity ``Prod.mk 4 do throwError "source coordinate pair required"
    let some lower ← Meta.getIntValue? value.getAppArgs[2]! | throwError "source lower integer"
    let some upper ← Meta.getIntValue? value.getAppArgs[3]! | throwError "source upper integer"
    unless lower ≤ upper do throwError "source interval order"
    return (lower,upper)

def reductionLiterals (index : Nat) : TermElabM (Array (Nat × Nat)) := do
  (← callLiteral ``rawCallReductions index 94).mapM fun value => do
    unless value.isAppOfArity ``Prod.mk 4 do throwError "source reduction pair required"
    let some lower ← Meta.getNatValue? value.getAppArgs[2]! | throwError "source lower reduction"
    let some upper ← Meta.getNatValue? value.getAppArgs[3]! | throwError "source upper reduction"
    return (lower,upper)

end LAlanine40K2025.BasinRefinement.WholeBandSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
