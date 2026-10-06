import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Reifier

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.SourceReifier
open Lean Elab Term Command
open BasinRefinement SourceExponential SourceSignedEvaluator

private def sqrtProposal (gamma : ℚ) : Pair :=
  let scale : ℚ := 2^80
  let lower := Nat.sqrt (⌊piLower/gamma*scale^2⌋ : Int).toNat
  let upper := Nat.sqrt (⌊piUpper/gamma*scale^2⌋ : Int).toNat + 1
  ((lower : ℚ)/scale,(upper : ℚ)/scale)

private def reduction (penalty : ℚ) : Nat := Id.run do
  if penalty == 0 || 112 ≤ penalty then return 0
  let mut steps := 0
  while |penalty| / 2^steps > 1/2 do steps := steps + 1
  return steps

elab "generateMetricSquareRoots " start:num stop:num : command => liftTermElabM do
  let data := inputs (← originalTerms)
  let first := start.getNat
  let last := stop.getNat
  unless first ≤ last && last ≤ data.gammas.size do throwError "square root range"
  let root ← getCurrNamespace
  for i in [first:last] do
    let value := mkApp2 (Lean.mkConst ``SqrtMaterial.mk) (toExpr data.gammas[i]!)
      (toExpr (sqrtProposal data.gammas[i]!))
    let name ← declare (Name.mkSimple s!"root{i}") value
    proveStructure (root ++ Name.mkSimple s!"root{i}_computed")
      (mkApp (Lean.mkConst ``SqrtComputed) (Lean.mkConst name)) ``SqrtComputed.mk

elab "generateMetricExponentials " start:num stop:num : command => liftTermElabM do
  let data := inputs (← originalTerms)
  let first := start.getNat
  let last := stop.getNat
  unless first ≤ last && last ≤ data.penalties.size do throwError "exponential range"
  let root ← getCurrNamespace
  for i in [first:last] do
    let penalty := data.penalties[i]!
    let steps := reduction penalty
    let value := mkApp3 (Lean.mkConst ``ExpMaterial.mk) (toExpr penalty) (toExpr steps)
      (toExpr (negativeExp penalty steps))
    let name ← declare (Name.mkSimple s!"exp{i}") value
    proveStructure (root ++ Name.mkSimple s!"exp{i}_computed")
      (mkApp (Lean.mkConst ``ExpComputed) (Lean.mkConst name)) ``ExpComputed.mk

end LAlanine40K2025.UnifiedOrbitals.SourceReifier
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
