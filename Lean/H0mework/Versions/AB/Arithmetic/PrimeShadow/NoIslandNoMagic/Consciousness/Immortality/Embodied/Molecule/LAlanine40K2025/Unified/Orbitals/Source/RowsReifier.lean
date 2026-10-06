import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.RowConsumer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.SourceReifier
open Lean Elab Term Command
open BasinRefinement SourceGaussianModel SourceFiniteData OriginalMetric

private def fin (value bound : Nat) : TermElabM Expr := do
  let proof ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit bound))
  return mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit bound) (mkNatLit value) proof

private def declareProof (name : Name) (type value : Expr) : TermElabM Unit :=
  addDecl (.thmDecl {name,levelParams := [],type,value})

/-- The source terms propose a sum; every coefficient and radial address is then recognized by the kernel. -/
elab "generateOriginalMetricRow " row:num : command => liftTermElabM do
  let b := row.getNat
  unless b < 98 do throwError "original AO row"
  let source ← originalTerms
  let data := inputs source
  let mut index : Std.HashMap ((Int × Nat) × (Int × Nat)) Nat := {}
  for i in [:data.radial.size] do
    let (gamma,penalty) := data.radial[i]!
    index := index.insert ((gamma.num,gamma.den),(penalty.num,penalty.den)) i
  let root ← getCurrNamespace
  let material := Lean.mkConst ``radialMaterial
  let bExpr ← fin b 98
  for c in [:98] do
    let cExpr ← fin c 98
    let mut summands : List Expr := []
    for first in source[b]! do
      for second in source[c]! do
        let gamma := pairExponent first second
        let penalty := pairPenalty first second
        let some i := index[((gamma.num,gamma.den),(penalty.num,penalty.den))]?
          | throwError "original radial address not generated"
        let value := mkApp2 (Lean.mkConst ``Summand.mk) (← fin i 3859)
          (toExpr (primitiveCoefficient first second))
        summands := value :: summands
    let stem := s!"entry{b}_{c}"
    let rowName ← declare (Name.mkSimple (stem ++ "_summands"))
      (← Meta.mkListLit (Lean.mkConst ``Summand) summands.reverse)
    let rowExpr := Lean.mkConst rowName
    let computedType := mkApp4 (Lean.mkConst ``RowComputed) material bExpr cExpr rowExpr
    let computedName := root ++ Name.mkSimple (stem ++ "_computed")
    declareProof computedName computedType (← exactComputation computedType)
    let interval := mkApp2 (Lean.mkConst ``rowInterval) material rowExpr
    let recorded := mkApp2 (Lean.mkConst ``recordedOverlap) bExpr cExpr
    let residualType := mkApp3 (Lean.mkConst ``RecordedResidual) interval recorded (toExpr (1/10^12 : ℚ))
    let residualName := root ++ Name.mkSimple (stem ++ "_residual")
    declareProof residualName residualType (← exactComputation residualType)
    let value ← Meta.mkAppM ``actual_row_error
      #[bExpr,cExpr,rowExpr,Lean.mkConst computedName,Lean.mkConst residualName]
    declareProof (root ++ Name.mkSimple (stem ++ "_error")) (← Meta.inferType value) value

end LAlanine40K2025.UnifiedOrbitals.SourceReifier
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
