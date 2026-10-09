import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Kinetic.RowConsumer
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Reifier

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.KineticReifier
open Lean Elab Term Command
open BasinRefinement SourceGaussianModel SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals OriginalMetric
open Kinetic
open SourceReifier

private def fin (value bound : Nat) : TermElabM Expr := do
  let proof ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit bound))
  return mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit bound) (mkNatLit value) proof

private def declareProof (name : Name) (type value : Expr) : TermElabM Unit :=
  addDecl (.thmDecl {name,levelParams := [],type,value})

/-- The source terms propose a kinetic sum; every coefficient and radial
    address is then recognized by the kernel against the recorded ledger. -/
elab "generateKineticRow " row:num : command => liftTermElabM do
  let b := row.getNat
  unless b < 98 do throwError "kinetic AO row"
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
          | throwError "kinetic radial address not generated"
        let value := mkApp2 (Lean.mkConst ``Summand.mk) (← fin i 3859)
          (toExpr (kineticCoefficient first second))
        summands := value :: summands
    let stem := s!"kentry{b}_{c}"
    let rowName ← declare (Name.mkSimple (stem ++ "_summands"))
      (← Meta.mkListLit (Lean.mkConst ``Summand) summands.reverse)
    let rowExpr := Lean.mkConst rowName
    let computedType := mkApp4 (Lean.mkConst ``KineticRowComputed) material bExpr cExpr rowExpr
    let computedName := root ++ Name.mkSimple (stem ++ "_computed")
    declareProof computedName computedType (← exactComputation computedType)
    let interval := mkApp2 (Lean.mkConst ``rowInterval) material rowExpr
    let recorded := mkApp2 (Lean.mkConst ``recordedKinetic) bExpr cExpr
    let residualType := mkApp3 (Lean.mkConst ``RecordedResidual) interval recorded (toExpr (1/10^12 : ℚ))
    let residualName := root ++ Name.mkSimple (stem ++ "_residual")
    declareProof residualName residualType (← exactComputation residualType)
    let value ← Meta.mkAppM ``actual_kinetic_row_error
      #[bExpr,cExpr,rowExpr,Lean.mkConst computedName,Lean.mkConst residualName]
    declareProof (root ++ Name.mkSimple (stem ++ "_error")) (← Meta.inferType value) value

end LAlanine40K2025.UnifiedOrbitals.KineticReifier
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
