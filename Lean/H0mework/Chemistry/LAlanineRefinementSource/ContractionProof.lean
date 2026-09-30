import H0mework.Chemistry.LAlanineRefinementDensity.LocalDot

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceRowProof

open Lean Elab Term Command Tactic SourceLaplaceRowData SourceLaplaceIntegers SourceFiniteData

def rowCondition (direction : Direction) (basis : Basis) : Prop :=
  rowFourth (innerAxis direction) (outerAxis direction) basis = sourceRow direction basis

elab "checkLaplaceRow " direction:num index:num : command => liftTermElabM do
  let d := direction.getNat
  let i := index.getNat
  unless d < 6 && i < 98 do throwError "Contraction proof incidence"
  let makeFin (value width : Nat) : TermElabM Expr := do
    let inside ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit width))
    return mkApp3 (mkConst ``Fin.mk) (mkNatLit width) (mkNatLit value) inside
  let dir ← makeFin d 6
  let basis ← makeFin i 98
  let lhs := mkApp2 (mkConst ``SourceLaplaceLocalDot.fourth) dir basis
  let type := mkApp2 (mkConst ``rowCondition) dir basis
  let shared := mkApp2 (mkConst ``SourceLaplaceLocalDot.fourth_commutes) dir basis
  let value ← Meta.mkEqTrans (← Meta.mkEqSymm shared) (← Meta.mkEqRefl lhs)
  let name := (← getCurrNamespace) ++ Name.mkSimple s!"row{i}"
  addDecl (.thmDecl { name, levelParams := [], type, value })

elab "closeLaplaceRows" : tactic => do
  let goals ← getGoals
  unless goals.length == 98 do throwError "Contraction proof row census"
  for (goal, i) in goals.zipIdx do
    goal.assign (mkConst ((← getCurrNamespace) ++ Name.mkSimple s!"row{i}"))
  setGoals []

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceRowProof
