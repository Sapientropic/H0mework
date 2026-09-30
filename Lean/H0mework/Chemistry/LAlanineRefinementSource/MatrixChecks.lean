import H0mework.Chemistry.LAlanineRefinementSource.SharedRationalTables
import H0mework.Chemistry.LAlanineRefinementSource.SharedIntegerTables

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SharedMatrixChecks

open SourceFiniteData
open Lean Elab Term Command

def rowCondition (i : Basis) : Prop := ∀ j : Basis,
  |SourceSharedRationalTables.density i j| ≤ (SourceLaplaceSharedTables.matrix i j : ℚ) / 10 ^ 12

elab "proveSharedMatrixRows" : command => liftTermElabM do
  for i in [:98] do
    let inside ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit i) (mkNatLit 98))
    let index := mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit 98) (mkNatLit i) inside
    let type := mkApp (Lean.mkConst ``rowCondition) index
    let expanded := (← getConstInfo ``rowCondition).value!.bindingBody!.instantiate1 index
    let value ← instantiateMVars (← Meta.mkDecideProof expanded)
    addDecl (.thmDecl { name := (← getCurrNamespace) ++ Name.mkSimple s!"row{i}", levelParams := [], type, value })

proveSharedMatrixRows

elab "useSharedMatrixRows" : tactic => do
  let goals ← Lean.Elab.Tactic.getGoals
  unless goals.length == 98 do throwError "Matrix row proof census"
  for (goal, i) in goals.zipIdx do
    goal.assign (Lean.mkConst ((← getCurrNamespace) ++ Name.mkSimple s!"row{i}"))
  Lean.Elab.Tactic.setGoals []

theorem actual_shared_matrix_envelope (i : Basis) : rowCondition i := by
  fin_cases i
  useSharedMatrixRows

theorem original_matrix_envelope (i j : Basis) : |densityMatrix i j| ≤ densityMatrixBound i j := by
  rw [densityMatrixBound_integer, ← SourceSharedRationalTables.density_commutes,
    ← SourceLaplaceSharedTables.matrix_commutes]
  exact actual_shared_matrix_envelope i j

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SharedMatrixChecks
