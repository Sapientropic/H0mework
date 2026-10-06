import H0mework.Versions.AB.Chemistry.LAlanineChargeIdentity.SourceSourceBoundChargeIdentity

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ChargeIdentity.ExactRows

open Lean Elab Term Command Tactic LAlanine40K2025.Force.Interface SourceData
open scoped BigOperators
noncomputable section

def inverseRow (i : Atom) : Prop := ∀ j : Atom,
  ∑ k : Atom, Source.inverseNumerator i k * Source.selectedBInteger k j =
    (Source.inverseDenominator : Int) * (Source.unitScale : Int) * if i = j then 1 else 0

def marginRow (i : Atom) : Prop :=
  2 * (∑ j : Atom, |Source.inverseNumerator i j|) < (Source.inverseDenominator : Int) * 1000000000

def selectedIncidenceRow (i : Atom) : Prop := ∀ j : Atom,
  Source.selectedBInteger i j = Source.fullBInteger (Source.selectedRows i) j

def selectedFieldRow (i : Atom) : Prop :=
  parentFieldInteger (Source.selectedRows i) = Source.reportedSelectedField i

def selectedResidualRow (i : Atom) : Prop :=
  1000 * parentFieldInteger (Source.selectedRows i) +
    ∑ j : Atom, Source.selectedBInteger i j * Source.reportedCharge j = Source.reportedSelectedResidual i

def selectedBoundRow (i : Atom) : Prop := |Source.reportedSelectedResidual i| ≤ 1000000
def positiveRow (i : Atom) : Prop := 0 < Source.reportedCharge i
def originalChargeRow (i : Atom) : Prop := Source.reportedCharge i = parentCharge i

elab "proveChargeRows" : command => liftTermElabM do
  for (family, predicate) in [(`inverse, ``inverseRow), (`margin, ``marginRow),
      (`incidence, ``selectedIncidenceRow), (`field, ``selectedFieldRow), (`residual, ``selectedResidualRow),
      (`bound, ``selectedBoundRow), (`positive, ``positiveRow), (`original, ``originalChargeRow)] do
    for i in [:13] do
      let inside ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit i) (mkNatLit 13))
      let index := mkApp3 (mkConst ``Fin.mk) (mkNatLit 13) (mkNatLit i) inside
      let type := mkApp (mkConst predicate) index
      let expanded := (← getConstInfo predicate).value!.bindingBody!.instantiate1 index
      let value ← instantiateMVars (← Meta.mkDecideProof expanded)
      let name := (← getCurrNamespace) ++ family ++ Name.mkSimple s!"row{i}"
      addDecl (.thmDecl { name, levelParams := [], type, value })

proveChargeRows

elab "closeChargeRows " family:ident : tactic => do
  let goals ← getGoals
  unless goals.length == 13 do throwError "Charge row count"
  for (goal, i) in goals.zipIdx do
    goal.assign (mkConst ((← getCurrNamespace) ++ family.getId ++ Name.mkSimple s!"row{i}"))
  setGoals []

theorem inverseRows (i : Atom) : inverseRow i := by fin_cases i; closeChargeRows inverse
theorem marginRows (i : Atom) : marginRow i := by fin_cases i; closeChargeRows margin
theorem selectedIncidenceRows (i : Atom) : selectedIncidenceRow i := by fin_cases i; closeChargeRows incidence
theorem selectedFieldRows (i : Atom) : selectedFieldRow i := by fin_cases i; closeChargeRows field
theorem selectedResidualRows (i : Atom) : selectedResidualRow i := by fin_cases i; closeChargeRows residual
theorem selectedBoundRows (i : Atom) : selectedBoundRow i := by fin_cases i; closeChargeRows bound
theorem positiveRows (i : Atom) : positiveRow i := by fin_cases i; closeChargeRows positive
theorem originalChargeRows (i : Atom) : originalChargeRow i := by fin_cases i; closeChargeRows original

end
end LAlanine40K2025.ChargeIdentity.ExactRows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
