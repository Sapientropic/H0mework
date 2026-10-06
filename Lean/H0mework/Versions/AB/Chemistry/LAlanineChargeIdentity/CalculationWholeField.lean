import H0mework.Versions.AB.Chemistry.LAlanineChargeIdentity.SourceSourceBoundChargeIdentity

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ChargeIdentity.WholeField

open Lean Elab Term Command Tactic LAlanine40K2025.Force.Interface SourceData
open scoped BigOperators
noncomputable section

def actualResidual (row : FieldRow) : Int :=
  1000 * parentFieldInteger row + ∑ atom : Atom, Source.fullBInteger row atom * Source.reportedCharge atom

def blockCheck (block : Fin 38) : Prop := ∀ offset : Fin 128,
  if inside : block.val * 128 + offset.val < 4851 then
    actualResidual ⟨block.val * 128 + offset.val, inside⟩ =
      Source.reportedFullResidual ⟨block.val * 128 + offset.val, inside⟩ ∧
    |Source.reportedFullResidual ⟨block.val * 128 + offset.val, inside⟩| ≤ 509
  else True

elab "proveWholeChargeField" : command => liftTermElabM do
  for i in [:38] do
    let inside ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit i) (mkNatLit 38))
    let index := mkApp3 (mkConst ``Fin.mk) (mkNatLit 38) (mkNatLit i) inside
    let type := mkApp (mkConst ``blockCheck) index
    let expanded := (← getConstInfo ``blockCheck).value!.bindingBody!.instantiate1 index
    let value ← instantiateMVars (← Meta.mkDecideProof expanded)
    let name := (← getCurrNamespace) ++ Name.mkSimple s!"block{i}"
    addDecl (.thmDecl { name, levelParams := [], type, value })

proveWholeChargeField

elab "closeWholeChargeField" : tactic => do
  let goals ← getGoals
  unless goals.length == 38 do throwError "Whole charge field block count"
  for (goal, i) in goals.zipIdx do
    goal.assign (mkConst ((← getCurrNamespace) ++ Name.mkSimple s!"block{i}"))
  setGoals []

theorem everyBlock (block : Fin 38) : blockCheck block := by
  fin_cases block
  closeWholeChargeField

theorem actualResidual_exact_and_bounded (row : FieldRow) :
    actualResidual row = Source.reportedFullResidual row ∧ |Source.reportedFullResidual row| ≤ 509 := by
  let block : Fin 38 := ⟨row.val / 128, by omega⟩
  let offset : Fin 128 := ⟨row.val % 128, Nat.mod_lt _ (by decide)⟩
  have index : block.val * 128 + offset.val = row.val := by dsimp [block, offset]; omega
  have inside : block.val * 128 + offset.val < 4851 := by rw [index]; exact row.isLt
  have check := everyBlock block offset
  rw [dif_pos inside] at check
  have same : (⟨block.val * 128 + offset.val, inside⟩ : FieldRow) = row := Fin.ext index
  simpa only [same] using check

end
end LAlanine40K2025.ChargeIdentity.WholeField
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
