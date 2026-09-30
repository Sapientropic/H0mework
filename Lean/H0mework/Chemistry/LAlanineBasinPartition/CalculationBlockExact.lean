import H0mework.Chemistry.LAlanineBasinPartition.SourceSourceBoundBasinPartition

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinPartition.BlockExact

open Lean Elab Term Command Tactic SourceData
open scoped BigOperators
noncomputable section

def xcField : Fin 3 → Field
  | 0 => 0
  | 1 => 6
  | 2 => 7

def blockAccount (block : GridBlock) : Prop :=
  ((∑ bucket : Bucket, Source.bucketCounts block bucket : Nat) : Int) = oldBlockValue block 1 ∧
  (∀ field : Field, ∑ bucket : Bucket, Source.bucketIntegrals block bucket field = Source.blockPointSums block field) ∧
  (∀ field : Field, Source.blockPointSums block field =
    Source.blockFloatSums block field + Source.blockPointRoundingResidual block field) ∧
  (∀ field : Fin 3, Source.blockFloatSums block (xcField field) =
    1000 * oldBlockValue block (field.val + 2) + Source.blockGridToOldXcResidual block field) ∧
  (∀ bucket : Bucket, 4 * (Source.bucketIntegrals block bucket 1 - Source.bucketIntegrals block bucket 2) -
    Source.bucketIntegrals block bucket 3 = Source.blockBucketGaugeResidual block bucket)

elab "proveBasinBlockAccounts" : command => liftTermElabM do
  for i in [:229] do
    let inside ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit i) (mkNatLit 229))
    let index := mkApp3 (mkConst ``Fin.mk) (mkNatLit 229) (mkNatLit i) inside
    let type := mkApp (mkConst ``blockAccount) index
    let expanded := (← getConstInfo ``blockAccount).value!.bindingBody!.instantiate1 index
    let value ← instantiateMVars (← Meta.mkDecideProof expanded)
    let name := (← getCurrNamespace) ++ Name.mkSimple s!"block{i}"
    addDecl (.thmDecl { name, levelParams := [], type, value })

proveBasinBlockAccounts

elab "closeBasinBlockAccounts" : tactic => do
  let goals ← getGoals
  unless goals.length == 229 do throwError "Basin block proof census"
  for (goal, i) in goals.zipIdx do
    goal.assign (mkConst ((← getCurrNamespace) ++ Name.mkSimple s!"block{i}"))
  setGoals []

theorem everyBlock (block : GridBlock) : blockAccount block := by
  fin_cases block
  closeBasinBlockAccounts

end
end LAlanine40K2025.BasinPartition.BlockExact
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
