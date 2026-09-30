import H0mework.Chemistry.LAlanineBasinPartition.SourceSourceBoundBasinPartition

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinPartition.GlobalExact

open Lean Elab Term Command Tactic SourceData
open scoped BigOperators
noncomputable section

def bucketAccount (bucket : Bucket) : Prop :=
  (∑ block : GridBlock, Source.bucketCounts block bucket) = Source.globalBucketCounts bucket ∧
  (∀ field : Field, ∑ block : GridBlock, Source.bucketIntegrals block bucket field = Source.globalBucketIntegrals bucket field) ∧
  4 * (Source.globalBucketIntegrals bucket 1 - Source.globalBucketIntegrals bucket 2) -
    Source.globalBucketIntegrals bucket 3 = Source.globalBucketGaugeResidual bucket

def fieldAccount (field : Field) : Prop :=
  (∑ block : GridBlock, Source.blockPointSums block field) = Source.globalPointSums field ∧
  Source.globalPointSums field = Source.globalFloatSums field + Source.globalPointRoundingResidual field ∧
  (∑ bucket : Bucket, Source.globalBucketIntegrals bucket field) = Source.globalPointSums field

elab "proveBasinGlobalAccounts" : command => liftTermElabM do
  for (family, predicate, count) in [(`bucket, ``bucketAccount, 20), (`field, ``fieldAccount, 8)] do
    for i in [:count] do
      let inside ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit i) (mkNatLit count))
      let index := mkApp3 (mkConst ``Fin.mk) (mkNatLit count) (mkNatLit i) inside
      let type := mkApp (mkConst predicate) index
      let expanded := (← getConstInfo predicate).value!.bindingBody!.instantiate1 index
      let value ← instantiateMVars (← Meta.mkDecideProof expanded)
      let name := (← getCurrNamespace) ++ family ++ Name.mkSimple s!"row{i}"
      addDecl (.thmDecl { name, levelParams := [], type, value })

proveBasinGlobalAccounts

elab "closeBasinGlobalAccounts " family:ident : tactic => do
  for (goal, i) in (← getGoals).zipIdx do
    goal.assign (mkConst ((← getCurrNamespace) ++ family.getId ++ Name.mkSimple s!"row{i}"))
  setGoals []

theorem everyBucket (bucket : Bucket) : bucketAccount bucket := by
  fin_cases bucket
  closeBasinGlobalAccounts bucket

theorem everyField (field : Field) : fieldAccount field := by
  fin_cases field
  closeBasinGlobalAccounts field

end
end LAlanine40K2025.BasinPartition.GlobalExact
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
