import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Relations.GeneratedRelationRole

/-!
# Relation-indexed source-owned future freedom

Future authority is fixed inside the relation compiler itself.  For one
generated relation, source/target continuation fibres are therefore functions
of its generated lineage; consumers cannot pair that relation with caller
finsets or an independently supplied future face.

The common finite carrier enumerates possible codes only.  Habitable and
actionable codes are calculated by filtering dependent continuation fibres,
so no completed future table or coverage certificate is stored.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Relations

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal

universe u v w x

variable {Source : Type u} {State : Type v}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {actorFace : M0BoundaryFace.{u, v, w} occurrenceOf}

namespace SourceOwnedRelationRoleCompiler

variable
    (compiler : SourceOwnedRelationRoleCompiler.{u, v, w, x}
      occurrenceOf game actorFace)

instance instFutureCodeDecidableEq :
    DecidableEq compiler.FutureCode :=
  compiler.futureCodeDecidableEq

/-- Exact inhabited future codes for one generated relation and edge side. -/
noncomputable def futureCodesAt
    (relation : compiler.GeneratedRelation) (side : EdgeSide) :
    Finset compiler.FutureCode := by
  classical
  exact compiler.futureCodeCarrier.filter fun code =>
    Nonempty (compiler.FutureContinuationAt relation.1 side code)

theorem mem_futureCodesAt_iff
    (relation : compiler.GeneratedRelation) (side : EdgeSide)
    (code : compiler.FutureCode) :
    code ∈ compiler.futureCodesAt relation side ↔
      code ∈ compiler.futureCodeCarrier ∧
      Nonempty
        (compiler.FutureContinuationAt relation.1 side code) := by
  classical
  simp [futureCodesAt]

/-- Actionability is an additional non-idle filter of inhabited codes. -/
noncomputable def actionableFutureCodesAt
    (relation : compiler.GeneratedRelation) (side : EdgeSide) :
    Finset compiler.FutureCode := by
  classical
  exact (compiler.futureCodesAt relation side).filter fun code =>
    ¬ compiler.futureIdle code

theorem mem_actionableFutureCodesAt_iff
    (relation : compiler.GeneratedRelation) (side : EdgeSide)
    (code : compiler.FutureCode) :
    code ∈ compiler.actionableFutureCodesAt relation side ↔
      code ∈ compiler.futureCodeCarrier ∧
      Nonempty
        (compiler.FutureContinuationAt relation.1 side code) ∧
      ¬ compiler.futureIdle code := by
  classical
  simp [actionableFutureCodesAt, mem_futureCodesAt_iff, and_assoc]

/-- Every admitted code exposes a dependent continuation and its fixed
domain-native witness. -/
theorem futureCode_has_witnessed_continuation
    (relation : compiler.GeneratedRelation) {side : EdgeSide}
    {code : compiler.FutureCode}
    (member : code ∈ compiler.futureCodesAt relation side) :
    ∃ continuation :
        compiler.FutureContinuationAt relation.1 side code,
      compiler.FutureContinuationWitnessAt relation.1 side code
        continuation := by
  rcases (compiler.mem_futureCodesAt_iff relation side code).mp member with
    ⟨_inCarrier, ⟨continuation⟩⟩
  exact ⟨continuation,
    compiler.futureContinuation_witnessed relation.1 side code
      continuation⟩

/-- Both future boundaries remain states of the same actual occurrence. -/
theorem futureBoundaryState_mem_occurrence
    (relation : compiler.GeneratedRelation) (side : EdgeSide) :
    compiler.futureBoundaryState relation.1 side ∈
      game.occurrence.trace :=
  compiler.futureBoundaryState_mem relation.1 side

end SourceOwnedRelationRoleCompiler
end Relations
end Society
end ProcessGame
end SaturationMonoid
