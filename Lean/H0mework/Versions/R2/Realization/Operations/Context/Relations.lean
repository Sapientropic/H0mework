import H0mework.Versions.R2.Realization.Operations.Context.Derivation
import H0mework.Versions.R2.Realization.Operations.Context.Words
import H0mework.Realization.Operations.ScalarPresentation

/-! Every original derivation and scalar relation witness has its generated contextual boundary. -/

set_option autoImplicit false

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Context

open SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarPresentation

noncomputable section

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ sort, AddCommGroup (PhysicalValue sort)]

def embedIndex (readEnv : process.State → Env PhysicalValue PhysicalVar)
    (runtime : LivingRuntimeState process) {s : Sorts} :
    RelationIndex ℤ (readEnv runtime.state) s →
      RelationIndex ℤ (environment (PhysicalValue := PhysicalValue) (point runtime)) (Sum.inl s)
  | .inl proof => .inl ⟨embed readEnv proof.1, embed readEnv proof.2.1, embedDerivation readEnv runtime proof.2.2⟩
  | .inr scalar => .inr scalar

def embedRelationWords (readEnv : process.State → Env PhysicalValue PhysicalVar)
    (runtime : LivingRuntimeState process) {s : Sorts} :
    (RelationIndex ℤ (readEnv runtime.state) s →₀ ℤ) →ₗ[ℤ]
      (RelationIndex ℤ (environment (PhysicalValue := PhysicalValue) (point runtime)) (Sum.inl s) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (embedIndex readEnv runtime)

private theorem constants_embedded (readEnv : process.State → Env PhysicalValue PhysicalVar) {s : Sorts} :
    (words readEnv).comp (constantMap (R := ℤ) (s := s)) =
      (constantMap (R := ℤ) (Value := Value process PhysicalValue) (Var := Var Sorts) (s := Sum.inl s)) := by
  apply Finsupp.lhom_ext
  intro value coefficient
  simp only [LinearMap.comp_apply, words, constantMap, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, embed]

theorem embed_index_boundary (readEnv : process.State → Env PhysicalValue PhysicalVar)
    (runtime : LivingRuntimeState process) {s : Sorts}
    (generator : RelationIndex ℤ (readEnv runtime.state) s) :
    relation (R := ℤ) (environment (PhysicalValue := PhysicalValue) (point runtime))
        (embedIndex readEnv runtime generator) =
      words readEnv (relation (R := ℤ) (readEnv runtime.state) generator) := by
  cases generator with
  | inl proof =>
      simp only [embedIndex, relation, map_sub, words, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  | inr scalar =>
      exact (LinearMap.congr_fun (constants_embedded (s := s) readEnv)
        (ScalarRelationPresentation.relation (R := ℤ) (PhysicalValue s) scalar)).symm

theorem embed_boundary_square (readEnv : process.State → Env PhysicalValue PhysicalVar)
    (runtime : LivingRuntimeState process) {s : Sorts} :
    (relationMap (R := ℤ) (environment (PhysicalValue := PhysicalValue) (point runtime))).comp
      (embedRelationWords (s := s) readEnv runtime) =
        (words readEnv).comp (relationMap (R := ℤ) (s := s) (readEnv runtime.state)) := by
  apply Finsupp.lhom_ext
  intro generator coefficient
  simp only [LinearMap.comp_apply, embedRelationWords, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, relationMap, Finsupp.linearCombination_single, map_smul]
  exact congrArg (fun value => coefficient • value) (embed_index_boundary readEnv runtime generator)

end
end SourceOperationNative.Context
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
