import H0mework.Realization.Operations.Substitution.Source
import H0mework.Versions.PR.SecondEdition.SaturationMonoid.GenericFoundation.Operations.Native.Substitution.Source

/-! The actual source action migrates complete paired relation witnesses from the literal next. -/

set_option autoImplicit false

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Relations

open SourceOperationEffects SourceOperationDerivations SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation Substitution

noncomputable section

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}

abbrev PairedValue := PairValue (Field.Value process)

def pairedBinding :
    ∀ sort, Field.Var process sort → Expr (PairedValue (process := process)) (Field.Var process) sort :=
  fun sort name => .linear (s := sort) (t := sort) (pairLinear (sourceAction process).toAddMonoidHom)
    (.var (s := sort) name)

def pairedEnvironment (runtime : LivingRuntimeState process) :=
  pairEnvironment (oldEnv runtime) (incrementEnv runtime)

theorem actual_environment (runtime : LivingRuntimeState process) :
    SourceSubstitution.sourceEnvironment (pairedBinding (process := process)) (pairedEnvironment runtime) =
      pairedEnvironment runtime.tick.next := by
  funext sort name
  apply Prod.ext
  · exact sourceAction_point runtime
  · exact (map_sub (sourceAction process) _ _).trans
      (congrArg₂ (· - ·) (sourceAction_point runtime.tick.next) (sourceAction_point runtime))

def index (runtime : LivingRuntimeState process) :
    RelationIndex ℤ (pairedEnvironment runtime.tick.next) PUnit.unit →
      RelationIndex ℤ (pairedEnvironment runtime) PUnit.unit
  | .inl proof => .inl ⟨proof.1.subst pairedBinding, proof.2.1.subst pairedBinding,
      Derivation.subst pairedBinding (pairedEnvironment runtime) (by
        change Derivation (SourceSubstitution.sourceEnvironment pairedBinding (pairedEnvironment runtime))
          proof.1 proof.2.1
        rw [actual_environment runtime]
        exact proof.2.2)⟩
  | .inr scalar => .inr scalar

def relationWords (runtime : LivingRuntimeState process) :
    (RelationIndex ℤ (pairedEnvironment runtime.tick.next) PUnit.unit →₀ ℤ) →ₗ[ℤ]
      (RelationIndex ℤ (pairedEnvironment runtime) PUnit.unit →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (index runtime)

theorem index_boundary (runtime : LivingRuntimeState process)
    (generator : RelationIndex ℤ (pairedEnvironment runtime.tick.next) PUnit.unit) :
    relation (R := ℤ) (pairedEnvironment runtime) (index runtime generator) =
      substitution (R := ℤ) pairedBinding
        (relation (R := ℤ) (pairedEnvironment runtime.tick.next) generator) := by
  cases generator with
  | inl proof =>
      simp only [index, relation, map_sub, substitution, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single]
  | inr scalar =>
      exact SourceSubstitution.index_boundary (R := ℤ) (s := PUnit.unit)
        (pairedBinding (process := process)) (pairedEnvironment runtime) (.inr scalar)

theorem boundary_square (runtime : LivingRuntimeState process) :
    (relationMap (R := ℤ) (s := PUnit.unit) (pairedEnvironment runtime)).comp (relationWords runtime) =
      (substitution (R := ℤ) pairedBinding).comp
        (relationMap (R := ℤ) (s := PUnit.unit) (pairedEnvironment runtime.tick.next)) := by
  apply Finsupp.lhom_ext
  intro generator coefficient
  simp only [LinearMap.comp_apply, relationWords, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, relationMap, Finsupp.linearCombination_single, map_smul]
  exact congrArg (fun value => coefficient • value) (index_boundary runtime generator)

end
end SourceOperationNative.Relations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
