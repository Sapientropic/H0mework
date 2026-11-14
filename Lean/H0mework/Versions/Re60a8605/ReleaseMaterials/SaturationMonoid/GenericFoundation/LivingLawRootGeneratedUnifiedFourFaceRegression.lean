import H0mework.Realization.Perfectification.LivingLawRootGeneratedUnifiedFourFaceKernel
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedSourcePerfectificationRegression

/-!
# Direct consumers for the unified four-face producer

The first instance uses one finite integral carrier and exercises all four
sibling projections, the quotient universal property, and the generated
finite-free ambient.  The second instance uses the countable Finsupp carrier
with the double-dual evaluation.  It is source-injective but not finite, so
the same producer returns a representation/compression residual.  No branch
is supplied by either input.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace UnifiedFourFaceRegression

open UnifiedFourFace
open SourceGeneratedPerfectification
open SourceGeneratedPerfectAmbient
open SourceGeneratedPerfectificationRegression
open CofinalPerfectCompressionNoGo

noncomputable section

/-! ## A finite source-owned occurrence -/

def positiveInput :
    Input Unit Nat Bool Unit Bool Unit Unit ℤ ℤ where
  occurrence := RootedAccountedUnfolding.zero ()
  algebraAt := fun _ => 0
  combinatorialAt := fun _ => true
  topologicalAt := fun _ => ()
  logicalAt := fun _ => true
  relationAt := fun _ => ()
  cochainAt := fun _ => ()
  dualEvaluationAt := fun _ => integerEvaluation
  faithfulAt := fun _ => LinearMap.id

@[simp] theorem positive_projection_roots :
    positiveInput.AlgebraOccurrence.root = 0 ∧
      positiveInput.CombinatorialOccurrence.root = true ∧
      positiveInput.TopologicalOccurrence.root = () ∧
      positiveInput.LogicalOccurrence.root = true := by
  simp [positiveInput]

theorem positive_root_is_same_evaluation :
    RootDualEvaluation positiveInput = integerEvaluation := by
  rfl

theorem positive_canonical_universal :
    ∃! factor : PerfectificationCarrier integerEvaluation →ₗ[ℤ] ℤ,
      factor.comp (SourceGeneratedPerfectification.canonicalMap integerEvaluation) =
        LinearMap.id := by
  exact SourceGeneratedPerfectification.canonicalMap_universal integerEvaluation
    (LinearMap.id) (by
    intro value value_mem
    change value = 0
    change integerEvaluation value = 0 at value_mem
    have evaluated := congrArg (fun functional => functional (1 : ℤ)) value_mem
    simpa [integerEvaluation, LinearMap.lsmul_apply] using evaluated)

theorem positive_ambient_has_finite_free_branch :
    ∃ equivalence :
        SourceGeneratedPerfectAmbient.HyperbolicCarrier
          (RootDualEvaluation positiveInput) ≃ₗ[ℤ]
          Module.Dual ℤ
            (SourceGeneratedPerfectAmbient.HyperbolicCarrier
              (RootDualEvaluation positiveInput)),
      (generate positiveInput).ambientExtension =
        .generated
          (by
            rw [positive_root_is_same_evaluation]
            exact integer_finite_observation_generates_free)
          (by
            exact integer_finite_observation_generates_finite)
          equivalence := by
  change ∃ equivalence :
      SourceGeneratedPerfectAmbient.HyperbolicCarrier integerEvaluation ≃ₗ[ℤ]
        Module.Dual ℤ
          (SourceGeneratedPerfectAmbient.HyperbolicCarrier integerEvaluation),
    (generate positiveInput).ambientExtension =
      .generated integer_finite_observation_generates_free
        integer_finite_observation_generates_finite equivalence
  exact generated_ambient_is_perfect integerEvaluation
    integer_finite_observation_generates_free
    integer_finite_observation_generates_finite

/-! The combinatorial law is consumed through the unique fold, not a table. -/

def positiveFoldLaw :
    CombinatorialFoldLaw Unit Nat Bool Unit Bool Unit Unit ℤ ℤ Bool where
  input := positiveInput
  atOccurrence := fun origin _ => origin
  candidate := fun occurrence => occurrence.root
  commutes := by
    intro origin branches
    rfl

theorem positive_fold_is_generated :
    CombinatorialFoldLaw.generatedFold positiveFoldLaw =
      positiveInput.CombinatorialOccurrence.root := by
  rfl

def positiveTopologyLaw :
    TopologicalRefinementLaw Unit Nat Bool Unit Bool Unit Unit ℤ ℤ Unit where
  input := positiveInput
  refineAt := id
  observationAt := id
  restrictionAt := id
  commutes := by intro value; rfl

theorem positive_topology_refines_same_root :
    positiveTopologyLaw.refinedOccurrence.root = () := by
  simp [positiveTopologyLaw, positiveInput]

def positiveLogicalLaw :
    LogicalDecisionLaw Unit Nat Bool Unit Bool Unit Unit ℤ ℤ where
  input := positiveInput
  predicate := fun value => value
  decideAt := by intro value; exact inferInstance

theorem positive_logic_has_witness :
    positiveLogicalLaw.predicate true ∨ ¬ positiveLogicalLaw.predicate true := by
  exact positiveLogicalLaw.outcome_exhaustive true

theorem positive_generated_package_total : Nonempty (Generated positiveInput) :=
  generated_total positiveInput

theorem positive_generated_readback :
    (generate positiveInput).embedding.comp (generate positiveInput).canonical =
      RootDualEvaluation positiveInput :=
  generated_dual_readback positiveInput

theorem positive_canonical_perfect_pair_readback :
    (generate positiveInput).canonicalPerfectPair.inclusion.comp
        (generate positiveInput).canonicalPerfectPair.map =
      SourceGeneratedPerfectification.dualEmbedding
        (RootDualEvaluation positiveInput) :=
  SourceGeneratedCanonicalPerfectPair.generated_readback
    (RootDualEvaluation positiveInput)

def positiveIdentityMorphism :
    SourceMorphism positiveInput Unit Nat Bool Unit Bool Unit Unit ℤ ℤ
      positiveInput where
  sourceMap := id
  occurrence_map := by simp [positiveInput]
  carrierMap := LinearMap.id
  dualMap := LinearMap.id
  naturality := by
    apply LinearMap.ext
    intro value
    rfl

theorem positive_identity_root_transport :
    positiveInput.occurrence.root =
      positiveIdentityMorphism.sourceMap positiveInput.occurrence.root := by
  exact SourceMorphism.root_map positiveInput Unit Nat Bool Unit Bool Unit Unit ℤ ℤ
    positiveInput positiveIdentityMorphism

theorem positive_identity_dual_transport :
    (dualEmbedding positiveInput).comp
        (inducedPerfectificationMap positiveInput Unit Nat Bool Unit Bool Unit Unit
          ℤ ℤ positiveInput positiveIdentityMorphism) =
      (SourceGeneratedPerfectification.inducedDualTarget
        positiveIdentityMorphism.dualMap).comp (dualEmbedding positiveInput) :=
  dualEmbedding_naturality positiveInput Unit Nat Bool Unit Bool Unit Unit ℤ ℤ
    positiveInput positiveIdentityMorphism

theorem positive_identity_transport_composes :
    UnifiedFourFace.inducedPerfectificationMap positiveInput Unit Nat Bool Unit Bool Unit Unit
      ℤ ℤ positiveInput
      (UnifiedFourFace.SourceMorphism.comp positiveInput positiveInput positiveInput
        positiveIdentityMorphism positiveIdentityMorphism) =
      (UnifiedFourFace.inducedPerfectificationMap positiveInput Unit Nat Bool Unit Bool Unit Unit
        ℤ ℤ positiveInput positiveIdentityMorphism).comp
        (UnifiedFourFace.inducedPerfectificationMap positiveInput Unit Nat Bool Unit Bool Unit Unit
          ℤ ℤ positiveInput positiveIdentityMorphism) :=
  UnifiedFourFace.inducedPerfectificationMap_comp_morphism positiveInput positiveInput positiveInput
    positiveIdentityMorphism positiveIdentityMorphism

/-! ## An infinite source-owned occurrence -/

abbrev InfiniteCarrier := ℕ →₀ ℤ

def infiniteInput :
    Input Unit Nat Bool Unit Bool Unit Unit InfiniteCarrier
      (Module.Dual ℤ InfiniteCarrier) where
  occurrence := RootedAccountedUnfolding.zero ()
  algebraAt := fun _ => 0
  combinatorialAt := fun _ => false
  topologicalAt := fun _ => ()
  logicalAt := fun _ => false
  relationAt := fun _ => ()
  cochainAt := fun _ => ()
  dualEvaluationAt := fun _ => Module.Dual.eval ℤ InfiniteCarrier
  faithfulAt := fun _ => LinearMap.id

theorem infinite_root_evaluation_injective :
    Function.Injective (RootDualEvaluation infiniteInput) := by
  change Function.Injective (Module.Dual.eval ℤ InfiniteCarrier)
  intro left right equality
  apply Finsupp.ext
  intro index
  have evaluated := LinearMap.congr_fun equality (Finsupp.lapply index)
  simpa [Module.Dual.eval] using evaluated

theorem infinite_perfectification_not_finite :
    ¬ Module.Finite ℤ (Perfectification infiniteInput) := by
  change ¬ Module.Finite ℤ
    (PerfectificationCarrier (Module.Dual.eval ℤ InfiniteCarrier))
  intro finiteP
  let _ : Module.Finite ℤ
      (PerfectificationCarrier (Module.Dual.eval ℤ InfiniteCarrier)) := finiteP
  have canonical_injective : Function.Injective
      (SourceGeneratedPerfectification.canonicalMap
        (Module.Dual.eval ℤ InfiniteCarrier)) := by
    intro left right equality
    have mapped := congrArg
      (SourceGeneratedPerfectification.dualEmbedding
        (Module.Dual.eval ℤ InfiniteCarrier)) equality
    exact infinite_root_evaluation_injective (by
      change (Module.Dual.eval ℤ InfiniteCarrier) left =
        (Module.Dual.eval ℤ InfiniteCarrier) right
      simpa only [← LinearMap.comp_apply,
        SourceGeneratedPerfectification.dualEmbedding_comp_canonicalMap] using mapped)
  let equivalence : InfiniteCarrier ≃ₗ[ℤ]
      PerfectificationCarrier (Module.Dual.eval ℤ InfiniteCarrier) :=
    LinearEquiv.ofBijective
      (SourceGeneratedPerfectification.canonicalMap
        (Module.Dual.eval ℤ InfiniteCarrier))
      ⟨canonical_injective, Submodule.mkQ_surjective _⟩
  have finiteCarrier : Module.Finite ℤ InfiniteCarrier :=
    Module.Finite.equiv equivalence.symm
  exact CofinalPerfectCompressionNoGo.natFinsupp_not_moduleFinite finiteCarrier

theorem infinite_ambient_is_residual :
    ∃ notFinite : ¬ Module.Finite ℤ (Perfectification infiniteInput),
      (generate infiniteInput).ambientExtension =
        .representationResidual notFinite := by
  refine ⟨infinite_perfectification_not_finite, ?_⟩
  simp [generate, ambientExtensionDisposition,
    SourceGeneratedPerfectAmbient.settlePerfectAmbientExtension,
    infinite_perfectification_not_finite]

theorem infinite_no_finite_free_compression :
    ¬ Nonempty
      (FiniteFreeSurjectiveCompressionAt InfiniteCarrier) :=
  CofinalPerfectCompressionNoGo.natFinsupp_no_finiteFreeSurjectiveCompression

theorem infinite_canonical_perfect_pair_readback :
    (generate infiniteInput).canonicalPerfectPair.inclusion.comp
        (generate infiniteInput).canonicalPerfectPair.map =
      SourceGeneratedPerfectification.dualEmbedding
        (RootDualEvaluation infiniteInput) :=
  SourceGeneratedCanonicalPerfectPair.generated_readback
    (RootDualEvaluation infiniteInput)

example : True := by
  fail_if_success exact positive_generated_package_total
  fail_if_success exact infinite_ambient_is_residual
  trivial

#print axioms positive_canonical_universal
#print axioms positive_ambient_has_finite_free_branch
#print axioms positive_fold_is_generated
#print axioms positive_topology_refines_same_root
#print axioms positive_logic_has_witness
#print axioms positive_identity_root_transport
#print axioms positive_identity_dual_transport
#print axioms positive_canonical_perfect_pair_readback
#print axioms positive_identity_transport_composes
#print axioms infinite_perfectification_not_finite
#print axioms infinite_ambient_is_residual
#print axioms infinite_no_finite_free_compression
#print axioms infinite_canonical_perfect_pair_readback

end
end UnifiedFourFaceRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
