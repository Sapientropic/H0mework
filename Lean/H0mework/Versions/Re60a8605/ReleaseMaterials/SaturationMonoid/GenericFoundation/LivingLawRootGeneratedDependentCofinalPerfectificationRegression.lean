import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedDependentCofinalPerfectificationKernel
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedDependentCarrierRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.LivingLawConstructiveFoundationIntegrationRegression

/-!
# Direct consumers for the dependent cofinal producer

This regression keeps one source-indexed carrier family and installs the
cofinal completion only at the selected root occurrence.  The finite payload
exercises the generated perfectification/ambient disposition; the infinite
payload reuses the actual persistent residual witness from the cofinal tower.
The two outcomes are produced by the same generic interface, with no branch
marker supplied by a domain consumer.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace DependentCofinalRegression

open DependentCarrier
open DependentCarrierRegression
open DependentCofinal
open SourceGeneratedPerfectification
open SourceGeneratedPerfectAmbient
open CofinalKernelCompletion
open CofinalKernelCompletion.RootGeneratedCofinalKernelCompletionAt
open CofinalCoverageResidualTower
open CofinalCoverageResidualTower.RootGeneratedCofinalCoverageResidualTowerAt
open ConstructiveFoundationIntegrationRegression

noncomputable section

abbrev GeneratorFamily (_ : Bool) : Type := Unit
abbrev StageCarrierFamily (source : Bool) (_stage : Nat) : Type :=
  match source with
  | true => ℤ
  | false => Finsupp Nat Int

instance generatorFamilyAdd : ∀ source, AddCommGroup (GeneratorFamily source) := by
  intro source
  infer_instance

instance stageCarrierFamilyAdd : ∀ source stage,
    AddCommGroup (StageCarrierFamily source stage) := by
  intro source stage
  cases source <;> simp only [StageCarrierFamily] <;> infer_instance

def positiveData : AdditiveCofinalEvaluatorData
    (GeneratorFamily true) (StageCarrierFamily true) where
  evaluator := fun _ => 0
  transition := fun _ => AddMonoidHom.id _

def negativeData : AdditiveCofinalEvaluatorData
    (GeneratorFamily false) (StageCarrierFamily false) where
  evaluator := fun _ => 0
  transition := fun _ => AddMonoidHom.id _

def positiveCofinalOccurrence : RootedAccountedUnfolding
    (Bool × AdditiveCofinalEvaluatorData
      (GeneratorFamily true) (StageCarrierFamily true)) :=
  RootedAccountedUnfolding.zero (true, positiveData)

def negativeCofinalOccurrence : RootedAccountedUnfolding
    (Bool × AdditiveCofinalEvaluatorData
      (GeneratorFamily false) (StageCarrierFamily false)) :=
  RootedAccountedUnfolding.zero (false, negativeData)

theorem positiveCompatibility :
    GeneratedCompatibilityCalculationAt
      (RootGeneratedCofinalKernelCompletionAt.generate
        (dependentOccurrence := positiveCofinalOccurrence)) := by
  apply RootGeneratedCofinalKernelCompletionAt.generateCompatibility
  intro stage
  ext generator
  rfl

theorem negativeCompatibility :
    GeneratedCompatibilityCalculationAt
      (RootGeneratedCofinalKernelCompletionAt.generate
        (dependentOccurrence := negativeCofinalOccurrence)) := by
  apply RootGeneratedCofinalKernelCompletionAt.generateCompatibility
  intro stage
  ext generator
  rfl

def positiveProfile :
    ProfileT Bool AlgebraFamily CombinatorialFamily TopologicalFamily
      LogicalFamily RelationFamily CochainFamily CarrierFamily DualFamily
      ActualFamily GeneratorFamily StageCarrierFamily where
  base := positiveInput
  cofinalOccurrence := positiveCofinalOccurrence
  compatibility := positiveCompatibility
  cofinal_root_alignment := by
    rfl
  completionEvaluation := by
    exact 0

def negativeProfile :
    ProfileT Bool AlgebraFamily CombinatorialFamily TopologicalFamily
      LogicalFamily RelationFamily CochainFamily CarrierFamily DualFamily
      ActualFamily GeneratorFamily StageCarrierFamily where
  base := negativeInput
  cofinalOccurrence := negativeCofinalOccurrence
  compatibility := negativeCompatibility
  cofinal_root_alignment := by
    rfl
  completionEvaluation := by
    exact 0

/-! A root whose cofinal data is the actual infinite-rank residual source. -/

abbrev UnitGeneratorFamily (_ : Unit) : Type := Unit
abbrev UnitStageCarrierFamily (_ : Unit) (_stage : Nat) : Type := Finsupp Nat Int
abbrev UnitCarrierFamily (_ : Unit) : Type := Finsupp Nat Int
abbrev UnitDualFamily (_ : Unit) : Type := Module.Dual ℤ (Finsupp Nat Int)
abbrev UnitActualFamily (_ : Unit) : Type := Finsupp Nat Int
abbrev UnitAlgebraFamily (_ : Unit) : Type := Unit
abbrev UnitCombinatorialFamily (_ : Unit) : Type := Unit
abbrev UnitTopologicalFamily (_ : Unit) : Type := Unit
abbrev UnitLogicalFamily (_ : Unit) : Type := Unit
abbrev UnitRelationFamily (_ : Unit) : Type := Unit
abbrev UnitCochainFamily (_ : Unit) : Type := Unit

instance unitCarrierFamilyAdd : ∀ source, AddCommGroup (UnitCarrierFamily source) := by
  intro source
  infer_instance

instance unitDualFamilyAdd : ∀ source, AddCommGroup (UnitDualFamily source) := by
  intro source
  infer_instance

instance unitActualFamilyAdd : ∀ source, AddCommGroup (UnitActualFamily source) := by
  intro source
  infer_instance

instance unitGeneratorFamilyAdd : ∀ source, AddCommGroup (UnitGeneratorFamily source) := by
  intro source
  infer_instance

instance unitStageCarrierFamilyAdd : ∀ source stage,
    AddCommGroup (UnitStageCarrierFamily source stage) := by
  intro source stage
  infer_instance

def residualInput :
    Input Unit UnitAlgebraFamily UnitCombinatorialFamily UnitTopologicalFamily
      UnitLogicalFamily UnitRelationFamily UnitCochainFamily UnitCarrierFamily
      UnitDualFamily UnitActualFamily where
  occurrence := RootedAccountedUnfolding.zero ()
  algebraAt := fun _ => ()
  combinatorialAt := fun _ => ()
  topologicalAt := fun _ => ()
  logicalAt := fun _ => ()
  relationAt := fun _ => ()
  cochainAt := fun _ => ()
  dualEvaluationAt := fun _ => Module.Dual.eval ℤ (Finsupp Nat Int)
  faithfulAt := fun _ => LinearMap.id

def residualProfile :
    ProfileT Unit UnitAlgebraFamily UnitCombinatorialFamily
      UnitTopologicalFamily UnitLogicalFamily UnitRelationFamily
      UnitCochainFamily UnitCarrierFamily UnitDualFamily UnitActualFamily
      UnitGeneratorFamily UnitStageCarrierFamily where
  base := residualInput
  cofinalOccurrence := InfiniteRankResidualExample.residualDependentOccurrence
  compatibility := InfiniteRankResidualExample.residualCompatibility
  cofinal_root_alignment := by
    rfl
  completionEvaluation := by
    exact 0

theorem positive_package_total :
    Nonempty (DependentCofinalGenerated positiveProfile) :=
  generated_total positiveProfile

theorem positive_perfectification_readback :
    (UniversalCofinalPerfectification.dualEmbedding
      (rootFace positiveProfile) (rootCalculation positiveProfile)
      (rootEvaluation positiveProfile)).comp
      (UniversalCofinalPerfectification.canonicalMap
        (rootFace positiveProfile) (rootCalculation positiveProfile)
        (rootEvaluation positiveProfile)) =
      rootEvaluation positiveProfile :=
  perfectification_readback positiveProfile

theorem positive_canonical_perfect_pair_readback :
    (generate positiveProfile).canonicalPerfectPair.inclusion.comp
      (generate positiveProfile).canonicalPerfectPair.map =
      SourceGeneratedPerfectification.dualEmbedding
        (rootEvaluation positiveProfile) :=
  canonicalPerfectPair_readback positiveProfile

def positiveGeneratedDualObservation :
    SourceGeneratedPerfectification.PerfectificationCarrier
        (rootEvaluation positiveProfile) →ₗ[ℤ]
      SourceGeneratedCanonicalPerfectPair.GeneratedDual
        (rootEvaluation positiveProfile) :=
  SourceGeneratedCanonicalPerfectPair.generatedDualMap
    (rootEvaluation positiveProfile)

theorem positive_root_alignment_reused :
    (rootOccurrence positiveProfile).map Prod.fst =
      positiveProfile.base.occurrence :=
  root_alignment positiveProfile

theorem positive_cofinal_zero_evaluation :
    rootEvaluation positiveProfile = 0 := by
  rfl

theorem positive_cofinal_perfectification_finite :
    Module.Finite ℤ
      (SourceGeneratedPerfectification.PerfectificationCarrier
        (rootEvaluation positiveProfile)) := by
  rw [positive_cofinal_zero_evaluation]
  letI : Subsingleton
      (SourceGeneratedPerfectification.PerfectificationCarrier
        (0 : rootCompletedCarrier positiveProfile →ₗ[ℤ]
          Module.Dual ℤ (DualFamily positiveProfile.base.occurrence.root))) := by
    constructor
    intro left right
    obtain ⟨left, rfl⟩ := Submodule.mkQ_surjective _ left
    obtain ⟨right, rfl⟩ := Submodule.mkQ_surjective _ right
    apply sub_eq_zero.mp
    apply (QuotientAddGroup.eq_zero_iff (left - right)).2
    simp
  let map : ℤ →ₗ[ℤ]
      SourceGeneratedPerfectification.PerfectificationCarrier
        (0 : rootCompletedCarrier positiveProfile →ₗ[ℤ]
          Module.Dual ℤ (DualFamily positiveProfile.base.occurrence.root)) := 0
  apply Module.Finite.of_surjective map
  intro value
  refine ⟨0, ?_⟩
  exact Subsingleton.elim _ _

theorem positive_cofinal_perfectification_free :
    Module.Free ℤ
      (SourceGeneratedPerfectification.PerfectificationCarrier
        (rootEvaluation positiveProfile)) := by
  rw [positive_cofinal_zero_evaluation]
  letI : Subsingleton
      (SourceGeneratedPerfectification.PerfectificationCarrier
        (0 : rootCompletedCarrier positiveProfile →ₗ[ℤ]
          Module.Dual ℤ (DualFamily positiveProfile.base.occurrence.root))) := by
    constructor
    intro left right
    obtain ⟨left, rfl⟩ := Submodule.mkQ_surjective _ left
    obtain ⟨right, rfl⟩ := Submodule.mkQ_surjective _ right
    apply sub_eq_zero.mp
    apply (QuotientAddGroup.eq_zero_iff (left - right)).2
    simp
  exact Module.Free.of_subsingleton ℤ _

theorem positive_generated_dual_finite :
    Module.Finite ℤ
      (SourceGeneratedCanonicalPerfectPair.GeneratedDual
        (rootEvaluation positiveProfile)) := by
  letI : Module.Finite ℤ
      (SourceGeneratedPerfectification.PerfectificationCarrier
        (rootEvaluation positiveProfile)) :=
    positive_cofinal_perfectification_finite
  exact Module.Finite.equiv
    (SourceGeneratedCanonicalPerfectPair.perfectEquiv
      (rootEvaluation positiveProfile))

theorem positive_generated_dual_free :
    Module.Free ℤ
      (SourceGeneratedCanonicalPerfectPair.GeneratedDual
        (rootEvaluation positiveProfile)) := by
  letI : Module.Free ℤ
      (SourceGeneratedPerfectification.PerfectificationCarrier
        (rootEvaluation positiveProfile)) :=
    positive_cofinal_perfectification_free
  exact Module.Free.of_equiv
    (SourceGeneratedCanonicalPerfectPair.perfectEquiv
      (rootEvaluation positiveProfile))

theorem positiveGeneratedDualObservation_bounded :
    SourceGeneratedPerfectification.settleFiniteObservation
      positiveGeneratedDualObservation =
      .bounded (SourceGeneratedCanonicalPerfectPair.perfectEquiv
        (rootEvaluation positiveProfile)) :=
  SourceGeneratedPerfectification.settleFiniteObservation_eq_bounded_of_bijective
    positiveGeneratedDualObservation
    (SourceGeneratedCanonicalPerfectPair.generatedDualMap_injective
      (rootEvaluation positiveProfile))
    (SourceGeneratedCanonicalPerfectPair.generatedDualMap_surjective
      (rootEvaluation positiveProfile))

theorem positive_bounded_face_generates_determinant :
    boundedObservationDisposition positiveProfile positiveGeneratedDualObservation =
      .determinantEligible
        (SourceGeneratedCanonicalPerfectPair.perfectEquiv
          (rootEvaluation positiveProfile))
        (ExactPerfectEnvelopeBoundedDisposition.GeneratedDeterminantReadout.generate
          positive_generated_dual_free positive_generated_dual_finite) :=
  ExactPerfectEnvelopeBoundedDisposition.settle_eq_determinantEligible
    (rootEvaluation positiveProfile) positiveGeneratedDualObservation
    (SourceGeneratedCanonicalPerfectPair.perfectEquiv
      (rootEvaluation positiveProfile))
    positiveGeneratedDualObservation_bounded
    positive_generated_dual_free positive_generated_dual_finite

theorem positive_cofinal_ambient_generated :
    ∃ equivalence :
        SourceGeneratedPerfectAmbient.HyperbolicCarrier
          (rootEvaluation positiveProfile) ≃ₗ[ℤ]
          Module.Dual ℤ
            (SourceGeneratedPerfectAmbient.HyperbolicCarrier
              (rootEvaluation positiveProfile)),
      (generate positiveProfile).cofinal.ambient =
        .generated positive_cofinal_perfectification_free
          positive_cofinal_perfectification_finite equivalence := by
  exact SourceGeneratedPerfectAmbient.generated_ambient_is_perfect
    (rootEvaluation positiveProfile)
    positive_cofinal_perfectification_free
    positive_cofinal_perfectification_finite

theorem negative_package_total :
    Nonempty (DependentCofinalGenerated negativeProfile) :=
  generated_total negativeProfile

theorem negative_root_alignment_reused :
    (rootOccurrence negativeProfile).map Prod.fst =
      negativeProfile.base.occurrence :=
  root_alignment negativeProfile

theorem negative_cofinal_residual_map_injective :
    Function.Injective
      (UniversalCofinalPerfectification.cofinalResidualMap
        (rootFace negativeProfile) (rootCalculation negativeProfile)) :=
  cofinal_residual_map_injective negativeProfile

theorem negative_persistent_residual_is_not_erased :
    ¬ Subsingleton InfiniteRankResidualExample.residualFace.residualLimit :=
  InfiniteRankResidualExample.residualLimit_not_subsingleton

theorem negative_residual_branch_is_source_owned :
    ¬ Module.Finite Int (Finsupp Nat Int) ∧
      ∃ obstruction : GeneratedFiniteResidualCoordinateObstructionAt
          InfiniteRankResidualExample.residualFace,
        obstruction.residualCoordinate ≠ 0 ∧
        obstruction.representative ∉
          (InfiniteRankResidualExample.residualCompletionFace.evaluator
            obstruction.stage).range :=
  InfiniteRankResidualExample.infinite_rank_persistent_residual_branch

theorem residual_profile_total :
    Nonempty (DependentCofinalGenerated residualProfile) :=
  generated_total residualProfile

theorem residual_profile_coverage_reuses_actual_face :
    (generate residualProfile).cofinal.coverage =
      InfiniteRankResidualExample.residualFace := by
  rfl

theorem residual_canonical_perfect_pair_readback :
    (generate residualProfile).canonicalPerfectPair.inclusion.comp
      (generate residualProfile).canonicalPerfectPair.map =
      SourceGeneratedPerfectification.dualEmbedding
        (rootEvaluation residualProfile) :=
  canonicalPerfectPair_readback residualProfile

theorem residual_profile_persistent_residual :
    ¬ Subsingleton ((generate residualProfile).cofinal.coverage).residualLimit := by
  change ¬ Subsingleton InfiniteRankResidualExample.residualFace.residualLimit
  exact InfiniteRankResidualExample.residualLimit_not_subsingleton

theorem residual_profile_explicit_residual_coordinate :
    ∃ obstruction : GeneratedFiniteResidualCoordinateObstructionAt
        ((generate residualProfile).cofinal.coverage),
      obstruction.residualCoordinate ≠ 0 ∧
      obstruction.representative ∉
        ((rootFace residualProfile).evaluator obstruction.stage).range := by
  change ∃ obstruction : GeneratedFiniteResidualCoordinateObstructionAt
      InfiniteRankResidualExample.residualFace,
    obstruction.residualCoordinate ≠ 0 ∧
      obstruction.representative ∉
        (InfiniteRankResidualExample.residualCompletionFace.evaluator
          obstruction.stage).range
  exact (InfiniteRankResidualExample.infinite_rank_persistent_residual_branch).2

example : True := by
  fail_if_success exact positiveProfile.base.occurrence = negativeProfile.base.occurrence
  fail_if_success exact positive_package_total.some.cofinal.ambient
  trivial

#print axioms positive_package_total
#print axioms positive_perfectification_readback
#print axioms positive_canonical_perfect_pair_readback
#print axioms positive_bounded_face_generates_determinant
#print axioms positive_root_alignment_reused
#print axioms negative_package_total
#print axioms negative_cofinal_residual_map_injective
#print axioms negative_residual_branch_is_source_owned
#print axioms positive_cofinal_ambient_generated
#print axioms residual_profile_total
#print axioms residual_profile_coverage_reuses_actual_face
#print axioms residual_canonical_perfect_pair_readback
#print axioms residual_profile_persistent_residual
#print axioms residual_profile_explicit_residual_coordinate

end
end DependentCofinalRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
