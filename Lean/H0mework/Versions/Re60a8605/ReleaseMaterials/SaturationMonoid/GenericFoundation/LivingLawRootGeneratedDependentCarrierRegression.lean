import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedDependentCarrierKernel
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedUnifiedFourFaceRegression

/-!
# Direct consumers for dependent source carriers

The same source-polymorphic producer is instantiated at two payloads of one
dependent family: the `true` payload has the finite integral carrier, while
the `false` payload has the countable Finsupp carrier.  Sigma-labelled face
roots retain which payload was visited.  The finite payload reaches the
generated ambient branch; the countable payload yields the representation
residual, with no change to the producer or a caller-supplied branch.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace DependentCarrierRegression

open DependentCarrier
open SourceGeneratedPerfectification
open SourceGeneratedPerfectAmbient
open UnifiedFourFaceRegression
open SourceGeneratedPerfectificationRegression
open CofinalPerfectCompressionNoGo

noncomputable section

abbrev InfiniteCarrier := ℕ →₀ ℤ

def CarrierFamily : Bool → Type
  | true => ℤ
  | false => InfiniteCarrier

def DualFamily : Bool → Type
  | true => ℤ
  | false => Module.Dual ℤ InfiniteCarrier

def ActualFamily : Bool → Type
  | true => ℤ
  | false => InfiniteCarrier

instance carrierFamilyAdd : ∀ source, AddCommGroup (CarrierFamily source) := by
  intro source
  cases source <;> simp only [CarrierFamily] <;> infer_instance

instance dualFamilyAdd : ∀ source, AddCommGroup (DualFamily source) := by
  intro source
  cases source <;> simp only [DualFamily] <;> infer_instance

instance actualFamilyAdd : ∀ source, AddCommGroup (ActualFamily source) := by
  intro source
  cases source <;> simp only [ActualFamily] <;> infer_instance

def AlgebraFamily (_ : Bool) : Type := Unit
def CombinatorialFamily (_ : Bool) : Type := Bool
def TopologicalFamily (_ : Bool) : Type := Unit
def LogicalFamily (_ : Bool) : Type := Bool
def RelationFamily (_ : Bool) : Type := Unit
def CochainFamily (_ : Bool) : Type := Unit

def positiveInput :
    Input Bool AlgebraFamily CombinatorialFamily TopologicalFamily LogicalFamily
      RelationFamily CochainFamily CarrierFamily DualFamily ActualFamily where
  occurrence := RootedAccountedUnfolding.zero true
  algebraAt := fun _ => ()
  combinatorialAt := fun source => source
  topologicalAt := fun _ => ()
  logicalAt := fun source => source
  relationAt := fun _ => ()
  cochainAt := fun _ => ()
  dualEvaluationAt := fun source => by
    cases source
    · exact Module.Dual.eval ℤ InfiniteCarrier
    · exact integerEvaluation
  faithfulAt := fun source => by
    cases source
    · exact LinearMap.id
    · exact LinearMap.id

def negativeInput :
    Input Bool AlgebraFamily CombinatorialFamily TopologicalFamily LogicalFamily
      RelationFamily CochainFamily CarrierFamily DualFamily ActualFamily where
  occurrence := RootedAccountedUnfolding.zero false
  algebraAt := fun _ => ()
  combinatorialAt := fun source => source
  topologicalAt := fun _ => ()
  logicalAt := fun source => source
  relationAt := fun _ => ()
  cochainAt := fun _ => ()
  dualEvaluationAt := fun source => by
    cases source
    · exact Module.Dual.eval ℤ InfiniteCarrier
    · exact integerEvaluation
  faithfulAt := fun source => by
    cases source
    · exact LinearMap.id
    · exact LinearMap.id

theorem positive_root_is_finite_carrier :
    RootCarrier positiveInput = ℤ := by
  rfl

theorem positive_root_evaluation_is_integer :
    RootEvaluation positiveInput = integerEvaluation := by
  rfl

theorem positive_generated_total : Nonempty (Generated positiveInput) :=
  generated_total positiveInput

theorem positive_generated_dual_readback :
    (generate positiveInput).embedding.comp (generate positiveInput).canonical =
      RootEvaluation positiveInput :=
  generated_dual_readback positiveInput

def positiveRootIdentity := RootMorphism.id positiveInput

theorem positive_root_identity_preserves_payload :
    positiveInput.occurrence.root =
      positiveRootIdentity.sourceMap positiveInput.occurrence.root :=
  RootMorphism.root_map positiveRootIdentity

theorem positive_root_identity_coimage_map :
    inducedPerfectificationMap positiveInput Bool AlgebraFamily
      CombinatorialFamily TopologicalFamily LogicalFamily RelationFamily
      CochainFamily CarrierFamily DualFamily ActualFamily positiveInput
      positiveRootIdentity = LinearMap.id :=
  inducedPerfectificationMap_id positiveInput

theorem positive_root_composition_coimage_map :
    inducedPerfectificationMap positiveInput Bool AlgebraFamily
      CombinatorialFamily TopologicalFamily LogicalFamily RelationFamily
      CochainFamily CarrierFamily DualFamily ActualFamily positiveInput
      (RootMorphism.comp positiveInput positiveInput positiveInput
        positiveRootIdentity positiveRootIdentity) =
      (inducedPerfectificationMap positiveInput Bool AlgebraFamily
        CombinatorialFamily TopologicalFamily LogicalFamily RelationFamily
        CochainFamily CarrierFamily DualFamily ActualFamily positiveInput
        positiveRootIdentity).comp
        (inducedPerfectificationMap positiveInput Bool AlgebraFamily
          CombinatorialFamily TopologicalFamily LogicalFamily RelationFamily
          CochainFamily CarrierFamily DualFamily ActualFamily positiveInput
          positiveRootIdentity) :=
  inducedPerfectificationMap_comp positiveInput positiveInput positiveInput
    positiveRootIdentity positiveRootIdentity

theorem positive_ambient_is_generated :
    ∃ equivalence :
        HyperbolicCarrier (RootEvaluation positiveInput) ≃ₗ[ℤ]
          Module.Dual ℤ (HyperbolicCarrier (RootEvaluation positiveInput)),
      (generate positiveInput).ambient =
        .generated integer_finite_observation_generates_free
          integer_finite_observation_generates_finite equivalence := by
  change ∃ equivalence :
      HyperbolicCarrier integerEvaluation ≃ₗ[ℤ]
        Module.Dual ℤ (HyperbolicCarrier integerEvaluation),
    (generate positiveInput).ambient =
      .generated integer_finite_observation_generates_free
        integer_finite_observation_generates_finite equivalence
  exact generated_ambient_is_perfect integerEvaluation
    integer_finite_observation_generates_free
    integer_finite_observation_generates_finite

theorem negative_root_evaluation_injective :
    Function.Injective (RootEvaluation negativeInput) := by
  change Function.Injective (Module.Dual.eval ℤ InfiniteCarrier)
  intro left right equality
  apply Finsupp.ext
  intro index
  have evaluated := LinearMap.congr_fun equality (Finsupp.lapply index)
  simpa [Module.Dual.eval] using evaluated

theorem negative_perfectification_not_finite :
    ¬ Module.Finite ℤ (Perfectification negativeInput) := by
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
    exact negative_root_evaluation_injective (by
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

theorem negative_generated_residual :
    ∃ notFinite : ¬ Module.Finite ℤ (Perfectification negativeInput),
      (generate negativeInput).ambient = .representationResidual notFinite := by
  refine ⟨negative_perfectification_not_finite, ?_⟩
  simp [generate, ambientDisposition,
    SourceGeneratedPerfectAmbient.settlePerfectAmbientExtension,
    negative_perfectification_not_finite]

theorem dependent_face_roots_keep_payload :
    (generate positiveInput).algebraFace.root =
        ⟨true, ()⟩ ∧
      (generate negativeInput).algebraFace.root =
        ⟨false, ()⟩ := by
  constructor <;> rfl

example : True := by
  fail_if_success exact positive_generated_total.some.perfectification
  fail_if_success exact negative_generated_residual.some
  trivial

#print axioms positive_generated_total
#print axioms positive_ambient_is_generated
#print axioms positive_root_identity_preserves_payload
#print axioms positive_root_identity_coimage_map
#print axioms positive_root_composition_coimage_map
#print axioms negative_generated_residual
#print axioms dependent_face_roots_keep_payload

end
end DependentCarrierRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
