import H0mework.Versions.X.Fock.PrimeField.ClockResidualCofinal
import H0mework.Versions.X.Fock.PrimeField.CompletionConsumer

/-! The original paired completion projects to its prime face while retaining the generated clock residual. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockResidual

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery
open SourceGeneratedScalarCofinalNaturality CategoryTheory

noncomputable section

def primeMorphism : Morphism jointData (data nativeAction observation) where
  generatorMap := LinearMap.id
  stageMap stage := LinearMap.pi fun index =>
    (LinearMap.fst ℤ _ _).comp (LinearMap.proj index)
  transition_naturality _ := rfl
  evaluator_naturality stage := by
    apply LinearMap.ext
    intro source
    funext index
    change (jointObservation ((nativeAction ^ index.val) source)).1 = observation ((nativeAction ^ index.val) source)
    rw [observation_joint]
    rfl

def primeProjection : JointField →ₗ[ℤ] SourcePrimeCompletion.Field :=
  (primeMorphism.completionMorphism jointLaws (compatible nativeAction observation)).hom

theorem projection_source (source : SourceOperationNative.Carrier process) :
    primeProjection (sourceMap nativeAction jointObservation source) = sourceMap nativeAction observation source :=
  ConcreteCategory.congr_hom (primeMorphism.completionMorphism_source_naturality jointLaws (compatible nativeAction observation)) source

private theorem realized_projection (stage : Nat) (value : jointData.StageQuotient stage) :
    (data nativeAction observation).stageRealization stage (primeMorphism.stageQuotientMap stage value) =
      fun index => (jointData.stageRealization stage value index).1 := by
  obtain ⟨source, rfl⟩ := Submodule.mkQ_surjective (jointData.stageKernel stage) value
  change prefixEvaluator nativeAction observation stage source = fun index => (prefixEvaluator nativeAction jointObservation stage source index).1
  funext index
  change observation ((nativeAction ^ index.val) source) = (jointObservation ((nativeAction ^ index.val) source)).1
  rw [observation_joint]
  rfl

theorem projection_prefix (value : JointField) (stage : Nat) :
    stageRead nativeAction observation stage (primeProjection value) =
      fun index => (stageRead nativeAction jointObservation stage value index).1 := by
  have source := ConcreteCategory.congr_hom
    (primeMorphism.completionMorphism_restriction jointLaws (compatible nativeAction observation) stage) value
  have actual := congrArg ((data nativeAction observation).stageRealization stage) source
  exact actual.trans (realized_projection stage ((jointData.restriction jointLaws stage).hom value))

def clockRead : JointField →ₗ[ℤ] ℤ :=
  (LinearMap.snd ℤ _ _).comp ((LinearMap.proj (0 : Fin 1)).comp (stageRead nativeAction jointObservation 0))

theorem residual_prime_zero : primeProjection residual = 0 := by
  apply SourcePrimeCompletion.complete_zero_of_reads_zero
  intro stage
  change stageRead nativeAction observation stage (primeProjection residual) (Fin.last stage) = 0
  rw [projection_prefix, residual_read]

theorem residual_clock_unit : clockRead residual = 1 := by
  change (stageRead nativeAction jointObservation 0 residual 0).2 = 1
  rw [residual_read]

theorem residual_nonzero : residual ≠ 0 := by
  intro vanished
  have unit := residual_clock_unit
  rw [vanished, map_zero] at unit
  exact zero_ne_one unit

theorem residual_not_source : ¬ ∃ source : SourceOperationNative.Carrier process,
    sourceMap nativeAction jointObservation source = residual := by
  rintro ⟨source, same⟩
  have projected := congrArg primeProjection same
  rw [projection_source, residual_prime_zero] at projected
  have empty : source = 0 := SourcePrimeHistoryRecovery.sourceMap_injective sourceOwner
    (projected.trans (map_zero (sourceMap nativeAction observation)).symm)
  rw [empty, map_zero] at same
  exact residual_nonzero same.symm

end
end SourcePrimeClockResidual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
