import H0mework.Fock.PrimeField.ClockSplittingQuotient

/-! Existing quotient-tower naturality generates the whole prime field's zero-clock lift. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockSplitting

open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery SourcePrimeClockResidual
open CategoryTheory CategoryTheory.Limits

noncomputable section

def quotientTransformation : primeData.quotientTower primeLaws ⟶ jointData.quotientTower jointLaws :=
  NatTrans.ofOpSequence (fun stage => ModuleCat.ofHom (quotientSection stage)) (fun stage => by
    simp only [SourceGeneratedScalarCofinalKernelCompletion.Data.quotientTower,
      Functor.ofOpSequence_map_homOfLE_succ]
    apply ModuleCat.hom_ext
    exact quotient_section_transition stage)

def sectionMap : SourcePrimeCompletion.Field →ₗ[ℤ] JointField := (limMap quotientTransformation).hom

theorem section_restriction (value : SourcePrimeCompletion.Field) (stage : Nat) :
    (jointData.restriction jointLaws stage).hom (sectionMap value) =
      quotientSection stage ((primeData.restriction primeLaws stage).hom value) :=
  ConcreteCategory.congr_hom (limMap_π quotientTransformation (Opposite.op stage)) value

private def two : Nat.Primes := ⟨2, Nat.prime_two⟩

theorem section_prefix (value : SourcePrimeCompletion.Field) (stage : Nat) :
    stageRead nativeAction jointObservation stage (sectionMap value) =
      fun index => (stageRead nativeAction observation stage value index,
        (index.val : ℤ) * SourcePrimeCompletion.mass value) := by
  obtain ⟨source, agrees⟩ := primeData.finite_lift primeLaws value stage
  have actual := congrArg (jointData.stageRealization stage) (section_restriction value stage)
  rw [← agrees stage le_rfl, quotient_section_source] at actual
  change stageRead nativeAction jointObservation stage (sectionMap value) =
    prefixEvaluator nativeAction jointObservation stage (correction stage source) at actual
  have sourceReads := congrArg (primeData.stageRealization stage) (agrees stage le_rfl)
  change prefixEvaluator nativeAction observation stage source = stageRead nativeAction observation stage value at sourceReads
  have first := congrFun (congrArg (primeData.stageRealization 0) (agrees 0 (Nat.zero_le _))) (0 : Fin 1)
  change observation source = SourcePrimeCompletion.read 0 value at first
  have mass : SourceSuccessorBoundary.mass ℤ source = SourcePrimeCompletion.mass value := by
    have sourceLaw := LinearMap.congr_fun (SourcePrimeCompletion.source_row_is_prime_read two 0) source
    change SourceSuccessorBoundary.mass ℤ source = primeRead two (observation source) at sourceLaw
    exact sourceLaw.trans (congrArg (primeRead two) first)
  rw [actual, corrected_prefix stage stage le_rfl, mass]
  funext index
  exact congrArg (fun prime => (prime, (index.val : ℤ) * SourcePrimeCompletion.mass value)) (congrFun sourceReads index)

theorem section_prime (value : SourcePrimeCompletion.Field) : primeProjection (sectionMap value) = value := by
  apply Limits.Concrete.limit_ext (primeData.quotientTower primeLaws)
  intro stage
  apply primeData.stageRealization_injective stage.unop
  change stageRead nativeAction observation stage.unop (primeProjection (sectionMap value)) =
    stageRead nativeAction observation stage.unop value
  rw [projection_prefix, section_prefix]

theorem section_clock (value : SourcePrimeCompletion.Field) : clockRead (sectionMap value) = 0 := by
  change (stageRead nativeAction jointObservation 0 (sectionMap value) 0).2 = 0
  rw [section_prefix]
  exact zero_mul _

end
end SourcePrimeClockSplitting
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
