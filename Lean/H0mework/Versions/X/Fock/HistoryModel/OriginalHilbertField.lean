import H0mework.Versions.X.Fock.HistoryModel.OriginalHilbertSource
import H0mework.Versions.X.Fock.HistoryModel.CompletionSource
import H0mework.Probability.Source.Hilbert

/-! Eliminate the actual observer equality into the original native Field; no second occurrence is introduced. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionObservationHistory SourceGeneratedScalarCofinalTopology

noncomputable section

private def sameObserver {B : Type} [AddCommGroup B] (left right : Carrier Current →ₗ[ℤ] B)
    (same : left = right) : completion (sourceAction nativeStep) left ≃ₗ[ℤ] completion (sourceAction nativeStep) right := by
  subst right
  exact LinearEquiv.refl ℤ _

private theorem sameObserver_source {B : Type} [AddCommGroup B] (left right : Carrier Current →ₗ[ℤ] B)
    (same : left = right) (source : Carrier Current) :
    sameObserver left right same (sourceMap (sourceAction nativeStep) left source) =
      sourceMap (sourceAction nativeStep) right source := by
  subst right
  rfl

private theorem sameObserver_action {B : Type} [AddCommGroup B] (left right : Carrier Current →ₗ[ℤ] B)
    (same : left = right) (value : completion (sourceAction nativeStep) left) :
    sameObserver left right same (endomorphism (sourceAction nativeStep) left value) =
      endomorphism (sourceAction nativeStep) right (sameObserver left right same value) := by
  subst right
  rfl

private theorem sameObserver_uniform {B : Type} [AddCommGroup B] (left right : Carrier Current →ₗ[ℤ] B)
    (same : left = right) :
    @UniformContinuous _ _
      (observationUniform (data (sourceAction nativeStep) left) (compatible (sourceAction nativeStep) left))
      (observationUniform (data (sourceAction nativeStep) right) (compatible (sourceAction nativeStep) right))
      (sameObserver left right same) := by
  subst right
  exact @uniformContinuous_id _
    (observationUniform (data (sourceAction nativeStep) left) (compatible (sourceAction nativeStep) left))

private theorem sameObserver_inverse_uniform {B : Type} [AddCommGroup B] (left right : Carrier Current →ₗ[ℤ] B)
    (same : left = right) :
    @UniformContinuous _ _
      (observationUniform (data (sourceAction nativeStep) right) (compatible (sourceAction nativeStep) right))
      (observationUniform (data (sourceAction nativeStep) left) (compatible (sourceAction nativeStep) left))
      (sameObserver left right same).symm := by
  subst right
  exact @uniformContinuous_id _
    (observationUniform (data (sourceAction nativeStep) left) (compatible (sourceAction nativeStep) left))

def originalField (depth : Nat) : Complete.Carrier depth ≃ₗ[ℤ] Field nativeStep (rawWords depth) :=
  sameObserver (inventory (Fock.actions depth) (Fock.observer depth))
    (observation (rawWords depth)) (observation_rawWords depth).symm

theorem original_point (depth : Nat) (current : Current) :
    originalField depth (Complete.point depth current) = fieldPoint nativeStep (rawWords depth) current :=
  sameObserver_source _ _ (observation_rawWords depth).symm (sourcePoint current)

theorem original_action (depth : Nat) (value : Complete.Carrier depth) :
    originalField depth (Complete.action depth (.inl ()) value) =
      fieldAction nativeStep (rawWords depth) (originalField depth value) := by
  have primary := congrArg (fun action : Complete.Carrier depth →ₗ[ℤ] Complete.Carrier depth =>
    originalField depth (action value)) (complete_primary_original (Fock.actions depth) (Fock.observer depth) (.inl ()))
  exact primary.trans (sameObserver_action _ _ (observation_rawWords depth).symm value)

theorem original_uniform (depth : Nat) :
    @UniformContinuous _ _
      (observationUniform (data (Fock.actions depth (.inl ())) (inventory (Fock.actions depth) (Fock.observer depth)))
        (compatible (Fock.actions depth (.inl ())) (inventory (Fock.actions depth) (Fock.observer depth))))
      (fieldUniform nativeStep (rawWords depth)) (originalField depth) :=
  sameObserver_uniform _ _ (observation_rawWords depth).symm

theorem original_inverse_uniform (depth : Nat) :
    @UniformContinuous _ _ (fieldUniform nativeStep (rawWords depth))
      (observationUniform (data (Fock.actions depth (.inl ())) (inventory (Fock.actions depth) (Fock.observer depth)))
        (compatible (Fock.actions depth (.inl ())) (inventory (Fock.actions depth) (Fock.observer depth))))
      (originalField depth).symm :=
  sameObserver_inverse_uniform _ _ (observation_rawWords depth).symm

end
end SourceGeneratedActionWords.Fock.OriginalHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
