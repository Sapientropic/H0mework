import H0mework.Fock.HistoryPolynomial.CopyPolynomial
import H0mework.Fock.HistoryPolynomial.CopyField
import H0mework.Fock.HistoryModel.DynamicAction

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyProgram

open SourceGeneratedActionObservationHistory SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceCyclicModule
noncomputable section

def complete (depth : Nat) : SourceOperationNative.Carrier process →ₗ[ℤ] Fock.Complete.Carrier depth :=
  (sourceMap (Fock.actions depth (.inl ())) (inventory (Fock.actions depth) (Fock.observer depth))).comp whole

def model (depth : Nat) : SourceOperationNative.Carrier process →ₗ[ℤ] Fock.WholeModel depth :=
  (SourceGeneratedActionWords.projection (Fock.actions depth) (Fock.observer depth) (.inl ())).comp whole

theorem complete_is_original_model (depth : Nat) (source : SourceOperationNative.Carrier process) :
    Fock.Complete.originalModel depth (complete depth source) = model depth source :=
  completion_inverse_source (Fock.actions depth) (Fock.observer depth) (.inl ()) (whole source)

def sourceLetter (depth : Nat) : Fock.Letter depth →
    SourceOperationNative.Carrier process →ₗ[ℤ] SourceOperationNative.Carrier process
  | .inl _ => SourcePrimeHistoryRecovery.nativeAction
  | .inr index => action depth index

theorem whole_letter (depth : Nat) (letter : Fock.Letter depth) (source : SourceOperationNative.Carrier process) :
    whole (sourceLetter depth letter source) = Fock.actions depth letter (whole source) := by
  cases letter with
  | inl _value => exact whole_native source
  | inr index => exact whole_copy depth index source

theorem whole_word (depth : Nat) (word : List (Fock.Letter depth))
    (source : SourceOperationNative.Carrier process) :
    whole (run (sourceLetter depth) word source) = run (Fock.actions depth) word (whole source) := by
  induction word generalizing source with
  | nil => rfl
  | cons letter rest previous =>
      change whole (run (sourceLetter depth) rest (sourceLetter depth letter source)) = _
      rw [previous, whole_letter]
      rfl

theorem complete_word (depth : Nat) (word : List (Fock.Letter depth))
    (source : SourceOperationNative.Carrier process) :
    run (Fock.Complete.action depth) word (complete depth source) = complete depth (run (sourceLetter depth) word source) := by
  exact (complete_run_source (Fock.actions depth) (Fock.observer depth) (.inl ()) word (whole source)).trans
    (congrArg (sourceMap (Fock.actions depth (.inl ())) (inventory (Fock.actions depth) (Fock.observer depth)))
      (whole_word depth word source).symm)

theorem model_copy (depth : Nat) (index : Index depth) (p : Polynomial ℤ) :
    Fock.letterAction depth (.inr index) (model depth (program p)) =
      model depth (program (polynomial depth index p)) := by
  rw [polynomial_source]
  exact (advance_source (Fock.actions depth) (Fock.observer depth) (.inl ()) (.inr index) (whole (program p))).trans
    (congrArg (SourceGeneratedActionWords.projection (Fock.actions depth) (Fock.observer depth) (.inl ()))
      (whole_copy depth index (program p)).symm)

theorem complete_copy (depth : Nat) (index : Index depth) (p : Polynomial ℤ) :
    Fock.Complete.action depth (.inr index) (complete depth (program p)) =
      complete depth (program (polynomial depth index p)) := by
  rw [polynomial_source]
  exact complete_word depth [.inr index] (program p)

theorem complete_previous (depth : Nat) (source : SourceOperationNative.Carrier process) :
    Fock.Dynamic.previous depth (complete (depth + 1) source) = complete depth source :=
  Fock.Dynamic.previous_source depth (whole source)

theorem old_material_program (depth : Nat) (index : Index depth) (p : Polynomial ℤ) :
    polynomial (depth + 1) (FamilyModel.Fock.oldIndex depth index) p = polynomial depth index p := rfl

end
end SourceCopyProgram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
