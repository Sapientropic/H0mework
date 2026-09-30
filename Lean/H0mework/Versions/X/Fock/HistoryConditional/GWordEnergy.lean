import H0mework.Versions.X.Fock.HistoryConditional.GWordSource
import H0mework.Versions.X.Fock.CopyGraph.TimeModelTime

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompiledGWord

open SourceGeneratedActionWords SourceCopyTimeModel
noncomputable section

theorem mass_effect (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    mass (effect depth word value) = mass value := by
  induction word generalizing value with
  | nil => rw [effect_nil]; rfl
  | cons next rest previous =>
      rw [effect_cons]
      change mass (effect depth rest (letter depth next value)) = _
      rw [previous]
      cases next <;> rfl

theorem joint_energy (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    ‖SourceJointClockGraph.joint (effect depth word value)‖ ^ 2 = ‖SourceJointClockGraph.joint value‖ ^ 2 := by
  induction word generalizing value with
  | nil => rw [effect_nil]; rfl
  | cons next rest previous =>
      rw [effect_cons]
      change ‖SourceJointClockGraph.joint (effect depth rest (letter depth next value))‖ ^ 2 = _
      rw [previous]
      cases next with
      | inl marker =>
          change ‖SourceMassCompletion.action (SourceJointClockGraph.joint value)‖ ^ 2 = _
          rw [SourceMassCompletion.action.norm_map]
      | inr index => exact SourceCopyGraph.joint_norm_sq depth index (SourceJointClockGraph.joint value)

theorem clock_effect (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    SourceJointClockGraph.clock (effect depth word value) =
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ) * SourceJointClockGraph.clock value +
        ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℂ) * mass value := by
  induction word generalizing value with
  | nil =>
      rw [effect_nil]
      simp only [List.map_nil, SourceCopyWordAffine.compile, List.foldr_nil, Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, add_zero]
      rfl
  | cons next rest previous =>
      rw [effect_cons]
      change SourceJointClockGraph.clock (effect depth rest (letter depth next value)) = _
      rw [previous]
      cases next with
      | inl marker =>
          change ((SourceCopyWordAffine.compile (rest.map SourceCopyNativeWord.encode)).1 : ℂ) *
            (SourceJointClockGraph.clock value + mass value) +
            ((SourceCopyWordAffine.compile (rest.map SourceCopyNativeWord.encode)).2 : ℂ) * mass value = _
          simp only [List.map_cons, SourceCopyNativeWord.encode, SourceCopyWordAffine.compile, List.foldr_cons, Nat.cast_add]
          ring
      | inr index =>
          change ((SourceCopyWordAffine.compile (rest.map SourceCopyNativeWord.encode)).1 : ℂ) *
            ((SourceCopyProgram.scale depth index : ℂ) * SourceJointClockGraph.clock value) +
            ((SourceCopyWordAffine.compile (rest.map SourceCopyNativeWord.encode)).2 : ℂ) * mass value = _
          rw [SourceCopyProgram.scale_source]
          simp only [List.map_cons, SourceCopyNativeWord.encode, SourceCopyWordAffine.compile, List.foldr_cons, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          ring

theorem energy (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    ‖effect depth word value‖ ^ 2 = ‖value‖ ^ 2 - ‖SourceJointClockGraph.clock value‖ ^ 2 +
      ‖((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ) * SourceJointClockGraph.clock value +
        ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℂ) * mass value‖ ^ 2 := by
  rw [SourceJointClockGraph.norm_sq, joint_energy, clock_effect, SourceJointClockGraph.norm_sq]
  ring

end
end SourceCompiledGWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
