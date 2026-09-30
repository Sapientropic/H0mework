import H0mework.Versions.X.Fock.HistoryConditional.GWordMaterial
import H0mework.Versions.X.Fock.CopyGraph.Moments
import H0mework.Versions.X.Fock.CopyGraph.TimeModelTimeRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGWordInverse

open SourceGeneratedActionWords SourceCopyTimeModel
noncomputable section

def letter (depth : Nat) : Fock.Letter depth → SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier
  | .inl _ => SourceJointClockGraph.recover
  | .inr index => SourceCopyGraph.recover depth index

def wordRecover (depth : Nat) (word : List (Fock.Letter depth)) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  word.foldr (fun next rest => (letter depth next).comp rest) (ContinuousLinearMap.id ℂ SourceJointClockGraph.Carrier)

theorem word_mass (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    mass (wordRecover depth word value) = mass value := by
  induction word generalizing value with
  | nil => rfl
  | cons next rest previous =>
      change mass (letter depth next (wordRecover depth rest value)) = _
      cases next with
      | inl marker => exact (recovered_mass _).trans (previous value)
      | inr index => exact previous value

theorem word_hilbert (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) (coordinate : Nat) :
    hilbert (wordRecover depth word value) coordinate =
      hilbert value (SourceCopyWordAffine.execute (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) coordinate) := by
  rw [SourceCopyWordAffine.execute_original]
  induction word generalizing value coordinate with
  | nil => rfl
  | cons next rest previous =>
      change hilbert (letter depth next (wordRecover depth rest value)) coordinate = _
      cases next with
      | inl marker =>
          rw [show letter depth (.inl ()) = SourceJointClockGraph.recover from rfl, recovered_hilbert, previous]
          rfl
      | inr index =>
          change SourceCopyGraph.hilbertRecover depth index (hilbert (wordRecover depth rest value)) coordinate = _
          rw [SourceCopyGraph.recover_coordinate, previous, SourceCopyProgram.index_source, SourceCopyProgram.scale_source]
          rfl

theorem word_clock_balance (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ) *
      SourceJointClockGraph.clock (wordRecover depth word value) +
        ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℂ) * mass value =
      SourceJointClockGraph.clock value := by
  induction word generalizing value with
  | nil =>
      simp only [List.map_nil, SourceCopyWordAffine.compile, List.foldr_nil, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, add_zero]
      rfl
  | cons next rest previous =>
      cases next with
      | inl marker =>
          change ((SourceCopyWordAffine.compile (rest.map SourceCopyNativeWord.encode)).1 : ℂ) *
            SourceJointClockGraph.clock (SourceJointClockGraph.recover (wordRecover depth rest value)) +
            (((SourceCopyWordAffine.compile (rest.map SourceCopyNativeWord.encode)).1 +
              (SourceCopyWordAffine.compile (rest.map SourceCopyNativeWord.encode)).2 : Nat) : ℂ) * mass value = _
          rw [recovered_clock, word_mass, Nat.cast_add]
          calc
            _ = ((SourceCopyWordAffine.compile (rest.map SourceCopyNativeWord.encode)).1 : ℂ) *
                SourceJointClockGraph.clock (wordRecover depth rest value) +
                ((SourceCopyWordAffine.compile (rest.map SourceCopyNativeWord.encode)).2 : ℂ) * mass value := by ring
            _ = _ := previous value
      | inr index =>
          change (((SourceCopyWordAffine.compile (rest.map SourceCopyNativeWord.encode)).1 * (index.val + 1) : Nat) : ℂ) *
            ((SourceCopyProgram.scale depth index : ℂ)⁻¹ * SourceJointClockGraph.clock (wordRecover depth rest value)) +
            ((SourceCopyWordAffine.compile (rest.map SourceCopyNativeWord.encode)).2 : ℂ) * mass value = _
          rw [← SourceCopyProgram.scale_source depth index, Nat.cast_mul]
          calc
            _ = ((SourceCopyWordAffine.compile (rest.map SourceCopyNativeWord.encode)).1 : ℂ) *
                SourceJointClockGraph.clock (wordRecover depth rest value) +
                ((SourceCopyWordAffine.compile (rest.map SourceCopyNativeWord.encode)).2 : ℂ) * mass value := by
              rw [mul_assoc, mul_inv_cancel_left₀ (SourceCopyGraph.scale_nonzero depth index)]
            _ = _ := previous value

theorem word_clock (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    SourceJointClockGraph.clock (wordRecover depth word value) =
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ)⁻¹ *
        (SourceJointClockGraph.clock value -
          ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℂ) * mass value) := by
  have nonzero : ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (SourceCompiledWordOperator.slope_positive _).ne'
  have balance := eq_sub_of_add_eq (word_clock_balance depth word value)
  rw [← balance, inv_mul_cancel_left₀ nonzero]

end
end SourceGWordInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
