import H0mework.Fock.HistoryConditional.GWordProgramInverse
import H0mework.Fock.HistoryConditional.GWordInverseWord

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGWordInverse

open SourceGeneratedActionWords SourceCopyTimeModel
noncomputable section

def recover (depth : Nat) (word : List (Fock.Letter depth)) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  SourceGProgramInverse.recover (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
    (SourceCompiledWordOperator.slope_positive _)

def residual (depth : Nat) (word : List (Fock.Letter depth)) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  ContinuousLinearMap.id ℂ _ - (SourceCompiledGWord.effect depth word).comp (recover depth word)

theorem word_recover_eq (depth : Nat) (word : List (Fock.Letter depth)) : wordRecover depth word = recover depth word := by
  apply ContinuousLinearMap.ext
  intro value
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change hilbert (wordRecover depth word value) =
        SourceGProgramInverse.hilbertRecover (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
          (SourceCompiledWordOperator.slope_positive _) (hilbert value)
      apply lp.ext
      funext coordinate
      rw [word_hilbert, SourceGProgramInverse.recover_coordinate]
    · change mass (wordRecover depth word value) = mass value
      exact word_mass depth word value
  · change SourceJointClockGraph.clock (wordRecover depth word value) =
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ)⁻¹ *
        (SourceJointClockGraph.clock value -
          ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℂ) * mass value)
    exact word_clock depth word value

theorem recover_nil (depth : Nat) : recover depth [] = ContinuousLinearMap.id ℂ SourceJointClockGraph.Carrier := by
  rw [← word_recover_eq]
  rfl

theorem recover_cons (depth : Nat) (next : Fock.Letter depth) (rest : List (Fock.Letter depth)) :
    recover depth (next :: rest) = (letter depth next).comp (recover depth rest) := by
  rw [← word_recover_eq, ← word_recover_eq]
  rfl

theorem recover_effect (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    recover depth word (SourceCompiledGWord.effect depth word value) = value :=
  SourceGProgramInverse.recover_action _ _ value

theorem reconstruction (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    SourceCompiledGWord.effect depth word (recover depth word value) + residual depth word value = value := by
  change SourceCompiledGWord.effect depth word (recover depth word value) +
    (value - SourceCompiledGWord.effect depth word (recover depth word value)) = value
  abel

theorem mass_recover (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    mass (recover depth word value) = mass value := rfl

theorem hilbert_recover (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) (coordinate : Nat) :
    hilbert (recover depth word value) coordinate =
      hilbert value (SourceCopyWordAffine.execute (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) coordinate) :=
  SourceGProgramInverse.recover_coordinate _ _ (hilbert value) coordinate

end
end SourceGWordInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
