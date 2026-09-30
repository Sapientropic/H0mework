import H0mework.Versions.X.Fock.HistoryConditional.GWordProgramKernel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompiledGWord

open SourceGeneratedActionWords
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def letter (depth : Nat) : Fock.Letter depth → SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier
  | .inl _ => SourceJointClockGraph.action
  | .inr index => SourceCopyGraph.action depth index

def wordEffect (depth : Nat) (word : List (Fock.Letter depth)) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  word.foldr (fun next rest => rest.comp (letter depth next)) (ContinuousLinearMap.id ℂ SourceJointClockGraph.Carrier)

def effect (depth : Nat) (word : List (Fock.Letter depth)) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  SourceGWordProgram.action (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
    (SourceCompiledWordOperator.slope_positive _)

theorem letter_source (depth : Nat) (next : Fock.Letter depth) (source : SourceOperationNative.Carrier process) :
    letter depth next (SourceJointClockGraph.read (SourceClockComplex.ofNative source)) =
      SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCopyProgram.sourceLetter depth next source)) := by
  cases next with
  | inl marker =>
      change SourceJointClockGraph.action (SourceJointClockGraph.read (SourceClockComplex.ofNative source)) = _
      rw [SourceJointClockGraph.action_source, ← SourceJointClockGraph.native_word_action]
      rfl
  | inr index => exact SourceCopyGraph.action_native depth index source

theorem word_source (depth : Nat) (word : List (Fock.Letter depth)) (source : SourceOperationNative.Carrier process) :
    wordEffect depth word (SourceJointClockGraph.read (SourceClockComplex.ofNative source)) =
      SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.action depth word source)) := by
  rw [SourceCompiledWordOperator.action_original]
  induction word generalizing source with
  | nil => rfl
  | cons next rest previous =>
      change wordEffect depth rest (letter depth next (SourceJointClockGraph.read (SourceClockComplex.ofNative source))) =
        SourceJointClockGraph.read (SourceClockComplex.ofNative (run (SourceCopyProgram.sourceLetter depth) rest
          (SourceCopyProgram.sourceLetter depth next source)))
      rw [letter_source, previous]

theorem source_effect (depth : Nat) (word : List (Fock.Letter depth)) (source : SourceOperationNative.Carrier process) :
    effect depth word (SourceJointClockGraph.read (SourceClockComplex.ofNative source)) =
      SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.action depth word source)) := by
  rw [effect, SourceGWordProgram.action_source, ← SourceGWordProgram.complex_native]
  rfl

theorem word_effect_eq (depth : Nat) (word : List (Fock.Letter depth)) : wordEffect depth word = effect depth word := by
  have same : (wordEffect depth word).toLinearMap.comp SourceJointClockGraph.read =
      (effect depth word).toLinearMap.comp SourceJointClockGraph.read := by
    apply Finsupp.lhom_ext'
    intro coordinate
    apply LinearMap.ext_ring
    change wordEffect depth word (SourceJointClockGraph.read (Finsupp.single coordinate 1)) =
      effect depth word (SourceJointClockGraph.read (Finsupp.single coordinate 1))
    have left := word_source depth word (Finsupp.single coordinate 1)
    have right := source_effect depth word (Finsupp.single coordinate 1)
    simp only [SourceClockComplex.ofNative_single, Int.cast_one] at left right
    exact left.trans right.symm
  apply DFunLike.coe_injective
  exact SourceJointClockGraph.read_denseRange.equalizer (wordEffect depth word).continuous (effect depth word).continuous
    (funext fun source => LinearMap.congr_fun same source)

theorem effect_kernel (depth : Nat) (left right : List (Fock.Letter depth)) :
    effect depth left = effect depth right ↔
      SourceCopyWordAffine.compile (left.map SourceCopyNativeWord.encode) =
        SourceCopyWordAffine.compile (right.map SourceCopyNativeWord.encode) :=
  SourceGWordProgram.action_kernel _ _ _ _

theorem effect_nil (depth : Nat) : effect depth [] = ContinuousLinearMap.id ℂ SourceJointClockGraph.Carrier := by
  rw [← word_effect_eq]
  rfl

theorem effect_cons (depth : Nat) (next : Fock.Letter depth) (rest : List (Fock.Letter depth)) :
    effect depth (next :: rest) = (effect depth rest).comp (letter depth next) := by
  rw [← word_effect_eq, ← word_effect_eq]
  rfl

end
end SourceCompiledGWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
