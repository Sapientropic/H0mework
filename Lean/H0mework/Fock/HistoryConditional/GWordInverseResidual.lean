import H0mework.Fock.HistoryConditional.GWordInverseMoments
import H0mework.Fock.CopyGraph.TimeGramEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGWordInverse

open SourceGeneratedActionWords SourceCopyTimeModel
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem effect_axes (depth : Nat) (word : List (Fock.Letter depth)) (massValue clockValue : ℂ) :
    SourceCompiledGWord.effect depth word (SourceCopyGraph.axes massValue clockValue) =
      SourceCopyGraph.axes massValue
        (((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ) * clockValue +
          ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℂ) * massValue) := by
  induction word generalizing massValue clockValue with
  | nil =>
      rw [SourceCompiledGWord.effect_nil]
      simp only [List.map_nil, SourceCopyWordAffine.compile, List.foldr_nil, Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, add_zero]
      rfl
  | cons next rest previous =>
      rw [SourceCompiledGWord.effect_cons]
      change SourceCompiledGWord.effect depth rest (SourceCompiledGWord.letter depth next (SourceCopyGraph.axes massValue clockValue)) = _
      cases next with
      | inl marker =>
          change SourceCompiledGWord.effect depth rest (SourceJointClockGraph.action (SourceCopyGraph.axes massValue clockValue)) = _
          rw [SourceCopyTimeGram.axes_next, previous]
          apply congrArg (SourceCopyGraph.axes massValue)
          simp only [List.map_cons, SourceCopyNativeWord.encode, SourceCopyWordAffine.compile, List.foldr_cons, Nat.cast_add]
          ring
      | inr index =>
          have primitive : SourceCopyGraph.action depth index (SourceCopyGraph.axes massValue clockValue) =
              SourceCopyGraph.axes massValue ((SourceCopyProgram.scale depth index : ℂ) * clockValue) := by
            rw [SourceCopyGraph.action_apply, SourceCopyGraph.joint_apply]
            change WithLp.toLp 2 (WithLp.toLp 2 (SourceCopyGraph.hilbertAction depth index 0, massValue),
              (SourceCopyProgram.scale depth index : ℂ) * clockValue) = _
            rw [map_zero]
            rfl
          change SourceCompiledGWord.effect depth rest (SourceCopyGraph.action depth index (SourceCopyGraph.axes massValue clockValue)) = _
          rw [primitive, previous]
          apply congrArg (SourceCopyGraph.axes massValue)
          rw [SourceCopyProgram.scale_source]
          simp only [List.map_cons, SourceCopyNativeWord.encode, SourceCopyWordAffine.compile, List.foldr_cons,
            Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          ring

theorem correction_effect (depth : Nat) (word : List (Fock.Letter depth)) (source : SourceOperationNative.Carrier process) :
    SourceCompiledGWord.effect depth word (correction depth word source) =
      SourceCopyGraph.axes
        (mass (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.residual depth word source))))
        (SourceJointClockGraph.clock (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.residual depth word source)))) := by
  rw [correction, effect_axes]
  have nonzero : ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (SourceCompiledWordOperator.slope_positive _).ne'
  rw [mul_inv_cancel_left₀ nonzero, sub_add_cancel]

theorem residual_native_moments (depth : Nat) (word : List (Fock.Letter depth)) (source : SourceOperationNative.Carrier process) :
    residual depth word (SourceJointClockGraph.read (SourceClockComplex.ofNative source)) +
      SourceCopyGraph.axes
        (mass (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.residual depth word source))))
        (SourceJointClockGraph.clock (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.residual depth word source)))) =
      SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.residual depth word source)) := by
  have completed := reconstruction depth word (SourceJointClockGraph.read (SourceClockComplex.ofNative source))
  rw [recovery_native_moments, map_add, SourceCompiledGWord.source_effect, correction_effect] at completed
  have original := congrArg (fun value => SourceJointClockGraph.read (SourceClockComplex.ofNative value))
    (SourceCompiledWordOperator.reconstruct depth word source)
  rw [map_add, map_add] at original
  apply add_left_cancel (a := SourceJointClockGraph.read
    (SourceClockComplex.ofNative (SourceCompiledWordOperator.action depth word (SourceCompiledWordOperator.recover depth word source))))
  calc
    _ = SourceJointClockGraph.read (SourceClockComplex.ofNative source) := by
      convert completed using 1
      abel
    _ = _ := original.symm

end
end SourceGWordInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
