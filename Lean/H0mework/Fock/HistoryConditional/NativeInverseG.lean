import H0mework.Fock.HistoryConditional.NativeInverseBridge
import H0mework.Fock.HistoryConditional.GWordInverseResidual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeProgramInverse

open SourceGeneratedActionWords
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem g_recovery (depth : Nat) (word : List (Fock.Letter depth)) (target : Nat) :
    SourceGWordInverse.recover depth word (SourceJointClockGraph.read (SourceClockComplex.ofNative (Finsupp.single target 1))) =
      (match decode (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) target with
      | none => 0
      | some state => SourceJointClockGraph.read (SourceClockComplex.ofNative (Finsupp.single state 1))) +
        SourceGWordInverse.correction depth word (Finsupp.single target 1) := by
  rw [SourceGWordInverse.recovery_native_moments, raw_recovery]
  cases decode (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) target <;> simp only [map_zero]

theorem g_residual (depth : Nat) (word : List (Fock.Letter depth)) (target : Nat) :
    SourceGWordInverse.residual depth word (SourceJointClockGraph.read (SourceClockComplex.ofNative (Finsupp.single target 1))) +
      SourceCompiledGWord.effect depth word (SourceGWordInverse.correction depth word (Finsupp.single target 1)) =
      match decode (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) target with
      | none => SourceJointClockGraph.read (SourceClockComplex.ofNative (Finsupp.single target 1))
      | some _ => 0 := by
  calc
    _ = SourceJointClockGraph.read (SourceClockComplex.ofNative
        (SourceCompiledWordOperator.residual depth word (Finsupp.single target 1))) := by
      rw [SourceGWordInverse.correction_effect]
      exact SourceGWordInverse.residual_native_moments depth word _
    _ = _ := by
      rw [raw_residual]
      cases decode (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) target <;> simp only [map_zero]

end
end SourceNativeProgramInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
