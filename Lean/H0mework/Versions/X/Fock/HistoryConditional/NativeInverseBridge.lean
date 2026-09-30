import H0mework.Versions.X.Fock.HistoryConditional.NativeInverseConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeProgramInverse

open SourceGeneratedActionWords
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem raw_recovery (depth : Nat) (word : List (Fock.Letter depth)) (target : Nat) :
    SourceCompiledWordOperator.recover depth word (Finsupp.single target 1) =
      match decode (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) target with
      | none => 0
      | some state => Finsupp.single state 1 := by
  cases computed : decode (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) target with
  | none =>
      apply Finsupp.ext
      intro coordinate
      rw [SourceCompiledWordOperator.recovery_reads]
      have outside := (decode_none_iff _ (SourceCompiledWordOperator.slope_positive _) target).mp computed
      have separate : target ≠ SourceCopyWordAffine.execute
          (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) coordinate :=
        fun same => outside ⟨coordinate, same.symm⟩
      simp only [Finsupp.single_apply, if_neg separate, Finsupp.zero_apply]
  | some state =>
      apply Finsupp.ext
      intro coordinate
      rw [SourceCompiledWordOperator.recovery_reads]
      have generated := (decode_some_iff _ (SourceCompiledWordOperator.slope_positive _) target state).mp computed
      rw [← generated]
      simp only [Finsupp.single_apply, (SourceCompiledWordOperator.index_injective _).eq_iff]

theorem raw_outside (depth : Nat) (word : List (Fock.Letter depth)) (target : Nat)
    (outside : decode (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) target = none) :
    SourceCompiledWordOperator.residual depth word (Finsupp.single target 1) = Finsupp.single target 1 := by
  change Finsupp.single target 1 - SourceCompiledWordOperator.action depth word
    (SourceCompiledWordOperator.recover depth word (Finsupp.single target 1)) = _
  rw [raw_recovery, outside, map_zero, sub_zero]

theorem raw_residual (depth : Nat) (word : List (Fock.Letter depth)) (target : Nat) :
    SourceCompiledWordOperator.residual depth word (Finsupp.single target 1) =
      match decode (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) target with
      | none => Finsupp.single target 1
      | some _ => 0 := by
  cases computed : decode (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) target with
  | none => exact raw_outside depth word target computed
  | some state =>
      change Finsupp.single target 1 - SourceCompiledWordOperator.action depth word
        (SourceCompiledWordOperator.recover depth word (Finsupp.single target 1)) = 0
      rw [raw_recovery, computed]
      have generated := (decode_some_iff _ (SourceCompiledWordOperator.slope_positive _) target state).mp computed
      change Finsupp.single target 1 - Finsupp.mapDomain _ (Finsupp.single state 1) = 0
      rw [Finsupp.mapDomain_single, generated, sub_self]

end
end SourceNativeProgramInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
