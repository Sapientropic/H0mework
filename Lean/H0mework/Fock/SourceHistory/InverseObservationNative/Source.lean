import H0mework.Fock.SourceHistory.InverseObservationNative.Native
import H0mework.Fock.InverseDistribution.Realization
import H0mework.Fock.InverseDistribution.StreamSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationNative

noncomputable section

theorem shift_run (steps state : Nat) :
    SourceCopyNativeWord.run (List.replicate steps none) state = state + steps := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps previous =>
      rw [List.replicate_succ]
      change SourceCopyNativeWord.run (List.replicate steps none) (state + 1) = _
      rw [previous]
      omega

theorem position_source (steps : Nat) {bound : Nat} (actor : Fin (bound + 1)) :
    SourceCopyNativeWord.run (List.replicate steps none) (actor.val + 1) = position steps actor :=
  shift_run steps _

theorem shift_index (steps state : Nat) : SourceCopyWordAffine.execute (1, steps) state = state + steps := by
  simp only [SourceCopyWordAffine.execute, one_mul]
  omega

theorem fromState_source {Key : Type*} (bound : Nat) (program : Nat × Nat) (steps : Nat)
    (source : SourceConditionalNativeObservers.State Key bound) :
    SourceInverseDistributionStream.source bound (fromState bound program steps source) = source := by
  funext key
  apply Prod.ext
  · rfl
  · funext actor
    exact SourceInverseDistributionStream.weight_split program (position steps actor) _

theorem step_source {Key : Type*} (bound : Nat) (program : Nat × Nat) (steps : Nat)
    (source : SourceConditionalNativeObservers.State Key bound) :
    step bound program steps (fromState bound program steps source) = fromState bound program (steps + 1) source := by
  rw [step, fromState_source]

theorem generated_source {Key : Type*} [DecidableEq Key] (read : Nat → Key) (word : List (Option Nat)) (bound phase : Nat) :
    generate read word bound phase =
      fromState bound (SourceCopyWordAffine.compile word) ((SourceCopyWordAffine.compile word).2 + phase)
        (SourceConditionalNativeObservers.generate read bound) := by
  induction phase with
  | zero => rfl
  | succ phase previous =>
      rw [generated_next, previous, step_source]
      rfl

theorem fromState_equation {Key : Type*} (bound : Nat) (program : Nat × Nat) (positive : 0 < program.1) (steps : Nat)
    (source : SourceConditionalNativeObservers.State Key bound) (key : Key) :
    let entries := (fromState bound program steps source key).2
    SourceNativeInverseDistribution.action program (SourceInverseDistributionBirth.recovered bound entries) +
      SourceNativeInverseDistribution.action (1, steps) (SourceInverseDistributionBirth.residual bound entries) =
      SourceNativeInverseDistribution.action (1, steps) (SourceConditionalNativeKeys.word bound (source key).2) := by
  dsimp only
  simp only [SourceInverseDistributionBirth.recovered, SourceInverseDistributionBirth.residual,
    SourceConditionalNativeKeys.word, LinearMap.coe_mk, AddHom.coe_mk,
    SourceConditionalNativeKeys.source_single, Finsupp.smul_single, smul_eq_mul, mul_one, map_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro actor _
  have single (weight : ℚ) :
      SourceNativeInverseDistribution.action (1, steps) (Finsupp.single (actor.val + 1) weight) =
        Finsupp.single (position steps actor) weight := by
    simp only [SourceNativeInverseDistribution.action, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, shift_index, position]
  rw [single, single]
  exact SourceNativeInverseDistribution.entry_equation program positive _ _

theorem remainder_zero {Key : Type*} (bound : Nat) (program : Nat × Nat) (positive : 0 < program.1) (steps : Nat)
    (source : SourceConditionalNativeObservers.State Key bound) (key : Key) (state : Nat) :
    SourceNativeInverseDistribution.action (1, steps)
      (SourceInverseDistributionBirth.residual bound (fromState bound program steps source key).2)
        (SourceCopyWordAffine.execute program state) = 0 := by
  simp only [SourceInverseDistributionBirth.residual, SourceConditionalNativeKeys.word,
    LinearMap.coe_mk, AddHom.coe_mk, SourceConditionalNativeKeys.source_single,
    Finsupp.smul_single, smul_eq_mul, mul_one, map_sum, SourceNativeInverseDistribution.action,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, shift_index, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro actor _
  by_cases same : position steps actor = SourceCopyWordAffine.execute program state
  · change Finsupp.single (position steps actor)
      (SourceNativeInverseDistribution.splitEntry program (position steps actor) ((source key).2 actor)).2
        (SourceCopyWordAffine.execute program state) = 0
    rw [same]
    simp only [SourceNativeInverseDistribution.splitEntry, SourceNativeProgramInverse.decode_execute program positive,
      Finsupp.single_zero, Finsupp.zero_apply]
  · exact Finsupp.single_eq_of_ne (fun equal => same equal.symm)

end
end SourceInverseObservationNative
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
