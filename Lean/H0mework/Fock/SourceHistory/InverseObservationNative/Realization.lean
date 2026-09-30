import H0mework.Fock.SourceHistory.InverseObservationNative.Source
import H0mework.Fock.HistoryConditional.InverseObservationPacketSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationNative

open SourceGeneratedActionWords SourceCopyTimeModel
noncomputable section

theorem shift_complex_read (steps : Nat) (word : Nat →₀ ℂ) :
    SourceJointClockGraph.read (SourceGWordProgram.complexAction (1, steps) word) =
      time steps (SourceJointClockGraph.read word) := by
  induction steps with
  | zero =>
      change SourceJointClockGraph.read (Finsupp.mapDomain (SourceCopyWordAffine.execute (1, 0)) word) = SourceJointClockGraph.read word
      have identity : SourceCopyWordAffine.execute (1, 0) = id := by funext state; exact shift_index 0 state
      rw [identity, Finsupp.mapDomain_id]
  | succ steps previous =>
      rw [time_succ, ← previous, SourceJointClockGraph.action_source]
      change SourceJointClockGraph.read (Finsupp.mapDomain (SourceCopyWordAffine.execute (1, steps + 1)) word) =
        SourceJointClockGraph.read (Finsupp.mapDomain Nat.succ (Finsupp.mapDomain (SourceCopyWordAffine.execute (1, steps)) word))
      rw [← Finsupp.mapDomain_comp]
      have actual : SourceCopyWordAffine.execute (1, steps + 1) = Nat.succ ∘ SourceCopyWordAffine.execute (1, steps) := by
        funext state
        simp only [Function.comp_apply, shift_index]
        omega
      rw [actual]

theorem shift_read (steps : Nat) (word : Nat →₀ ℚ) :
    SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (SourceNativeInverseDistribution.action (1, steps) word)) =
      time steps (SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord word)) := by
  rw [SourceNativeInverseDistribution.embed_action, shift_complex_read]

theorem g_equation {Key : Type*} (bound depth : Nat) (word : List (Fock.Letter depth)) (steps : Nat)
    (source : SourceConditionalNativeObservers.State Key bound) (key : Key) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    let entries := (fromState bound program steps source key).2
    SourceCompiledGWord.effect depth word
      (SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (SourceInverseDistributionBirth.recovered bound entries))) +
      SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
        (SourceNativeInverseDistribution.action (1, steps) (SourceInverseDistributionBirth.residual bound entries))) =
      time steps (SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (SourceConditionalNativeKeys.word bound (source key).2))) := by
  dsimp only
  rw [SourceCompiledGWord.effect, SourceGWordProgram.action_source, ← SourceNativeInverseDistribution.embed_action,
    ← map_add, ← map_add, fromState_equation bound _ (SourceCompiledWordOperator.slope_positive _), shift_read]

end
end SourceInverseObservationNative
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
