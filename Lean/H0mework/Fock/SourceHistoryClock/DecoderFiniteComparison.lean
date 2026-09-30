import H0mework.Fock.PrimeFieldJoint.ClockGraphDecoderField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceJointFiniteDecoder

noncomputable section

theorem retained_full_residual (bound : Nat) (target : SourceJointClockGraph.Carrier) :
    ‖residual bound target‖ ^ 2 = ‖SourceJointClockGraph.residual target‖ ^ 2 +
      ‖SourceJointClockGraph.action (SourceJointClockGraph.recover target - read bound (decode bound target))‖ ^ 2 := by
  have whole := SourceJointClockDecoder.error_decomposition target (read bound (decode bound target))
  change ‖target - action bound (decode bound target)‖ ^ 2 = _ at whole
  rw [source_minimum_cost] at whole
  exact whole

theorem finite_root_cost (bound : Nat) :
    1 < ‖residual bound (SourceJointClockGraph.read (SourceClockComplex.ofNative
      (SourceOwnedObservationHistory.sourcePoint 0)))‖ ^ 2 := by
  have strict := SourceJointClockDecoder.finite_root_cost_strict
    (SourceHistoryWord.word bound (decode bound (SourceJointClockGraph.read (SourceClockComplex.ofNative
      (SourceOwnedObservationHistory.sourcePoint 0)))))
  rw [← read_source] at strict
  change 1 < ‖SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOwnedObservationHistory.sourcePoint 0)) -
    action bound (decode bound (SourceJointClockGraph.read (SourceClockComplex.ofNative
      (SourceOwnedObservationHistory.sourcePoint 0))))‖ ^ 2 at strict
  rw [source_minimum_cost] at strict
  exact strict

theorem action_normalized {old fresh : Nat} (retained : old ≤ fresh) (value : Space old) :
    action fresh (SourceHistoryGrowth.normalizedInclusion retained value) = action old value := by
  rw [action_source, action_source, SourceHistoryWord.normalized_word]

theorem residual_monotone {old fresh : Nat} (retained : old ≤ fresh) (target : SourceJointClockGraph.Carrier) :
    ‖residual fresh target‖ ^ 2 ≤ ‖residual old target‖ ^ 2 := by
  have minimum := (isMinOn_univ_iff.mp (source_minimum fresh target))
    (SourceHistoryGrowth.normalizedInclusion retained (decode old target))
  simpa only [source_minimum_cost, action_normalized] using minimum

end
end SourceJointFiniteDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
