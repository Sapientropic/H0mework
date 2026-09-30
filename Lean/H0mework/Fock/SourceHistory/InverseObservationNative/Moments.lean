import H0mework.Fock.SourceHistory.InverseObservationNative.Realization

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationNative

open SourceGeneratedActionWords SourceCopyTimeModel
noncomputable section

def realize (bound : Nat) (program : Nat × Nat) (steps : Nat)
    (entries : Fin (bound + 1) → Option (Nat × ℚ) × ℚ) : SourceJointClockGraph.Carrier :=
  let remainder := SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
    (SourceNativeInverseDistribution.action (1, steps) (SourceInverseDistributionBirth.residual bound entries)))
  SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (SourceInverseDistributionBirth.recovered bound entries)) +
    SourceCopyGraph.axes (mass remainder)
      ((program.1 : ℂ)⁻¹ * (SourceJointClockGraph.clock remainder - (program.2 : ℂ) * mass remainder))

theorem remainder_recovery {Key : Type*} (bound depth : Nat) (word : List (Fock.Letter depth)) (steps : Nat)
    (source : SourceConditionalNativeObservers.State Key bound) (key : Key) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    let remainder := SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
      (SourceNativeInverseDistribution.action (1, steps)
        (SourceInverseDistributionBirth.residual bound (fromState bound program steps source key).2)))
    SourceGWordInverse.recover depth word remainder = SourceCopyGraph.axes (mass remainder)
      ((program.1 : ℂ)⁻¹ * (SourceJointClockGraph.clock remainder - (program.2 : ℂ) * mass remainder)) := by
  dsimp only
  let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
  let remainder := SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
    (SourceNativeInverseDistribution.action (1, steps)
      (SourceInverseDistributionBirth.residual bound (fromState bound program steps source key).2)))
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply lp.ext
      funext coordinate
      change hilbert (SourceGWordInverse.recover depth word remainder) coordinate = 0
      rw [SourceGWordInverse.hilbert_recover]
      change SourceSuccessorBoundary.readWord (SourceConditionalRationalStream.embedWord
        (SourceNativeInverseDistribution.action (1, steps)
          (SourceInverseDistributionBirth.residual bound (fromState bound program steps source key).2)))
            (SourceCopyWordAffine.execute program coordinate) = 0
      rw [SourceSuccessorBoundary.readWord_coordinate]
      change ((SourceNativeInverseDistribution.action (1, steps)
        (SourceInverseDistributionBirth.residual bound (fromState bound program steps source key).2)
          (SourceCopyWordAffine.execute program coordinate) : ℚ) : ℂ) = 0
      rw [remainder_zero bound program (SourceCompiledWordOperator.slope_positive _) steps source key coordinate]
      exact Rat.cast_zero
    · exact SourceGWordInverse.mass_recover depth word remainder
  · exact SourceGWordInverse.clock_recover depth word remainder

theorem realize_fromState {Key : Type*} (bound depth : Nat) (word : List (Fock.Letter depth)) (steps : Nat)
    (source : SourceConditionalNativeObservers.State Key bound) (key : Key) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    realize bound program steps (fromState bound program steps source key).2 =
      SourceGWordInverse.recover depth word
        (time steps (SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (SourceConditionalNativeKeys.word bound (source key).2)))) := by
  dsimp only
  rw [← g_equation bound depth word steps source key, map_add, SourceGWordInverse.recover_effect, remainder_recovery]
  rfl

end
end SourceInverseObservationNative
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
