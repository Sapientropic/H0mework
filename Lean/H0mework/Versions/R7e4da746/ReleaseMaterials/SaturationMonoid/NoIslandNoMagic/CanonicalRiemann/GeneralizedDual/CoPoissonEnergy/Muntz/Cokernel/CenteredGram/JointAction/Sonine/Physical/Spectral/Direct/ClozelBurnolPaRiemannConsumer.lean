import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Spectral.Direct.ClozelBurnolPaRootEffectSplice

/-!
# Terminal RH consumer of complete Burnol dynamics

The original exact-order Jordan read generates nonvanishing of the completed-
Mellin evaluator at each zero. Uniform cancellation of the actual fixed-root
boundary residual then excludes both
strict sides of the critical line.  Left-half zeros are transported through
the existing completed functional equation to their right-half reversal.

This consumer does not produce boundary cancellation or store it in a new
source, gate, or runtime.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open Complex

noncomputable section

theorem riemannHypothesis_of_burnolPa_completeDynamics
    (boundaryCancellation : ∀ (coordinate : BurnolCompletedMellinCoordinate)
      (zero : riemannZeta coordinate.value = 0),
      BurnolPaBoundaryCancellationAt coordinate zero) :
    RiemannHypothesis := by
  intro value zero nontrivial _notPole
  let observation : GeneratedRiemannZeroObservation :=
    GeneratedRiemannZeroObservation.ofMathlibZero value zero
  have strip := observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial
  have stripValue : 0 < value.re ∧ value.re < 1 := by
    simpa [observation] using strip
  rcases lt_trichotomy value.re (1 / 2) with left | center | right
  · let reversalValue := coordinateReversal value
    have reversalRight : 1 / 2 < reversalValue.re := by
      have realRead : reversalValue.re = 1 - value.re := by
        simp [reversalValue, coordinateReversal]
      rw [realRead]
      linarith
    have reversalBelow : reversalValue.re < 1 := by
      have realRead : reversalValue.re = 1 - value.re := by
        simp [reversalValue, coordinateReversal]
      rw [realRead]
      linarith [stripValue.1]
    let reversalCoordinate : BurnolCompletedMellinCoordinate :=
      ⟨reversalValue, reversalRight, reversalBelow⟩
    have reversalNe : reversalValue ≠ 0 := by
      intro equality
      have realZero := congrArg Complex.re equality
      rw [Complex.zero_re] at realZero
      linarith
    have completedZero :
        generatedCompletedRiemannZeta ActualAnalyticOwner reversalValue = 0 := by
      simpa [observation, reversalValue] using
        observation.completed_reversal_eq_zero_of_nontrivial nontrivial
    have reversalZero : riemannZeta reversalCoordinate.value = 0 := by
      rw [riemannZeta_def_of_ne_zero reversalNe]
      rw [← generatedCompletedRiemannZeta_eq_mathlib ActualAnalyticOwner]
      rw [completedZero, zero_div]
    exact False.elim
      (burnolPaBoundaryCancellation_incompatible_with_rightHalf
        reversalCoordinate reversalZero (boundaryCancellation reversalCoordinate reversalZero))
  · exact center
  · let coordinate : BurnolCompletedMellinCoordinate :=
      ⟨value, right, stripValue.2⟩
    exact False.elim
      (burnolPaBoundaryCancellation_incompatible_with_rightHalf
        coordinate zero (boundaryCancellation coordinate zero))

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
