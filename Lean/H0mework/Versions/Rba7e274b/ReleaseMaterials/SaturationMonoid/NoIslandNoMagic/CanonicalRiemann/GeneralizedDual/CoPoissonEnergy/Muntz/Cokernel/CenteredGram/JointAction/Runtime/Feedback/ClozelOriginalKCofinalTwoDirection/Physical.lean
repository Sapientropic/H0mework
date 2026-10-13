import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalTwoDirection.Readback
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Exterior.Resolvent.Translation

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalTwoDirection
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open scoped InnerProductSpace Topology

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

def originalK : BurnolL2 :=
  (burnolCompletedMellinRieszVector (coordinate observation nontrivial half) : BurnolL2)

def originalFourierK : BurnolL2 := fourierL2 (originalK observation nontrivial half)

def completeCurrent (ordinal : Nat) (test : BurnolL2) (shift : ℝ) : ℂ :=
  inner ℂ test (translatedCorrection observation nontrivial half shift (D.raw observation nontrivial half depth ordinal)) +
  inner ℂ test (translatedUnit observation nontrivial half shift (D.raw observation nontrivial half depth ordinal)) +
  inner ℂ test (translatedShell observation nontrivial half shift (D.raw observation nontrivial half depth ordinal)) +
  inner ℂ test (translatedInvisible observation nontrivial half shift (D.raw observation nontrivial half depth ordinal))

theorem complete_current_eq_original (ordinal : Nat) (test : BurnolL2) (shift : ℝ) :
    completeCurrent observation nontrivial half depth ordinal test shift =
      inner ℂ test (burnolMultiplicativeDilation shift
        (D.raw observation nontrivial half depth (ordinal + 1))) := by
  have source := congrArg (inner ℂ test)
    (four_terms_eq_action observation nontrivial half shift (D.raw observation nontrivial half depth ordinal))
  have terms : completeCurrent observation nontrivial half depth ordinal test shift =
      inner ℂ test (fourTerms observation nontrivial half shift (D.raw observation nontrivial half depth ordinal)) := by
    change _ = inner ℂ test (_ + _ + _ + _)
    simp only [inner_add_right]
    rfl
  exact (terms.trans source).trans (congrArg (fun value : BurnolL2 =>
    inner ℂ test (burnolMultiplicativeDilation shift value))
      (D.raw_successor observation nontrivial half depth ordinal).symm)

theorem actual_original_K_current (ordinal : Nat) :
    inner ℂ (originalK observation nontrivial half)
      (directions (CF.collapseValue (actionPacket observation nontrivial half depth ordinal).1
        (receipt observation nontrivial half depth ordinal).2.2.1)).1 =
      completeCurrent observation nontrivial half depth (ordinal + 1) (originalK observation nontrivial half) sourceShift :=
  (congrArg (fun value : BurnolL2 × BurnolL2 => inner ℂ (originalK observation nontrivial half) value.1)
    (actual_R_two_direction observation nontrivial half depth ordinal)).trans
      (complete_current_eq_original observation nontrivial half depth (ordinal + 1)
        (originalK observation nontrivial half) sourceShift).symm

theorem actual_original_Fourier_K_current (ordinal : Nat) :
    inner ℂ (originalFourierK observation nontrivial half)
      (directions (CF.collapseValue (actionPacket observation nontrivial half depth ordinal).1
        (receipt observation nontrivial half depth ordinal).2.2.1)).2 =
      completeCurrent observation nontrivial half depth (ordinal + 1) (originalFourierK observation nontrivial half) (-sourceShift) :=
  (congrArg (fun value : BurnolL2 × BurnolL2 => inner ℂ (originalFourierK observation nontrivial half) value.2)
    (actual_R_two_direction observation nontrivial half depth ordinal)).trans
      (complete_current_eq_original observation nontrivial half depth (ordinal + 1)
        (originalFourierK observation nontrivial half) (-sourceShift)).symm

theorem complete_current_laplace (ordinal : Nat) (test : BurnolL2) (shift : ℝ) :
    (∫ t : ℝ in Ioi 0, positiveMellinQuarterRightResolventWeight (observation.coordinate / 2) t *
      inner ℂ test (burnolMultiplicativeDilation (shift - t / 2)
        (D.raw observation nontrivial half depth ordinal))) +
      completeCurrent observation nontrivial half depth ordinal test shift = 0 := by
  rw [complete_current_eq_original, D.raw_successor, Paid.original_R_direct observation nontrivial half]
  have actual := OriginalPaPhysicalGreen.translated_resolvent_pairing
    (coordinate observation nontrivial half) (D.raw observation nontrivial half depth ordinal) test shift
  rw [coordinate_value] at actual
  rw [actual]
  ring

theorem actual_source_p_PaOrth_r (ordinal : Nat) :
    (Pa.actualPa observation nontrivial half depth (ordinal + 1) : BurnolL2) +
      (Pa.Q (D.raw observation nontrivial half depth (ordinal + 1)) : BurnolL2) +
      (D.input observation nontrivial half depth (ordinal + 1)).2 =
      D.raw observation nontrivial half depth (ordinal + 1) :=
  Pa.actual_complete_reconstruction observation nontrivial half depth ordinal

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalTwoDirection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
