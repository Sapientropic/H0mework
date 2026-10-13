import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceReturn.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceReturn
open Complex
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)

def returnedOriginalK : BurnolL2 :=
  returnedField observation nontrivial half - S.contactCorrection (Prior.coordinate observation nontrivial half)

theorem source_return_original_K :
    returnedOriginalK observation nontrivial half = Prior.originalK observation nontrivial half := by
  rw [returnedOriginalK, source_return_corrected_field]
  change (Prior.originalK observation nontrivial half + _) - _ = _
  exact add_sub_cancel_right _ _

-- A material change is acted on by the same original R; it is not discarded at the reader.
def updatedOriginalK (increment : BurnolL2) : BurnolL2 :=
  P.R observation nontrivial half (sourceInput observation nontrivial half + increment) -
    S.contactCorrection (Prior.coordinate observation nontrivial half)

theorem source_return_actual_increment (increment : BurnolL2) :
    updatedOriginalK observation nontrivial half increment =
      Prior.originalK observation nontrivial half + P.R observation nontrivial half increment := by
  rw [updatedOriginalK, map_add]
  have initial := source_return_original_K observation nontrivial half
  change P.R observation nontrivial half (sourceInput observation nontrivial half) -
    S.contactCorrection (Prior.coordinate observation nontrivial half) = _ at initial
  rw [show P.R observation nontrivial half (sourceInput observation nontrivial half) +
      P.R observation nontrivial half increment - S.contactCorrection (Prior.coordinate observation nontrivial half) =
      (P.R observation nontrivial half (sourceInput observation nontrivial half) -
        S.contactCorrection (Prior.coordinate observation nontrivial half)) +
      P.R observation nontrivial half increment by abel, initial]

theorem source_return_original_K_price (increment : BurnolL2) :
    inner ℂ (Prior.originalK observation nontrivial half)
      (updatedOriginalK observation nontrivial half increment) =
    inner ℂ (Prior.originalK observation nontrivial half) (Prior.originalK observation nontrivial half) +
      inner ℂ (Prior.originalK observation nontrivial half) (P.R observation nontrivial half increment) := by
  rw [source_return_actual_increment, inner_add_right]

theorem source_return_original_FourierK_price (increment : BurnolL2) :
    inner ℂ (Prior.originalFourierK observation nontrivial half)
      (fourierL2 (updatedOriginalK observation nontrivial half increment)) =
    inner ℂ (Prior.originalFourierK observation nontrivial half) (Prior.originalFourierK observation nontrivial half) +
      inner ℂ (Prior.originalFourierK observation nontrivial half)
        (fourierL2 (P.R observation nontrivial half increment)) := by
  rw [source_return_actual_increment, map_add, inner_add_right]
  rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceReturn
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
