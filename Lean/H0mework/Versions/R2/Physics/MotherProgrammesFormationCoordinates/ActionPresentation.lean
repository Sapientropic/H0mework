import H0mework.Versions.R2.Physics.MotherProgrammesFormationCoordinates.ActionOperations
import H0mework.Versions.R2.Physics.MotherProgrammesFormationCoordinates.Consumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCoordinateCompletion

open MotherFamilyOccurrence

noncomputable section

def presentationAdd (first last : PointPresentation) : PointPresentation :=
  (completedAdd 65 first.1 last.1, first.2 + last.2)

def presentationSub (last first : PointPresentation) : PointPresentation :=
  (completedSub 65 last.1 first.1, last.2 - first.2)

theorem presentation_event_recovered (first last : PointPresentation) :
    presentationAdd first (presentationSub last first) = last ∧
      presentationSub (presentationAdd first last) first = last := by
  constructor
  · apply Prod.ext
    · exact (completed_event_recovered 65 first.1 last.1).1
    · change first.2 + (last.2 - first.2) = last.2
      abel
  · apply Prod.ext
    · exact (completed_event_recovered 65 first.1 last.1).2
    · change first.2 + last.2 - first.2 = last.2
      abel

def eventEquiv (before : PointPresentation) : PointPresentation ≃ PointPresentation where
  toFun := presentationAdd before
  invFun after := presentationSub after before
  left_inv event := (presentation_event_recovered before event).2
  right_inv after := (presentation_event_recovered before after).1

theorem points_add (first last : PointPresentation) :
    points (presentationAdd first last) = points first + points last := by
  rw [← PotentialSourceFormation.points_recovered (points first + points last),
    PotentialSourceFormation.materials_increment, PotentialSourceFormation.remainders_increment,
    points_materials, points_materials, points_spatial, points_spatial]
  unfold points presentationAdd
  congr 1
  exact coordinates_add 65 first.1 last.1

theorem points_sub (last first : PointPresentation) :
    points (presentationSub last first) = points last - points first := by
  have recovered := congrArg points (presentation_event_recovered first last).1
  rw [points_add] at recovered
  calc
    points (presentationSub last first) =
        (points first + points (presentationSub last first)) - points first := by abel
    _ = points last - points first := congrArg (fun value => value - points first) recovered

abbrev CompletedState := MotherVisit × PointPresentation

def statePoints (state : CompletedState) : MotherVisit × PotentialSourceFormation.Points :=
  (state.1, points state.2)

def completedAct (state : CompletedState) (event : PointPresentation) : CompletedState :=
  (targetVisit state.1, presentationAdd state.2 event)

theorem next_commutes (state : CompletedState) (event : PointPresentation) :
    statePoints (completedAct state event) =
      PotentialSourceFormation.nextOperands state.1 (points state.2) (points event) :=
  Prod.ext rfl (points_add state.2 event)

theorem full_event_fibre (before after : CompletedState) :
    (∃! event : PointPresentation, completedAct before event = after) ↔
      after.1 = targetVisit before.1 := by
  constructor
  · rintro ⟨event, generated, _⟩
    exact (congrArg Prod.fst generated).symm
  · intro native
    refine ⟨presentationSub after.2 before.2,
      Prod.ext native.symm (presentation_event_recovered before.2 after.2).1, ?_⟩
    intro event generated
    apply (eventEquiv before.2).injective
    exact (congrArg Prod.snd generated).trans (presentation_event_recovered before.2 after.2).1.symm

theorem potential_action_commutes (first event : PointPresentation) (slot : Fin 65) :
    StageNineEnrichedProofFreeSource.generatedMotherPotential Runtime.source
        (points (presentationAdd first event) slot) 1 =
      StageNineEnrichedProofFreeSource.generatedMotherPotential Runtime.source (points first slot) 1 +
        StageNineEnrichedProofFreeSource.generatedMotherPotential Runtime.source (points event slot) 1 := by
  rw [points_add]
  exact PotentialSourceFormation.potential_increment (points first slot) (points event slot)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCoordinateCompletion
