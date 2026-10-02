import H0mework.Versions.R2.Physics.MotherProgrammesFormationCoordinates.WholeConsumer
import H0mework.Versions.R2.Physics.MotherProgrammesFormationCoordinates.ActionConsumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholePointFormation

open MotherCoordinateCompletion MotherFamilyOccurrence PotentialSourceFormation
open StageEightDiscreteFormation

noncomputable section

theorem readPoints_injective : Function.Injective readPoints := by
  intro first last same
  have recovered := congrArg (fun data => points ((realEquiv (65 * 4)).symm data)) same
  simpa only [points_read] using recovered

theorem readPoints_add (first last : Points) :
    readPoints (first + last) = readPoints first + readPoints last := by
  funext address
  obtain ⟨⟨slot, axis⟩, rfl⟩ := index.surjective address
  simp only [readPoints, Equiv.symm_apply_apply, materials_increment, remainders_increment, Pi.add_apply]
  exact Fin.cases rfl (fun _ => rfl) axis

theorem points_add (first last : Carrier) :
    points (completedAdd (65 * 4) first last) = points first + points last := by
  apply readPoints_injective
  rw [read_points, coordinates_add, readPoints_add, read_points, read_points]

def eventEquiv (before : Carrier) : Carrier ≃ Carrier where
  toFun := completedAdd (65 * 4) before
  invFun after := completedSub (65 * 4) after before
  left_inv event := (completed_event_recovered (65 * 4) before event).2
  right_inv after := (completed_event_recovered (65 * 4) before after).1

abbrev State := MotherVisit × Carrier

def statePoints (state : State) : GeneratedPotentialHistory.State :=
  (state.1, points state.2)

def act (state : State) (event : Carrier) : State :=
  (targetVisit state.1, completedAdd (65 * 4) state.2 event)

theorem next_commutes (state : State) (event : Carrier) :
    statePoints (act state event) =
      PotentialSourceFormation.nextOperands state.1 (points state.2) (points event) :=
  Prod.ext rfl (points_add state.2 event)

theorem full_event_fibre (before after : State) :
    (∃! event : Carrier, act before event = after) ↔ after.1 = targetVisit before.1 := by
  constructor
  · rintro ⟨event, generated, _⟩
    exact (congrArg Prod.fst generated).symm
  · intro native
    refine ⟨completedSub (65 * 4) after.2 before.2,
      Prod.ext native.symm (completed_event_recovered (65 * 4) before.2 after.2).1, ?_⟩
    intro event generated
    apply (eventEquiv before.2).injective
    exact (congrArg Prod.snd generated).trans
      (completed_event_recovered (65 * 4) before.2 after.2).1.symm

/-- One finite mother response fills all coordinates of the event before
completion; the spatial response of this particular emitter is zero. -/
def finiteEmission (visit : MotherVisit) : RationalCarrier (65 * 4) :=
  fromRational (65 * 4) (fun address =>
    let pair := index.symm address
    Fin.cases (rationalEmission visit pair.1) (fun _ => 0) pair.2)

def emit (visit : MotherVisit) : Carrier := (finiteEmission visit : Carrier)

theorem emit_material (visit : MotherVisit) (slot : Fin 65) :
    coordinate (emit visit) slot 0 =
      coordinates 65 (MotherCoordinateCompletion.completedEmit visit).1 slot := by
  change coordinates (65 * 4) (finiteEmission visit : Carrier) (index (slot, 0)) =
    coordinates 65 (finiteEmit visit : Completed 65) slot
  rw [coordinates_coe, coordinates_coe]
  simp only [realEmbedding, finiteEmission, finiteEmit, fromRational,
    Equiv.symm_apply_apply, Fin.cases_zero]

theorem emitted_points (visit : MotherVisit) :
    points (emit visit) = GeneratedPotentialHistory.emit visit := by
  rw [← MotherCoordinateCompletion.emitted_points visit]
  unfold points MotherCoordinateCompletion.points
  apply congrArg₂ restorePoints
  · funext slot
    exact emit_material visit slot
  · funext slot axis
    change coordinates (65 * 4) (finiteEmission visit : Carrier) (index (slot, axis.succ)) = 0
    rw [coordinates_coe]
    simp only [realEmbedding, finiteEmission, fromRational,
      Equiv.symm_apply_apply, Fin.cases_succ, Rat.cast_zero]

def step (state : State) : State := act state (emit state.1)

theorem step_commutes (state : State) :
    statePoints (step state) = GeneratedPotentialHistory.step (statePoints state) := by
  rw [step, next_commutes, emitted_points]
  rfl

def initial : State :=
  (Runtime.visit, pointEquiv.symm GeneratedPotentialHistory.initialPoints)

def stateAt : ℕ → State
  | 0 => initial
  | count + 1 => step (stateAt count)

theorem generated_state_commutes (count : ℕ) :
    statePoints (stateAt count) = GeneratedPotentialHistory.stateAt count := by
  induction count with
  | zero => exact Prod.ext rfl (pointEquiv.apply_symm_apply _)
  | succ count induction =>
      rw [stateAt, step_commutes, induction]
      rfl

def emittedHistory : ℕ → List Carrier
  | 0 => []
  | count + 1 => emittedHistory count ++ [emit (stateAt count).1]

theorem generated_history_commutes (count : ℕ) :
    (emittedHistory count).map points = GeneratedPotentialHistory.emittedHistory count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [emittedHistory, List.map_append, List.map_cons, List.map_nil, induction,
        emitted_points, GeneratedPotentialHistory.history_succ]
      rw [show (stateAt count).1 = (GeneratedPotentialHistory.stateAt count).1 from
        congrArg Prod.fst (generated_state_commutes count)]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholePointFormation
