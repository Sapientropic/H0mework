import H0mework.Physics.MotherProgrammesFormationCoordinates.ActionPresentation
import H0mework.Physics.MotherProgrammesFormationPotential.GeneratedConsumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCoordinateCompletion

open MotherFamilyOccurrence StageEightDiscreteFormation

noncomputable section

def rationalInput (visit : MotherVisit) (slot : Fin 65) : ℚ :=
  RationalSourceFormation.rationalTrace (RationalSourceFormation.sampleSource visit slot.succ)

theorem rational_input_cast (visit : MotherVisit) (slot : Fin 65) :
    (rationalInput visit slot : ℝ) =
      ContinuousSourceFormation.coordinates (RationalSourceFormation.assembledSource visit) slot := by
  refine Fin.cases ?_ ?_ slot
  · exact RationalSourceFormation.rational_trace_cast _
  · intro index
    change (rationalInput visit index.succ : ℝ) =
      RationalSourceFormation.sampleTrace visit
        (RationalSourceFormation.coframeIndex (RationalSourceFormation.coframeIndex.symm index)).succ.succ
    rw [Equiv.apply_symm_apply]
    exact RationalSourceFormation.rational_trace_cast _

/-- Each emitted coordinate is calculated from the current finite prefix
and the original keep/trace weight before completion. -/
def rationalEmission (visit : MotherVisit) : Fin 65 → ℚ :=
  fun slot => (1 / 2 : ℚ) ^ (codeOf visit + 1) *
    ((rationalInput visit slot)^2 / (1 + (rationalInput visit slot)^2))

def finiteEmit (visit : MotherVisit) : RationalCarrier 65 :=
  fromRational 65 (rationalEmission visit)

def completedEmit (visit : MotherVisit) : PointPresentation :=
  ((finiteEmit visit : Completed 65), 0)

theorem emission_coordinates (visit : MotherVisit) :
    coordinates 65 (completedEmit visit).1 =
      ContinuousSourceFormation.weight (codeOf visit) • ContinuousSourceFormation.responseAt visit := by
  rw [show (completedEmit visit).1 = (finiteEmit visit : Completed 65) from rfl, coordinates_coe]
  funext slot
  change ((rationalEmission visit slot : ℚ) : ℝ) = _
  simp only [rationalEmission, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat, Rat.cast_add, rational_input_cast, ContinuousSourceFormation.weight_eq,
    ContinuousSourceFormation.responseAt, ContinuousSourceFormation.response, Pi.smul_apply,
    smul_eq_mul]

theorem emitted_points (visit : MotherVisit) :
    points (completedEmit visit) = GeneratedPotentialHistory.emit visit := by
  change PotentialSourceFormation.restorePoints (coordinates 65 (completedEmit visit).1) 0 = _
  rw [emission_coordinates]
  rfl

def completedStep (state : CompletedState) : CompletedState :=
  completedAct state (completedEmit state.1)

theorem step_commutes (state : CompletedState) :
    statePoints (completedStep state) = GeneratedPotentialHistory.step (statePoints state) := by
  rw [completedStep, next_commutes, emitted_points]
  rfl

/-- Only the original initial state is translated; every subsequent state
is produced by the completed operation and the finite-source emitter. -/
def completedInitial : CompletedState :=
  (Runtime.visit, pointPresentationEquiv.symm GeneratedPotentialHistory.initialPoints)

def completedStateAt : ℕ → CompletedState
  | 0 => completedInitial
  | index + 1 => completedStep (completedStateAt index)

theorem generated_state_commutes (index : ℕ) :
    statePoints (completedStateAt index) = GeneratedPotentialHistory.stateAt index := by
  induction index with
  | zero => exact Prod.ext rfl (pointPresentationEquiv.apply_symm_apply _)
  | succ index induction =>
      rw [completedStateAt, step_commutes, induction]
      rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCoordinateCompletion
