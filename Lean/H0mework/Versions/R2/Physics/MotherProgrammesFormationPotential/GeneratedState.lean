import H0mework.Versions.R2.Physics.MotherProgrammesFormationPotential.History
import H0mework.Versions.R2.Physics.MotherProgrammesFormationContinuous.Finite

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.GeneratedPotentialHistory

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open Stage9C.Revision MotherFamilyOccurrence StageEightDiscreteFormation
open PotentialSourceFormation

noncomputable section

abbrev State := MotherVisit × Points

def initialPoints : Points := restorePoints (ContinuousSourceFormation.coordinates Runtime.source) 0
def initialState : State := (Runtime.visit, initialPoints)

/-- Only the current mother's complete prefix supplies this displacement.
The original keep/trace weight and response rule fix all 65 coordinates. -/
def emit (visit : MotherVisit) : Points :=
  restorePoints (ContinuousSourceFormation.weight (codeOf visit) • ContinuousSourceFormation.responseAt visit) 0

def act (state : State) (displacement : Points) : State := nextOperands state.1 state.2 displacement
def step (state : State) : State := act state (emit state.1)

def stateAt : ℕ → State
  | 0 => initialState
  | index + 1 => step (stateAt index)

theorem state_succ (index : ℕ) : stateAt (index + 1) = step (stateAt index) := rfl

theorem points_succ (index : ℕ) :
    (stateAt (index + 1)).2 = (stateAt index).2 + emit (stateAt index).1 := rfl

theorem visit_projection (index : ℕ) : (stateAt index).1 = SpinPair.visit (10 + index) := by
  induction index with
  | zero => rfl
  | succ index induction =>
      change targetVisit (stateAt index).1 = _
      rw [induction, target_native]
      rfl

theorem code_projection (index : ℕ) : codeOf (stateAt index).1 = index := by
  rw [visit_projection, code_at]

theorem after_origin (index : ℕ) : originDepth ≤ temporalDepth (stateAt index).1.history := by
  rw [visit_projection, origin_depth, visit_depth]
  omega

theorem emit_materials (visit : MotherVisit) :
    materials (emit visit) =
      ContinuousSourceFormation.weight (codeOf visit) • ContinuousSourceFormation.responseAt visit :=
  materials_restored _ _

theorem emit_spatial (visit : MotherVisit) : remainders (emit visit) = 0 := rfl

theorem initial_materials : materials initialPoints = ContinuousSourceFormation.coordinates Runtime.source :=
  materials_restored _ _

theorem initial_coframe : coframeMaterials initialPoints = Runtime.source.stageEight.coframeLinearCoefficient := by
  funext direction row column
  unfold coframeMaterials
  rw [initial_materials]
  simp only [ContinuousSourceFormation.coordinates, Fin.cons_succ, Equiv.symm_apply_apply]

theorem materials_finite (index : ℕ) :
    materials (stateAt index).2 = ContinuousSourceFormation.coordinates Runtime.source +
      ContinuousSourceFormation.finite index := by
  induction index with
  | zero =>
      rw [ContinuousSourceFormation.finite_zero, add_zero]
      exact initial_materials
  | succ index induction =>
      rw [points_succ, materials_increment, induction, emit_materials,
        visit_projection, code_at, ContinuousSourceFormation.finite_next]
      change _ + _ + ContinuousSourceFormation.contribution index =
        _ + (_ + ContinuousSourceFormation.contribution index)
      exact add_assoc _ _ _

def formedSource (index : ℕ) : SmoothUnifiedSource := sourceOf (stateAt index).1 (stateAt index).2

theorem initial_source : formedSource 0 = StageEightDiscreteFormation.sourceAtVisit Runtime.visit := by
  change sourceOf Runtime.visit initialPoints = _
  unfold sourceOf
  rw [initial_coframe, initial_materials]
  rfl

theorem source_next (index : ℕ) : formedSource (index + 1) =
    sourceStep (stateAt index).1 (stateAt index).2 (emit (stateAt index).1) :=
  source_next_commutes _ (after_origin index) _ _

theorem formed_discrete (index : ℕ) :
    readMaterial (formedSource index) = execute (programAt index) neutralOrigin := by
  rw [formedSource, discrete_retained, complete_discrete_read, code_projection]

theorem formed_coordinates (index : ℕ) :
    ContinuousSourceFormation.coordinates (formedSource index) =
      ContinuousSourceFormation.coordinates Runtime.source + ContinuousSourceFormation.finite index := by
  rw [← materials_finite]
  funext slot
  refine Fin.cases rfl (fun coordinate => ?_) slot
  simp [formedSource, sourceOf, ContinuousSourceFormation.coordinates, coframeMaterials]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.GeneratedPotentialHistory
