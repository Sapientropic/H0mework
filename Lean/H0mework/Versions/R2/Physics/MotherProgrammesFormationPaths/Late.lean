import H0mework.Versions.R2.Physics.MotherProgrammesFormationPaths.Steps
import H0mework.Versions.R2.Physics.MotherProgrammesFormationDiscrete.Recurrence

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.RawSourcePaths

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open Stage9C.Revision WholePointFormation WholePointHistories MotherFamilyOccurrence
open StageEightDiscreteFormation

noncomputable section

abbrev Datum := SmoothUnifiedSource × PotentialSourceFormation.SpatialRemainders

def readout (state : State) : Datum :=
  (source state.1 state.2, PotentialSourceFormation.remainders (points state.2))

def pathReadout (before : State) (events : List Carrier) : List Datum :=
  (steps before events).map readout

/-- Discrete recurrence fixes a later original visit; the complete
potential coordinates then restore the source and every spatial entry there. -/
theorem arbitrary_late_state (start : ℕ) (target : Datum) :
    ∃ finish : ℕ, ∃ value : Carrier, start < finish ∧
      readout (SpinPair.visit (10 + finish), value) = target := by
  obtain ⟨finish, late, hit⟩ :=
    GeneratedDiscreteRecurrence.arbitrary_late_material (readMaterial target.1) (start + 1)
  have material : materialAt (codeOf (SpinPair.visit (10 + finish))) = readMaterial target.1 := by
    simpa only [sourceAtVisit, full_material_recovered] using hit
  have discrete : sourceAtVisit (SpinPair.visit (10 + finish)) = retainReferenceContinuous target.1 := by
    rw [sourceAtVisit, material, source_reassembled]
  let operands := PotentialSourceFormation.restorePoints (ContinuousSourceFormation.coordinates target.1) target.2
  let value := pointEquiv.symm operands
  have pointsRead : points value = operands := pointEquiv.apply_symm_apply operands
  have valuesRead : PotentialSourceFormation.materials operands =
      ContinuousSourceFormation.coordinates target.1 := PotentialSourceFormation.materials_restored _ _
  have coframeRead : PotentialSourceFormation.coframeMaterials operands =
      target.1.stageEight.coframeLinearCoefficient := by
    funext direction row column
    unfold PotentialSourceFormation.coframeMaterials
    rw [valuesRead]
    simp only [ContinuousSourceFormation.coordinates, Fin.cons_succ, Equiv.symm_apply_apply]
  have contactRead : PotentialSourceFormation.materials operands 0 = target.1.continuousContactResidual := by
    rw [valuesRead]
    rfl
  have formed : source (SpinPair.visit (10 + finish)) value = target.1 := by
    unfold source
    rw [pointsRead]
    unfold PotentialSourceFormation.sourceOf
    rw [discrete]
    change { target.1 with
      stageEight := { target.1.stageEight with coframeLinearCoefficient := PotentialSourceFormation.coframeMaterials operands }
      continuousContactResidual := PotentialSourceFormation.materials operands 0 } = target.1
    rw [coframeRead, contactRead]
  refine ⟨finish, value, by omega, Prod.ext formed ?_⟩
  exact (congrArg PotentialSourceFormation.remainders pointsRead).trans
    (PotentialSourceFormation.remainders_restored _ _)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.RawSourcePaths
