import H0mework.Versions.R2.Physics.MotherProgrammesFormationProgrammes.AutonomousHistory

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.AutonomousProgrammes

open StageNineEnrichedProofFreeSource MotherFamilyOccurrence MotherCoordinateCompletion
open MotherProgrammes MotherProgrammeExecution StageEightDiscreteFormation

noncomputable section

def datumCarrier (data : MotherProgrammes.Datum) : WholePointFormation.Carrier :=
  (fromRational (65 * 4) data.2 : WholePointFormation.Carrier)

/-- This is the source-and-space readout of complete programme data.
The autonomous recurrence never reads this target-facing function. -/
def datumSource (data : MotherProgrammes.Datum) : SmoothUnifiedSource :=
  let discrete := toSource data.1
  let operands := WholePointFormation.points (datumCarrier data)
  { discrete with
    stageEight := { discrete.stageEight with
      coframeLinearCoefficient := PotentialSourceFormation.coframeMaterials operands }
    continuousContactResidual := PotentialSourceFormation.materials operands 0 }

def datumReadout (data : MotherProgrammes.Datum) : RawSourcePaths.Datum :=
  (datumSource data, PotentialSourceFormation.remainders (WholePointFormation.points (datumCarrier data)))

theorem entry_carrier_data (entry : Entry) : entry.carrier = datumCarrier entry.data := by
  change (fromVisit (65 * 4) entry.coordinateVisit : Completed (65 * 4)) =
    (fromRational (65 * 4) entry.data.2 : Completed (65 * 4))
  apply congrArg (fun value : RationalCarrier (65 * 4) => (value : Completed (65 * 4)))
  exact Subtype.ext rfl

theorem entry_readout_data (entry : Entry) : entryReadout entry = datumReadout entry.data := by
  have discrete : toSource entry.data.1 = sourceAtVisit entry.discreteVisit := by
    change toSource (readMaterial (toSource (materialAt (codeOf entry.discreteVisit)))) =
      toSource (materialAt (codeOf entry.discreteVisit))
    rw [full_material_recovered]
  simp only [entryReadout, Entry.source, WholePointFormation.source, datumReadout, datumSource,
    PotentialSourceFormation.sourceOf, discrete, entry_carrier_data]

/-- Every finite rational material programme is executed in a finite
prefix of this one generated history. The target only selects the witness round. -/
theorem every_programme_in_history (targets : List MotherProgrammes.Datum) :
    ∃ round,
      (roundProgramme round).map Entry.data = targets ∧
      List.Sublist (targets.map datumReadout)
        (RawSourcePaths.pathReadout WholePointFormation.initial (globalEvents (round + 1))) := by
  obtain ⟨round, generated⟩ := MotherProgrammes.every_programme targets
  have data := (round_programme_data round).trans generated
  have reads : (roundProgramme round).map entryReadout = targets.map datumReadout := by
    calc
      _ = ((roundProgramme round).map Entry.data).map datumReadout := by
        rw [List.map_map]
        exact congrArg (fun read : Entry → RawSourcePaths.Datum => (roundProgramme round).map read)
          (funext entry_readout_data)
      _ = _ := by rw [data]
  exact ⟨round, data, reads ▸ round_order round⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.AutonomousProgrammes
