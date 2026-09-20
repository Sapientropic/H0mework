import H0mework.Physics.MotherProgrammesFormationPotential.Potential
import H0mework.Physics.MotherProgrammesFormationRational.Assembly

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.PotentialSourceFormation

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open MotherFamilyOccurrence StageEightDiscreteFormation

noncomputable section

abbrev Points := Fin 65 → BasePoint
abbrev SpatialRemainders := Fin 65 → Fin 3 → ℝ

def materials (points : Points) : Fin 65 → ℝ := fun slot => potentialRead (points slot)
def remainders (points : Points) : SpatialRemainders := fun slot => spatialRemainder (points slot)
def restorePoints (values : Fin 65 → ℝ) (spatial : SpatialRemainders) : Points :=
  fun slot => restorePoint (values slot) (spatial slot)

theorem materials_restored (values : Fin 65 → ℝ) (spatial : SpatialRemainders) :
    materials (restorePoints values spatial) = values :=
  funext (fun slot => restore_read (values slot) (spatial slot))

theorem remainders_restored (values : Fin 65 → ℝ) (spatial : SpatialRemainders) :
    remainders (restorePoints values spatial) = spatial := rfl

theorem points_recovered (points : Points) : restorePoints (materials points) (remainders points) = points :=
  funext (fun slot => point_recovered (points slot))

def coframeMaterials (points : Points) : LorentzianCoframeDerivative :=
  fun direction row column => materials points (RationalSourceFormation.coframeIndex (direction, row, column)).succ

/-- The source factory reads only one discrete history and 65 complete
operands of the original generated mother potential. -/
def sourceOf (visit : MotherVisit) (points : Points) : SmoothUnifiedSource :=
  let discrete := StageEightDiscreteFormation.sourceAtVisit visit
  { discrete with
    stageEight := { discrete.stageEight with coframeLinearCoefficient := coframeMaterials points }
    continuousContactResidual := materials points 0 }

theorem discrete_retained (visit : MotherVisit) (points : Points) :
    readMaterial (sourceOf visit points) = readMaterial (StageEightDiscreteFormation.sourceAtVisit visit) := rfl

theorem materials_increment (points displacement : Points) :
    materials (points + displacement) = materials points + materials displacement :=
  funext (fun slot => potential_read_increment (points slot) (displacement slot))

theorem remainders_increment (points displacement : Points) :
    remainders (points + displacement) = remainders points + remainders displacement := rfl

theorem coframe_increment (points displacement : Points) :
    coframeMaterials (points + displacement) = coframeMaterials points + coframeMaterials displacement := by
  funext direction row column
  exact congrFun (materials_increment points displacement)
    (RationalSourceFormation.coframeIndex (direction, row, column)).succ

theorem source_material_increment (visit : MotherVisit) (points displacement : Points) :
    (sourceOf visit (points + displacement)).stageEight.coframeLinearCoefficient -
        (sourceOf visit points).stageEight.coframeLinearCoefficient = coframeMaterials displacement ∧
      (sourceOf visit (points + displacement)).continuousContactResidual -
        (sourceOf visit points).continuousContactResidual = materials displacement 0 := by
  constructor
  · change coframeMaterials (points + displacement) - coframeMaterials points = _
    rw [coframe_increment]
    abel
  · change materials (points + displacement) 0 - materials points 0 = _
    rw [materials_increment]
    simp

/-- Every full raw source lies in this actual potential image. Spatial
remainders are retained freely in the full operands and are not read as source fields. -/
theorem every_source_generated (source : SmoothUnifiedSource) (spatial : SpatialRemainders) :
    ∃ code points, sourceOf (Stage9C.Revision.SpinPair.visit (10 + code)) points = source ∧
      remainders points = spatial := by
  obtain ⟨code, discrete⟩ := every_source_discrete_generated source
  let values : Fin 65 → ℝ := Fin.cons source.continuousContactResidual
    (fun slot : Fin 64 => source.stageEight.coframeLinearCoefficient
      (RationalSourceFormation.coframeIndex.symm slot).1
      (RationalSourceFormation.coframeIndex.symm slot).2.1
      (RationalSourceFormation.coframeIndex.symm slot).2.2)
  let points := restorePoints values spatial
  have valuesRead : materials points = values := materials_restored values spatial
  have coframeRead : coframeMaterials points = source.stageEight.coframeLinearCoefficient := by
    funext direction row column
    unfold coframeMaterials
    rw [valuesRead]
    simp only [values, Fin.cons_succ, Equiv.symm_apply_apply]
  have contactRead : materials points 0 = source.continuousContactResidual := by
    rw [valuesRead]
    rfl
  refine ⟨code, points, ?_, remainders_restored values spatial⟩
  unfold sourceOf
  rw [discrete]
  change { source with
    stageEight := { source.stageEight with coframeLinearCoefficient := coframeMaterials points },
    continuousContactResidual := materials points 0 } = source
  rw [coframeRead, contactRead]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.PotentialSourceFormation
