import H0mework.Physics.MotherProgrammesFormationCoordinates.Consumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholePointFormation

open Stage9C.Revision
open MotherCoordinateCompletion MotherFamilyOccurrence PotentialSourceFormation
open ProofFreeRicherAnholonomicSource
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

abbrev Carrier := Completed (65 * 4)

def index : Fin 65 × Fin 4 ≃ Fin (65 * 4) := finProdFinEquiv

def coordinate (value : Carrier) (slot : Fin 65) (axis : Fin 4) : ℝ :=
  coordinates (65 * 4) value (index (slot, axis))

/-- All material and spatial coordinates are read from one completed
finite source range. No separate real remainder is an input. -/
def points (value : Carrier) : Points :=
  restorePoints (fun slot => coordinate value slot 0)
    (fun slot axis => coordinate value slot axis.succ)

def readPoints (operands : Points) : Fin (65 * 4) → ℝ :=
  fun address =>
    let pair := index.symm address
    Fin.cases (materials operands pair.1) (remainders operands pair.1) pair.2

theorem materials_points (value : Carrier) :
    materials (points value) = fun slot => coordinate value slot 0 :=
  materials_restored _ _

theorem spatial_points (value : Carrier) :
    remainders (points value) = fun slot axis => coordinate value slot axis.succ :=
  remainders_restored _ _

theorem read_points (value : Carrier) :
    readPoints (points value) = coordinates (65 * 4) value := by
  funext address
  obtain ⟨⟨slot, axis⟩, rfl⟩ := index.surjective address
  simp only [readPoints, Equiv.symm_apply_apply, materials_points, spatial_points]
  exact Fin.cases rfl (fun _ => rfl) axis

theorem points_read (operands : Points) :
    points ((realEquiv (65 * 4)).symm (readPoints operands)) = operands := by
  have coordinate_read (slot : Fin 65) (axis : Fin 4) :
      coordinate ((realEquiv (65 * 4)).symm (readPoints operands)) slot axis =
        Fin.cases (materials operands slot) (remainders operands slot) axis := by
    unfold coordinate
    change realEquiv (65 * 4) ((realEquiv (65 * 4)).symm (readPoints operands)) _ = _
    rw [(realEquiv (65 * 4)).apply_symm_apply]
    simp only [readPoints, Equiv.symm_apply_apply]
  unfold points
  simp_rw [coordinate_read]
  exact points_recovered operands

def pointEquiv : Carrier ≃ Points where
  toFun := points
  invFun operands := (realEquiv (65 * 4)).symm (readPoints operands)
  left_inv value := by
    change (realEquiv (65 * 4)).symm (readPoints (points value)) = value
    rw [read_points]
    exact (realEquiv (65 * 4)).symm_apply_apply value
  right_inv := points_read

theorem finite_native_coordinate (visit : MotherVisit) (slot : Fin 65) (axis : Fin 4) :
    coordinate (fromVisit (65 * 4) visit : Carrier) slot axis =
      RationalSourceFormation.sourceTrace
        (StageEightDiscreteFormation.sourceAtVisit (sample (65 * 4) visit (index (slot, axis)))) :=
  finite_native_read (65 * 4) visit (index (slot, axis))

theorem finite_sample_is_past (visit : MotherVisit) (slot : Fin 65) (axis : Fin 4) :
    temporalDepth (sample (65 * 4) visit (index (slot, axis))).history ≤ temporalDepth visit.history :=
  sample_is_past (65 * 4) visit (index (slot, axis))

theorem actual_material (value : Carrier) (slot : Fin 65) :
    curvatureRate (StageNineEnrichedProofFreeSource.generatedMotherPotential Runtime.source
      (points value slot) 1) = coordinate value slot 0 :=
  congrFun (materials_points value) slot

theorem actual_spatial (value : Carrier) (slot : Fin 65) (axis : Fin 3) :
    points value slot axis.succ = coordinate value slot axis.succ :=
  congrFun (congrFun (spatial_points value) slot) axis

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholePointFormation
