import H0mework.Physics.MotherSource.Contact
import H0mework.Versions.R2.Physics.RootRuntime.RuntimeOccurrence

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.PotentialSourceFormation

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource SU7MotherLieAlgebra

noncomputable section

def potentialRead (point : BasePoint) : ℝ :=
  curvatureRate (generatedMotherPotential Runtime.source point 1)

theorem potential_read_formula (point : BasePoint) : potentialRead point = Real.pi * point 0 := by
  unfold potentialRead
  rw [Runtime.source_eq]
  unfold generatedMotherPotential
  rw [if_pos rfl, positive_continuousContactRate]
  simp [curvatureRate, motherHyperchargeDirection_hyperPlus_entry]

def spatialRemainder (point : BasePoint) : Fin 3 → ℝ := fun index => point index.succ

def restorePoint (material : ℝ) (spatial : Fin 3 → ℝ) : BasePoint :=
  WithLp.toLp 2 (Fin.cons (material / Real.pi) spatial)

theorem restore_read (material : ℝ) (spatial : Fin 3 → ℝ) :
    potentialRead (restorePoint material spatial) = material := by
  rw [potential_read_formula]
  change Real.pi * (material / Real.pi) = material
  field_simp

theorem restore_spatial (material : ℝ) (spatial : Fin 3 → ℝ) :
    spatialRemainder (restorePoint material spatial) = spatial := rfl

theorem point_recovered (point : BasePoint) :
    restorePoint (potentialRead point) (spatialRemainder point) = point := by
  apply PiLp.ext
  intro index
  refine Fin.cases ?_ ?_ index
  · simp [restorePoint, potential_read_formula, Real.pi_ne_zero]
  · intro spatial
    rfl

def pointEquiv : BasePoint ≃ ℝ × (Fin 3 → ℝ) where
  toFun point := (potentialRead point, spatialRemainder point)
  invFun data := restorePoint data.1 data.2
  left_inv := point_recovered
  right_inv data := Prod.ext (restore_read data.1 data.2) (restore_spatial data.1 data.2)

theorem potential_read_surjective : Function.Surjective potentialRead :=
  fun material => ⟨restorePoint material 0, restore_read material 0⟩

theorem potential_increment (point displacement : BasePoint) :
    generatedMotherPotential Runtime.source (point + displacement) 1 =
      generatedMotherPotential Runtime.source point 1 + generatedMotherPotential Runtime.source displacement 1 := by
  exact generatedMotherPotential_increment Runtime.source point displacement

private theorem read_add (first second : SU7MotherLieMatrix) :
    curvatureRate (first + second) = curvatureRate first + curvatureRate second := by
  simp [curvatureRate]

theorem potential_read_increment (point displacement : BasePoint) :
    potentialRead (point + displacement) = potentialRead point + potentialRead displacement := by
  exact (congrArg curvatureRate (potential_increment point displacement)).trans (read_add _ _)

theorem spatial_increment (point displacement : BasePoint) :
    spatialRemainder (point + displacement) = spatialRemainder point + spatialRemainder displacement := rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.PotentialSourceFormation
