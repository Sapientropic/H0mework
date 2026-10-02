import H0mework.Versions.R2.Physics.CompositeSpectrum.Naturality
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The full action's oriented cubic transforms by the determinant under
magnetic-component basis changes. Proper spatial rotations therefore leave
it fixed before any occupied readout or dual pairing. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open DiracExteriorMatterAction
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF

noncomputable section

def mixComponents {A : Type*} [AddCommGroup A] [Module ℂ A]
    (rotation : Matrix (Fin 3) (Fin 3) ℂ) (fields : Fin 3 → A) : Fin 3 → A :=
  fun axis => ∑ component, rotation axis component • fields component

theorem alternatingProduct_mixing {A : Type*} [Ring A] [Algebra ℂ A]
    (rotation : Matrix (Fin 3) (Fin 3) ℂ) (fields : Fin 3 → A) :
    alternatingProduct (mixComponents rotation fields) = rotation.det • alternatingProduct fields := by
  simp only [alternatingProduct, mixComponents, Fin.sum_univ_three, Matrix.det_fin_three]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_add, smul_sub, mul_assoc]
  module

def rotatedCompositeAction (rotation : Matrix (Fin 3) (Fin 3) ℂ) (point : BasePoint) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  alternatingProduct (mixComponents rotation (incomingCurvatureAction point))

theorem rotatedCompositeAction_det (rotation : Matrix (Fin 3) (Fin 3) ℂ) (point : BasePoint) :
    rotatedCompositeAction rotation point = rotation.det • compositeAction point :=
  alternatingProduct_mixing rotation (incomingCurvatureAction point)

theorem rotatedCompositeAction_volumePreserving (rotation : Matrix (Fin 3) (Fin 3) ℂ)
    (volume : rotation.det = 1) (point : BasePoint) :
    rotatedCompositeAction rotation point = compositeAction point := by
  rw [rotatedCompositeAction_det, volume, one_smul]

def spatialRotationMatrix (rotation : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  (rotation : Matrix (Fin 3) (Fin 3) ℝ).map Complex.ofReal

theorem spatialRotationMatrix_det (rotation : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    (spatialRotationMatrix rotation).det = 1 := by
  have determinant : (rotation : Matrix (Fin 3) (Fin 3) ℝ).det = 1 :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp rotation.property).2
  change (Complex.ofRealHom.mapMatrix (rotation : Matrix (Fin 3) (Fin 3) ℝ)).det = 1
  rw [← Complex.ofRealHom.map_det, determinant, map_one]

theorem compositeAction_spatialRotation
    (rotation : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (point : BasePoint) :
    rotatedCompositeAction (spatialRotationMatrix rotation) point = compositeAction point :=
  rotatedCompositeAction_volumePreserving _ (spatialRotationMatrix_det rotation) point

theorem compositeAction_rotation_dual
    (rotation : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (point : BasePoint) :
    Runtime.configuration.conjugateMatter point
      (rotatedCompositeAction (spatialRotationMatrix rotation) point (Runtime.configuration.matter point)) =
      4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation (Runtime.tick.answer point) (cubic point) := by
  rw [compositeAction_spatialRotation, compositeAction_quantum_response]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
