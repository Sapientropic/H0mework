import H0mework.Versions.R2.Physics.Helicity.Transform
import H0mework.Versions.R2.Physics.CompositeSpectrum.Rotation

/-! Proper spatial rotations act simultaneously on the source connection
and magnetic components. The actual non-Abelian triad supplies their
proportionality, and determinant naturality gives the scalar contraction. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity

open Matrix ProofFreeRicherAnholonomicSource StageNineHolonomicField
open SU7MotherLieAlgebra SU7MotherGaugeTheory Stage9C.Material.SpinPair Stage9DEF
open StageNineP286GaugeConnectionVariation

noncomputable section

theorem magnetic_connection (point : BasePoint) (axis : Fin 3) :
    motherMagnetic point axis = -(gaugeScale : ℂ) • connectionMatrix point axis := by
  rw [motherMagnetic, magnetic_eq, connectionMatrix, Runtime.configuration_eq,
    Compatibility.actual_connection_source]
  simp only [p286LieBlockEmbed_real_smul, SetLike.val_smul]
  ext row column
  simp [Complex.real_smul]
  ring

theorem homogeneousHelicity_scaled (connection : Fin 3 → MotherMatrix) (scalar : ℂ) :
    homogeneousHelicity connection (fun axis => scalar • connection axis) =
      (12 * Complex.I * scalar ^ 2) * (alternatingProduct connection).trace := by
  simp [homogeneousHelicity, bracketCurl, bracket, alternatingProduct,
    Fin.sum_univ_three, Matrix.mul_sub,
    Matrix.mul_assoc, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem mixComponents_smul (rotation : Matrix (Fin 3) (Fin 3) ℂ)
    (connection : Fin 3 → MotherMatrix) (scalar : ℂ) :
    mixComponents rotation (fun i => scalar • connection i) =
      fun axis => scalar • mixComponents rotation connection axis := by
  funext axis
  simp only [mixComponents, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro component _
  rw [mul_comm]

theorem actual_rotation_invariant (rotation : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (point : BasePoint) :
    homogeneousHelicity (mixComponents (spatialRotationMatrix rotation) (connectionMatrix point))
      (mixComponents (spatialRotationMatrix rotation) (motherMagnetic point)) = value point := by
  have field : motherMagnetic point = fun axis => -(gaugeScale : ℂ) • connectionMatrix point axis :=
    funext (magnetic_connection point)
  have rotated : mixComponents (spatialRotationMatrix rotation) (motherMagnetic point) =
      fun axis => -(gaugeScale : ℂ) •
        mixComponents (spatialRotationMatrix rotation) (connectionMatrix point) axis := by
    rw [field]
    exact mixComponents_smul _ _ _
  rw [rotated, homogeneousHelicity_scaled, alternatingProduct_mixing,
    spatialRotationMatrix_det, one_smul, value_homogeneous, field, homogeneousHelicity_scaled]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity
