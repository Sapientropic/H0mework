import H0mework.Versions.X.NavierStokes.MaterialJets.DensitizedReceipt
import H0mework.Physics.DiracEvolution.FiberMassRiesz

set_option autoImplicit false
open scoped Matrix

namespace SaturationMonoid.NavierStokes.NativeCanonicalFriedrichsPrincipal

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineHolonomicField StageNineDiracMatterFiberMassRiesz
open ThreeDimensionalPeriodicCoarseFilterCore
open NativeCanonicalFluidCoframe NativeMaterialMomentumJet

noncomputable section

/-- The actual Stage-9 principal of the canonical source, including its volume. -/
def matrix (velocity : PhysicalSpace) (direction : Fin 4) : DiracMatrix :=
  (volumeFactor velocity : ℂ) •
    coframeCoordinateDiracEvolutionPrincipal (coframe velocity) direction

theorem coordinate_matrix (velocity : PhysicalSpace) (direction : Fin 4) :
    coframeCoordinateDiracEvolutionPrincipal (coframe velocity) direction =
      ((diagonal velocity direction)⁻¹ : ℝ) • diracFrameEvolutionPrincipal direction := by
  rw [coframeCoordinateDiracEvolutionPrincipal, inverseGamma]
  simp only [diracFrameEvolutionPrincipal, diracFramePrincipal]
  simp only [← smul_comm (Complex.I : ℂ) ((diagonal velocity direction)⁻¹ : ℝ),
    Matrix.mul_smul]

theorem matrix_coefficient (velocity : PhysicalSpace) (direction : Fin 4) :
    matrix velocity direction =
      (coefficient velocity direction : ℂ) • diracFrameEvolutionPrincipal direction := by
  rw [matrix, coordinate_matrix]
  change (volumeFactor velocity : ℂ) •
    (((diagonal velocity direction)⁻¹ : ℝ) : ℂ) • diracFrameEvolutionPrincipal direction = _
  rw [smul_smul]
  congr 1
  simp [coefficient, div_eq_mul_inv]

theorem mass (velocity : PhysicalSpace) :
    matrix velocity 0 = ((density velocity)⁻¹ : ℝ) • (1 : DiracMatrix) := by
  rw [matrix_coefficient, coefficient_eq, if_pos rfl,
    diracFrameEvolutionPrincipal_time_eq_one]
  rfl

theorem spatial (velocity : PhysicalSpace) (direction : Fin 3) :
    matrix velocity direction.succ = diracFrameEvolutionPrincipal direction.succ := by
  rw [matrix_coefficient, coefficient_eq, if_neg (Fin.succ_ne_zero direction)]
  simp

/-- Left normalization acts on the original whole equation, with its clock unchanged. -/
def normalized (velocity : PhysicalSpace) (direction : Fin 4) : DiracMatrix :=
  (density velocity : ℂ) • matrix velocity direction

theorem normalized_time (velocity : PhysicalSpace) : normalized velocity 0 = 1 := by
  rw [normalized, mass]
  change (density velocity : ℂ) • (((density velocity)⁻¹ : ℝ) : ℂ) • (1 : DiracMatrix) = _
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (density_pos velocity).ne']
  simp

theorem normalized_spatial (velocity : PhysicalSpace) (direction : Fin 3) :
    normalized velocity direction.succ =
      (density velocity : ℂ) • diracFrameEvolutionPrincipal direction.succ := by
  rw [normalized, spatial]

theorem normalized_mass_pairing (velocity : PhysicalSpace)
    (first second : MatterCoordinateCarrier) :
    matterFiberMassPairing (normalized velocity 0) first second =
      matterFiberMassPairing 1 first second := by rw [normalized_time]

theorem original_mass_pairing (velocity : PhysicalSpace)
    (first second : MatterCoordinateCarrier) :
    matterFiberMassPairing (matrix velocity 0) first second =
      (density velocity)⁻¹ * matterFiberMassPairing 1 first second := by
  rw [mass, map_smul]
  rfl

/-- This is the exact cost of a scalar normalization on every material test. -/
theorem normalization_factor (velocity : PhysicalSpace) (factor : ℝ)
    (normalizes : factor * (density velocity)⁻¹ = 1) :
    factor = density velocity := by
  have multiplied := congrArg (fun x : ℝ => x * density velocity) normalizes
  simpa [mul_assoc, inv_mul_cancel₀ (density_pos velocity).ne'] using multiplied

theorem mass_lower_iff (velocity : PhysicalSpace) (κ : ℝ) (positive : 0 < κ) :
    κ ≤ (density velocity)⁻¹ ↔ ‖velocity‖ ^ 2 ≤ 8 * (κ⁻¹ - 2) := by
  have inverse : κ ≤ (density velocity)⁻¹ ↔ density velocity ≤ κ⁻¹ := by
    simpa only [inv_inv] using inv_le_inv₀ (inv_pos.mpr positive) (density_pos velocity)
  rw [inverse]
  unfold density
  constructor <;> intro bound <;> nlinarith

local instance : MeasureTheory.MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem density_integral (velocity : NativePhysicalTimeAction.PhysicalField) :
    (∫ point : NativePhysicalFourier.Torus, density (velocity point)) =
      2 + ‖velocity‖ ^ 2 / 8 := by
  simpa only [NativePhysicalMaterial.temporalCurrent_eq, density] using
    NativePhysicalMaterial.temporalCurrent_integral velocity

end
end SaturationMonoid.NavierStokes.NativeCanonicalFriedrichsPrincipal
