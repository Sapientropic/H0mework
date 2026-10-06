import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.Source
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Coulomb

/-! The source-generated Green kernel is consumed by every original four-index ERI address, with length conversion explicit. -/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.GreenSource
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open MeasureTheory BasinRefinement SourceGaussianModel SourceFiniteData SourceCoulomb
open UnifiedOrbitals
noncomputable section

theorem distance_scaled (lengthUnit : ℝ) (positive : 0 < lengthUnit) (point : Point) :
    distance (lengthUnit • point) = lengthUnit*distance point := by
  unfold distance
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg lengthUnit), Real.sqrt_sq_eq_abs, abs_of_pos positive]

def greenCoefficient (lengthUnit : ℝ) : ℝ := (8*Real.pi*lapse*lengthUnit)⁻¹

theorem green_scaled (lengthUnit : ℝ) (positive : 0 < lengthUnit) (point : Point) :
    green (lengthUnit • point) = greenCoefficient lengthUnit*kernel point := by
  rw [green_kernel]
  unfold kernel
  rw [distance_scaled lengthUnit positive]
  simp only [greenCoefficient, div_eq_mul_inv, mul_inv_rev]
  ring

def greenMatrixEntry (lengthUnit : ℝ) (i j k l : Basis) : ℝ :=
  ∫ z : Point × Point, ao i z.1*ao j z.1*(ao k z.2*ao l z.2)*
    green (lengthUnit • (z.2-z.1))

theorem green_matrix_integrable (lengthUnit : ℝ) (positive : 0 < lengthUnit) (i j k l : Basis) :
    Integrable (fun z : Point × Point => ao i z.1*ao j z.1*(ao k z.2*ao l z.2)*
      green (lengthUnit • (z.2-z.1))) := by
  have same : (fun z : Point × Point => ao i z.1*ao j z.1*(ao k z.2*ao l z.2)*
      green (lengthUnit • (z.2-z.1))) =
      fun z => greenCoefficient lengthUnit*(ao i z.1*ao j z.1*(ao k z.2*ao l z.2)*kernel (z.2-z.1)) := by
    funext z
    rw [green_scaled lengthUnit positive]
    ring
  rw [same]
  exact (quartet_integrable i j k l).const_mul _

theorem original_ERI_green (lengthUnit : ℝ) (positive : 0 < lengthUnit) (i j k l : Basis) :
    greenMatrixEntry lengthUnit i j k l = greenCoefficient lengthUnit*electronRepulsion i j k l := by
  unfold greenMatrixEntry electronRepulsion
  simp_rw [green_scaled lengthUnit positive]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  ring


end
end LAlanine40K2025.UnifiedAction.GreenSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
