import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.CutoffLaplacian
import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.CutoffLimit
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenFieldIntegrability
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenLaplacianBoundary

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel
open scoped ContDiff
noncomputable section

theorem spatialFirst_square (f : Point → ℝ) (smooth : ContDiff ℝ ∞ f) (index : Fin 3) (point : Point) :
    spatialFirst (fun p => f p^2) index point = 2*(f point*spatialFirst f index point) := by
  simp only [pow_two, spatialFirst_mul smooth smooth]
  ring

theorem spatialSecond_square (f : Point → ℝ) (smooth : ContDiff ℝ ∞ f) (index : Fin 3) (point : Point) :
    spatialFirst (spatialFirst (fun p => f p^2) index) index point =
      2*(spatialFirst f index point)^2+2*f point*spatialFirst (spatialFirst f index) index point := by
  have same : spatialFirst (fun p => f p^2) index = fun p => 2*(f p*spatialFirst f index p) :=
    funext (spatialFirst_square f smooth index)
  rw [same, spatialFirst_const_mul 2 _ (smooth.mul (spatialFirst_smooth smooth index)),
    spatialFirst_mul smooth (spatialFirst_smooth smooth index)]
  ring

theorem spatialLap_square (f : Point → ℝ) (smooth : ContDiff ℝ ∞ f) (point : Point) :
    spatialLap (fun p => f p^2) point = 2*gradientSquare f point+2*f point*spatialLap f point := by
  simp only [spatialLap, spatialSecond_square f smooth, Finset.sum_add_distrib, gradientSquare, Finset.mul_sum]

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.GreenSource
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open MeasureTheory BasinRefinement SourceGaussianModel
noncomputable section

theorem original_D3_linear_cutoff_energy (radius : ℝ) (positive : 0 < radius) :
    lapse*(∫ point : Point, cutoff radius point*gradientSquare sourcePotential point) =
      (lapse/2)*(∫ point : Point, laplacianBoundary radius point)-
        (1/2)*(∫ point : Point, cutoff radius point*(sourceCurrent point*sourcePotential point)) := by
  have pairing := compact_pairing_laplacian (sourcePotential_smooth.pow 2) (cutoff_smooth radius) (cutoff_compact radius positive)
  change (∫ point, laplacianBoundary radius point) = ∫ point, spatialLap (fun p => sourcePotential p^2) point*cutoff radius point at pairing
  have same : (fun point => lapse*(spatialLap (fun p => sourcePotential p^2) point*cutoff radius point)) =
      fun point => (2*lapse)*(cutoff radius point*gradientSquare sourcePotential point)+
        cutoff radius point*(sourceCurrent point*sourcePotential point) := by
    funext point
    rw [spatialLap_square sourcePotential sourcePotential_smooth]
    have gauss := original_D3_pointwise_gauss point
    linear_combination -(cutoff radius point*sourcePotential point)*gauss
  have equality : lapse*(∫ point, laplacianBoundary radius point) =
      (2*lapse)*(∫ point, cutoff radius point*gradientSquare sourcePotential point)+
        (∫ point, cutoff radius point*(sourceCurrent point*sourcePotential point)) := by
    rw [pairing, ← integral_const_mul, same,
      integral_add ((cutoff_mul_integrable _ source_gradient_integrable radius).const_mul _) (cutoff_mul_integrable _ source_current_potential_integrable radius),
      integral_const_mul]
  linarith

end
end LAlanine40K2025.UnifiedAction.GreenSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
