import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenPointwise

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel
open scoped ContDiff
noncomputable section

theorem spatialFirst_mul {f g : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (index : Fin 3) (point : Point) :
    spatialFirst (fun p => f p*g p) index point = spatialFirst f index point*g point+f point*spatialFirst g index point := by
  unfold spatialFirst
  rw [fderiv_fun_mul (hf.differentiable (by simp) point) (hg.differentiable (by simp) point)]
  simp
  ring

theorem cutoff_energy_point {f cut : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hc : ContDiff ℝ ∞ cut)
    (index : Fin 3) (point : Point) :
    (spatialFirst (fun p => cut p*f p) index point)^2 =
      spatialFirst f index point*spatialFirst (fun p => cut p*cut p*f p) index point+
        f point^2*(spatialFirst cut index point)^2 := by
  simp only [spatialFirst_mul hc hf, spatialFirst_mul (hc.mul hc) hf, spatialFirst_mul hc hc]
  ring

theorem cutoff_energy_coordinate {f cut : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hc : ContDiff ℝ ∞ cut)
    (support : HasCompactSupport cut) (index : Fin 3) :
    (∫ point, (spatialFirst (fun p => cut p*f p) index point)^2) =
      -(∫ point, spatialFirst (spatialFirst f index) index point*(cut point*cut point*f point))+
        (∫ point, f point^2*(spatialFirst cut index point)^2) := by
  have supportTest : HasCompactSupport (fun p => cut p*cut p*f p) := support.mul_right.mul_right
  have firstIntegral := compact_mul_integrable (spatialFirst_smooth hf index).continuous
    (spatialFirst_smooth ((hc.mul hc).mul hf) index).continuous (compact_first_support supportTest index)
  have supportError : HasCompactSupport (fun p => (spatialFirst cut index p)^2) := by
    convert (compact_first_support support index).mul_right (f' := spatialFirst cut index) using 1 <;>
      first | rfl | (funext point; simp only [pow_two, Pi.mul_apply])
  have errorIntegral := compact_mul_integrable (hf.continuous.pow 2) ((spatialFirst_smooth hc index).continuous.pow 2) supportError
  change Integrable (fun point => f point^2*(spatialFirst cut index point)^2) at errorIntegral
  simp_rw [cutoff_energy_point hf hc]
  rw [integral_add firstIntegral errorIntegral,
    compact_pairing_first (spatialFirst_smooth hf index) ((hc.mul hc).mul hf) supportTest]

def gradientSquare (f : Point → ℝ) (point : Point) : ℝ :=
  ∑ index : Fin 3, (spatialFirst f index point)^2

theorem compact_square_integrable {f : Point → ℝ} (continuous : Continuous f) (support : HasCompactSupport f) :
    Integrable (fun point => f point^2) := by
  simpa only [pow_two] using compact_mul_integrable continuous continuous support

theorem cutoff_energy_identity {f cut : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hc : ContDiff ℝ ∞ cut)
    (support : HasCompactSupport cut) :
    (∫ point, gradientSquare (fun p => cut p*f p) point) =
      -(∫ point, spatialLap f point*(cut point*cut point*f point))+
        (∫ point, f point^2*gradientSquare cut point) := by
  have supportProduct : HasCompactSupport (fun p => cut p*f p) := support.mul_right
  have supportTest : HasCompactSupport (fun p => cut p*cut p*f p) := support.mul_right.mul_right
  have derivativeIntegral (index : Fin 3) := compact_square_integrable
    (spatialFirst_smooth (hc.mul hf) index).continuous (compact_first_support supportProduct index)
  have lapIntegral (index : Fin 3) := compact_mul_integrable
    (spatialFirst_smooth (spatialFirst_smooth hf index) index).continuous ((hc.mul hc).mul hf).continuous supportTest
  have errorIntegral (index : Fin 3) : Integrable (fun point => f point^2*(spatialFirst cut index point)^2) := by
    have supportSquare : HasCompactSupport (fun point => (spatialFirst cut index point)^2) := by
      convert (compact_first_support support index).mul_right (f' := spatialFirst cut index) using 1 <;>
        first | rfl | (funext point; simp only [pow_two, Pi.mul_apply])
    exact compact_mul_integrable (hf.continuous.pow 2) ((spatialFirst_smooth hc index).continuous.pow 2) supportSquare
  simp only [gradientSquare, spatialLap, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun index _ => derivativeIntegral index),
    integral_finsetSum Finset.univ (fun index _ => lapIntegral index),
    integral_finsetSum Finset.univ (fun index _ => errorIntegral index)]
  simp_rw [cutoff_energy_coordinate hf hc support]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.GreenSource
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open MeasureTheory BasinRefinement SourceGaussianModel
open scoped ContDiff
noncomputable section

theorem original_D3_cutoff_energy (cut : Point → ℝ) (smooth : ContDiff ℝ ∞ cut)
    (support : HasCompactSupport cut) :
    lapse*(∫ point, gradientSquare (fun p => cut p*sourcePotential p) point) =
      -(1/2)*(∫ point, sourceCurrent point*(cut point*cut point*sourcePotential point))+
        lapse*(∫ point, sourcePotential point^2*gradientSquare cut point) := by
  have same : (fun point => sourceCurrent point*(cut point*cut point*sourcePotential point)) =
      fun point => (2*lapse)*(spatialLap sourcePotential point*(cut point*cut point*sourcePotential point)) := by
    funext point
    have generated := original_D3_pointwise_gauss point
    linear_combination (cut point*cut point*sourcePotential point)*generated
  rw [same, integral_const_mul, cutoff_energy_identity sourcePotential_smooth smooth support]
  ring

end
end LAlanine40K2025.UnifiedAction.GreenSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
