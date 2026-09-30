import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.Kernel

import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.Multilinear
import H0mework.NavierStokes.StressAction.Stress

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadChannels

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open NativeTimeJetCarrier NativeUnheatedStressPairEvolution NativeUnheatedTriadKernel

noncomputable section

def basis (i j : Coordinate) : NativeFluidStressCoefficient :=
  Pi.single j (Pi.single i (-1 : ℂ))

theorem basis_square (i j : Coordinate) :
    (∑ output : Coordinate, ∑ input : Coordinate, Complex.normSq (basis i j output input)) = 1 := by
  classical
  simp [basis, Pi.single_apply, ite_apply, apply_ite]

def pressure (wave : IntegerWavevector) (i j output : Coordinate) : ℂ :=
  projectedDivergenceCLM wave (basis i j) output

theorem pressure_bound (wave : IntegerWavevector) (i j output : Coordinate) :
    ‖pressure wave i j output‖ ≤ Real.sqrt (integerWaveViscousMultiplier wave) := by
  by_cases zero : wave = 0
  · subst wave
    simp [pressure, projectedDivergenceCLM_apply, transverseProjection]
  · have divergence := NativeFullOrderStress.divergence_amplitude_le (fun _ => basis i j) wave
    rw [basis_square, mul_one] at divergence
    have projected := transverseProjection_amplitudeSq_le wave zero
      (nativeFluidStressDivergenceCoefficient (fun _ => basis i j) wave)
    have coordinate := Finset.single_le_sum (fun x (_ : x ∈ (Finset.univ : Finset Coordinate)) =>
      Complex.normSq_nonneg (projectedDivergenceCLM wave (basis i j) x)) (Finset.mem_univ output)
    change Complex.normSq (pressure wave i j output) ≤ _ at coordinate
    have square : ‖pressure wave i j output‖ ^ 2 ≤ integerWaveViscousMultiplier wave := by
      rw [← Complex.normSq_eq_norm_sq]
      exact coordinate.trans (projected.trans divergence)
    exact (Real.le_sqrt (norm_nonneg _) (multiplier_nonnegative wave)).mpr square

theorem projected_complex_smul (wave : IntegerWavevector) (scalar : ℂ) (stress : NativeFluidStressCoefficient) :
    projectedDivergenceCLM wave (scalar • stress) = scalar • projectedDivergenceCLM wave stress := by
  change transverseProjection wave (NativeStressCurlAlgebra.stressDivergenceCLM wave (scalar • stress)) = _
  rw [map_smul]
  exact ThreeDimensionalVorticityCoefficientCoarseFilterProcess.transverseProjection_smul wave scalar _

theorem dyad_basis (left right : ComplexCoordinateVector) :
    (fun output input => -(right output * left input)) =
      ∑ i : Coordinate, ∑ j : Coordinate, (left i * right j) • basis i j := by
  classical
  funext output input
  simp [basis, Pi.single_apply, apply_ite, Finset.sum_apply, mul_comm]

theorem pressure_dyad (wave : IntegerWavevector) (left right : ComplexCoordinateVector) (output : Coordinate) :
    projectedDivergenceCLM wave (fun i j => -(right i * left j)) output =
      ∑ i : Coordinate, ∑ j : Coordinate, pressure wave i j output * (left i * right j) := by
  rw [dyad_basis, map_sum]
  simp only [map_sum, projected_complex_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pressure]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def kernel (nu : Viscosity) (slot : Fin 3) (i j output : Coordinate)
    (a b c : IntegerWavevector) : ℂ :=
  ((decay nu (a+b) c)⁻¹ * (triadDecay nu a b c)⁻¹ *
    Real.sqrt (integerWaveViscousMultiplier (![a,b,c] slot))) • pressure (a+b) i j output

def cap (nu : Viscosity) : ℝ :=
  (2 / nu.coeff) * (nu.coeff * (2 * Real.pi)^2)⁻¹

theorem kernel_bound (nu : Viscosity) (slot : Fin 3) (i j output : Coordinate)
    (a b c : IntegerWavevector) :
    ‖kernel nu slot i j output a b c‖ ≤ cap nu * NativeCompleteStressCarrier.weight c := by
  have inSlot : ![a,b,c] slot = a ∨ ![a,b,c] slot = b ∨ ![a,b,c] slot = c := by
    fin_cases slot <;> simp
  have nonnegative : 0 ≤ (decay nu (a+b) c)⁻¹ * (triadDecay nu a b c)⁻¹ *
      Real.sqrt (integerWaveViscousMultiplier (![a,b,c] slot)) := by
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr ((mul_nonneg nu.coeff_pos.le (add_nonneg (multiplier_nonnegative (a+b)) (multiplier_nonnegative c)))))
      (inv_nonneg.mpr (triad_nonnegative a b c))) (Real.sqrt_nonneg _)
  rw [kernel, norm_smul, Real.norm_of_nonneg nonnegative]
  calc
    _ ≤ ((decay nu (a+b) c)⁻¹ * (triadDecay nu a b c)⁻¹ *
        Real.sqrt (integerWaveViscousMultiplier (![a,b,c] slot))) *
        Real.sqrt (integerWaveViscousMultiplier (a+b)) :=
      mul_le_mul_of_nonneg_left (pressure_bound (a+b) i j output) nonnegative
    _ = normalizedQuartic nu a b c (![a,b,c] slot) := by unfold normalizedQuartic; ring
    _ ≤ _ := normalized_quartic_internal a b c (![a,b,c] slot) inSlot

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadChannels
