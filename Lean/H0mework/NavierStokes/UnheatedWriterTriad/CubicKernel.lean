import H0mework.NavierStokes.UnheatedWriterTriad.CubicRows
import H0mework.NavierStokes.UnheatedWriterTriad.Channels
import H0mework.NavierStokes.UnheatedWriterTriad.Absolute

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedCubicKernel
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeTimeJetCarrier NativeEndpointVelocityCarrier NativeResolventCompactness NativeWholeResolvent
open NativeWholeH1Mixed NativeWholeH1Pairing NativeUnheatedStressPairEvolution
open NativeUnheatedPairNegativeKernel NativeUnheatedTriadChannels
noncomputable section

def kernel (nu : Viscosity) (i j response : Coordinate) (a b c : IntegerWavevector) : ℂ :=
  ((decay nu (a+b) c)⁻¹*(root c)⁻¹) • pressure (a+b) i j response

def cap (nu : Viscosity) : ℝ := (2*nu.coeff)⁻¹*((2*Real.pi)^2)⁻¹

theorem kernel_bound (nu : Viscosity) (i j response : Coordinate) (a b c : IntegerWavevector) :
    ‖kernel nu i j response a b c‖ ≤ cap nu*NativeCompleteStressCarrier.weight c := by
  by_cases zero : c = 0
  · subst c
    simp only [kernel, root, integerWaveViscousMultiplier, integerWaveNormSq, Pi.zero_apply, Int.cast_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero, Real.sqrt_zero, inv_zero,
      zero_smul, norm_zero]
    unfold cap
    positivity [nu.coeff_pos, NativeCompleteStressCarrier.weight_pos 0]
  · have positive := root_positive c zero
    have coefficient0 : 0 ≤ (decay nu (a+b) c)⁻¹*(root c)⁻¹ := by
      unfold decay integerWaveViscousMultiplier
      positivity [nu.coeff_pos, integerWaveNormSq_nonneg (a+b), integerWaveNormSq_nonneg c]
    rw [kernel, norm_smul, Real.norm_of_nonneg coefficient0]
    apply (mul_le_mul_of_nonneg_left (pressure_bound (a+b) i j response) coefficient0).trans
    have paid := mul_le_mul_of_nonneg_right (NativeUnheatedPairNegativeKernel.kernel_bound (nu := nu) (a+b) c)
      (sq_nonneg ((root c)⁻¹))
    have same : ((decay nu (a+b) c)⁻¹*(root c)⁻¹)*root (a+b) =
        NativeUnheatedPairNegativeKernel.kernel nu (a+b) c*((root c)⁻¹)^2 := by
      unfold NativeUnheatedPairNegativeKernel.kernel
      field_simp
    change ((decay nu (a+b) c)⁻¹*(root c)⁻¹)*root (a+b) ≤ _
    rw [same]
    apply paid.trans_eq
    rw [inv_pow, root_sq]
    simp only [integerWaveViscousMultiplier, mul_inv_rev, cap, NativeCompleteStressCarrier.weight, if_neg zero]
    ring

def value (nu : Viscosity) (wave : IntegerWavevector) (i j response outside : Coordinate)
    (left right gradient : ComplexVorticityHilbertState) : ℂ :=
  NativeUnheatedTriadSum.value (kernel nu i j response) wave i j outside left right gradient

theorem value_absolute (nu : Viscosity) (wave : IntegerWavevector) (i j response outside : Coordinate)
    (left right gradient : ComplexVorticityHilbertState) :
    Summable (fun indices => ‖NativeUnheatedTriadSum.term (kernel nu i j response) wave i j outside left right gradient indices‖) :=
  NativeUnheatedTriadSum.absolute_summable _ (cap nu) (kernel_bound nu i j response) _ _ _ _ _ _ _

theorem value_bound (nu : Viscosity) (wave : IntegerWavevector) (i j response outside : Coordinate)
    (left right gradient : ComplexVorticityHilbertState) :
    ‖value nu wave i j response outside left right gradient‖ ≤
      (3*cap nu*‖NativeUnheatedTriadSum.weights‖)*‖left‖*‖right‖*‖gradient‖ :=
  NativeUnheatedTriadSum.norm_bound _ (cap nu) (kernel_bound nu i j response) _ _ _ _ _ _ _

theorem gradient_row (outer : wholePhysical) (regular : H1 outer) (wave : IntegerWavevector) :
    wholeVelocity (gradientValue outer regular) wave = root wave • wholeVelocity outer.1 wave := by
  by_cases zero : wave = 0
  · subst wave
    simp only [wholeVelocity_zero, smul_zero]
  · funext coordinate
    simp only [wholeVelocity_nonzero _ ⟨wave,zero⟩, gradientValue, root, Pi.smul_apply]
    rfl

end
end SaturationMonoid.NavierStokes.NativeUnheatedCubicKernel
