import H0mework.Versions.V2.Arithmetic.RieszGreen.RawDerivative

/-! A source-only Ward probe: the original return, kernel and both endpoints stay together. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Constructor

open Complex MeasureTheory
open scoped FourierTransform Topology

noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal

local notation "q" => (1 / 4 : ℝ)

def phase (frequency position : ℝ) : ℂ := 𝐞 (-(frequency * position))

theorem phase_derivative (frequency position : ℝ) :
    HasDerivAt (phase frequency)
      (-2 * (Real.pi : ℂ) * Complex.I * (frequency : ℂ) * phase frequency position) position := by
  have source := (Real.hasDerivAt_fourierChar (-(frequency * position))).scomp position
    (((hasDerivAt_id position).const_mul frequency).neg)
  have normalized : HasDerivAt (phase frequency)
      ((-frequency) • (2 * (Real.pi : ℂ) * Complex.I * phase frequency position)) position := by
    simpa only [phase, Function.comp_def, Pi.neg_apply, id_eq, mul_one] using! source
  convert! normalized using 1
  simp only [Complex.real_smul, Complex.ofReal_neg]
  ring

private theorem phase_continuous (frequency : ℝ) : Continuous (phase frequency) :=
  continuous_iff_continuousAt.mpr fun position => (phase_derivative frequency position).continuousAt

/-- The Euler/Fourier bulk for the actual `S b` is exactly its two source traces. -/
theorem return_kernel_ward (coordinate : BurnolCompletedMellinCoordinate) (frequency : ℝ) :
    (∫ position : ℝ in (-q)..q,
      phase frequency position *
        ((1 - 2 * (Real.pi : ℂ) * Complex.I * (frequency : ℂ) * (position : ℂ)) *
            burnolRieszReturnRaw coordinate position +
          (position : ℂ) * burnolRieszReturnRawDerivative coordinate position)) =
      (q : ℂ) * (phase frequency q * burnolRieszReturnRaw coordinate q +
        phase frequency (-q) * burnolRieszReturnRaw coordinate (-q)) := by
  let primitive := fun position : ℝ =>
    (position : ℂ) * phase frequency position * burnolRieszReturnRaw coordinate position
  let density := fun position : ℝ =>
    phase frequency position *
      ((1 - 2 * (Real.pi : ℂ) * Complex.I * (frequency : ℂ) * (position : ℂ)) *
          burnolRieszReturnRaw coordinate position +
        (position : ℂ) * burnolRieszReturnRawDerivative coordinate position)
  have derivative (position : ℝ) : HasDerivAt primitive (density position) position := by
    have source := ((Complex.ofRealCLM.hasDerivAt (x := position)).mul
      (phase_derivative frequency position)).mul
        (burnolRieszReturnRaw_hasDerivAt coordinate position)
    convert! source using 1
    simp only [density, Complex.ofRealCLM_apply, Pi.mul_apply, Complex.ofReal_one]
    ring
  have continuous : Continuous density := by
    have kernel := phase_continuous frequency
    have returned := burnolRieszReturnRaw_continuous coordinate
    have returnedDerivative := burnolRieszReturnRawDerivative_continuous coordinate
    dsimp only [density]
    fun_prop
  have actual := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun position _ => derivative position) (continuous.intervalIntegrable (-q) q)
  change (∫ position : ℝ in (-q)..q, density position) = _
  rw [actual]
  dsimp only [primitive]
  push_cast
  ring

end
end OriginalRieszSource.Constructor
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
