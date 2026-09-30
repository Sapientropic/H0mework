import H0mework.NavierStokes.StressAction.CompleteStressCarrier
import H0mework.NavierStokes.TimeJets.TimeBilinear

/-!
The original mixed flux acts continuously on the complete H⁻² stress carrier.
The zero Fourier row and every tensor component are retained.
-/

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeCompleteStressBilinear

open Set
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeCompleteStressCarrier NativeHigherTimeJets

noncomputable section

def mixed (left right : ComplexVorticityHilbertState) : Space :=
  ofBound (mixedFlux left right) (3 * ‖left‖ * ‖right‖)
    (mixedFlux_norm_le left right)

theorem mixed_read (left right : ComplexVorticityHilbertState) :
    read (mixed left right) = mixedFlux left right := read_ofBound _ _ _

def mixedBound : ℝ := 9 * Real.sqrt (∑' wave, weight wave ^ 2)

theorem mixed_norm_le (left right : ComplexVorticityHilbertState) :
    ‖mixed left right‖ ≤ mixedBound * ‖left‖ * ‖right‖ := by
  have paid := ofBound_norm_sq (mixedFlux left right) (3 * ‖left‖ * ‖right‖)
    (mixedFlux_norm_le left right)
  have root : Real.sqrt (∑' wave, weight wave ^ 2) ^ 2 = ∑' wave, weight wave ^ 2 :=
    Real.sq_sqrt (tsum_nonneg (fun wave => sq_nonneg (weight wave)))
  apply (sq_le_sq₀ (norm_nonneg _) (by unfold mixedBound; positivity)).mp
  change ‖mixed left right‖ ^ 2 ≤ _
  calc
    _ ≤ 9 * (3 * ‖left‖ * ‖right‖) ^ 2 * ∑' wave, weight wave ^ 2 := paid
    _ = _ := by unfold mixedBound; simp only [mul_pow, root]; ring

def mixedLinear : ComplexVorticityHilbertState →ₗ[ℝ] ComplexVorticityHilbertState →ₗ[ℝ] Space where
  toFun left :=
    { toFun := mixed left
      map_add' right other := by
        apply read_injective
        funext wave output input
        change (readCLM wave output input) (mixed left (right + other)) =
          (readCLM wave output input) (mixed left right + mixed left other)
        simp only [map_add, readCLM_apply, mixed_read, mixedFlux_add_right]
      map_smul' scalar right := by
        apply read_injective
        funext wave output input
        change read (mixed left (scalar • right)) wave output input =
          (weight wave)⁻¹ • (scalar • (mixed left right) wave (output, input))
        rw [smul_comm]
        change read (mixed left (scalar • right)) wave output input = scalar • read (mixed left right) wave output input
        simp only [mixed_read, mixedFlux_smul_right] }
  map_add' left other := by
    ext right wave pair
    change weight wave • mixedFlux (left + other) right wave pair.1 pair.2 =
      weight wave • mixedFlux left right wave pair.1 pair.2 + weight wave • mixedFlux other right wave pair.1 pair.2
    rw [mixedFlux_add_left, smul_add]
  map_smul' scalar left := by
    ext right wave pair
    change weight wave • mixedFlux (scalar • left) right wave pair.1 pair.2 =
      scalar • (weight wave • mixedFlux left right wave pair.1 pair.2)
    rw [mixedFlux_smul_left, smul_comm]

def mixedCLM : ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState →L[ℝ] Space :=
  mixedLinear.mkContinuous₂ mixedBound mixed_norm_le

theorem mixedCLM_apply (left right : ComplexVorticityHilbertState) : mixedCLM left right = mixed left right := rfl

theorem mixed_hasDerivWithinAt
    {left right : ℝ → ComplexVorticityHilbertState} {leftRate rightRate : ComplexVorticityHilbertState}
    {domain : Set ℝ} {time : ℝ}
    (leftDerivative : HasDerivWithinAt left leftRate domain time)
    (rightDerivative : HasDerivWithinAt right rightRate domain time) :
    HasDerivWithinAt (fun actual => mixed (left actual) (right actual))
      (mixed leftRate (right time) + mixed (left time) rightRate) domain time := by
  have actual := (mixedCLM.hasFDerivAt.comp_hasDerivWithinAt time leftDerivative).clm_apply rightDerivative
  simpa only [mixedCLM_apply, Function.comp_def] using actual

end
end SaturationMonoid.NavierStokes.NativeCompleteStressBilinear
