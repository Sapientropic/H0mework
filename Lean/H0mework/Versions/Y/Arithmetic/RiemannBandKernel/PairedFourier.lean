import H0mework.Versions.Y.Arithmetic.RiemannUnitFourier.FourierPhysical
import H0mework.Versions.Y.Arithmetic.RiemannBandKernel.DirichletProjection

/-! The same zero's original Fourier response consumes the generated complementary Dirichlet face. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology ArithmeticFunction
noncomputable section
local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def burnolPaCombFourierResponseDirichletRaw (s : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  let b := 1 + burnolPaCombSourceWidth n
  ((n : ℂ) + 2) / (s / 2) *
    (-(b : ℂ) * burnolUnitTailDirichletRaw (1 - s) 1 (b * x) +
      burnolUnitTailDirichletRaw (1 - s) 1 x - burnolReciprocalStepWaveRaw 1 b x)

theorem burnolPaCombFourierResolvent_coeFn {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : ℕ) :
    (fourierL2 (burnolDirectRightResolvent (observation.coordinate / 2)
      (burnolPaCombApproximation n : BurnolL2)) : ℝ → ℂ) =ᵐ[volume]
        burnolPaCombFourierResponseDirichletRaw observation.coordinate n := by
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  let b := 1 + burnolPaCombSourceWidth n
  let V := burnolUnitTailResponse coordinate 1
  let count := burnolReciprocalStepNativeWave 1 b
  let shifted := (Real.sqrt b : ℂ) • burnolMultiplicativeDilation (Real.log b) (fourierL2 V)
  have ordered : 1 ≤ b := by dsimp only [b]; linarith [(burnolPaCombSourceWidth_bounds n).1]
  have positive : 0 < b := lt_of_lt_of_le (by norm_num) ordered
  have bounded : b ≤ 4 := by dsimp only [b]; linarith [(burnolPaCombSourceWidth_bounds n).2]
  have zNe : coordinate.value / 2 ≠ 0 := div_ne_zero observation.coordinate_ne_zero (by norm_num)
  have countEven : reflectL2 count = count := by
    dsimp only [count]
    rw [burnolReciprocalStepNativeWave_eq 1 b (by norm_num) ordered]
    exact mem_evenL2ClosedFace_iff.mp
      (burnolReciprocalStepWave_physical 1 b (by norm_num) ordered bounded).2
  have action := congrArg (fun value : BurnolL2 => (coordinate.value / 2)⁻¹ • fourierL2 value)
    (burnolPaBandResolvent_action coordinate b)
  simp only [map_smul, inv_smul_smul₀ zNe, map_sub,
    fourierL2_burnolMultiplicativeDilation, neg_neg] at action
  have twice : fourierL2 (fourierL2 count) = count := by rw [fourierL2_fourierL2, countEven]
  change fourierL2 (burnolDirectRightResolvent (coordinate.value / 2) (fourierL2 count)) =
    (coordinate.value / 2)⁻¹ • (shifted - fourierL2 V - fourierL2 (fourierL2 count)) at action
  rw [twice] at action
  have generated : fourierL2 (burnolDirectRightResolvent (coordinate.value / 2)
      (burnolPaCombApproximation n : BurnolL2)) =
        (((n : ℂ) + 2) / (coordinate.value / 2)) • (shifted - fourierL2 V - count) := by
    rw [burnolPaCombApproximation_raw, burnolDirectRightResolvent_smul, map_smul]
    change ((n : ℂ) + 2) • fourierL2 (burnolDirectRightResolvent (coordinate.value / 2) (fourierL2 count)) = _
    rw [action, smul_smul]
    rfl
  have shiftedRead : (shifted : ℝ → ℂ) =ᵐ[volume]
      fun x => (b : ℂ) * (-burnolUnitTailDirichletRaw (1 - observation.coordinate) 1 (b * x)) := by
    have scaleRead := burnolSourceScalePrimitive_coeFn (fourierL2 V)
      (fun x => -burnolUnitTailDirichletRaw (1 - observation.coordinate) 1 x)
      (burnolZeroOwnedUnitFourier_dirichlet_coeFn observation nontrivial rightHalf) b positive
    have same : shifted = burnolSourceScalePrimitive (fourierL2 V) b := by
      unfold shifted burnolSourceScalePrimitive
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rfl
    rw [same]
    exact scaleRead
  have countRead : (count : ℝ → ℂ) =ᵐ[volume] burnolReciprocalStepWaveRaw 1 b := by
    rw [show count = burnolReciprocalStepWaveL2 1 b (by norm_num) ordered from
      burnolReciprocalStepNativeWave_eq 1 b (by norm_num) ordered]
    exact (burnolReciprocalStepWave_memLp 1 b (by norm_num) ordered).coeFn_toLp
  change (fourierL2 (burnolDirectRightResolvent (coordinate.value / 2)
    (burnolPaCombApproximation n : BurnolL2)) : ℝ → ℂ) =ᵐ[volume] _
  rw [generated]
  filter_upwards [Lp.coeFn_smul (((n : ℂ) + 2) / (coordinate.value / 2))
      (shifted - fourierL2 V - count),
    Lp.coeFn_sub (shifted - fourierL2 V) count, Lp.coeFn_sub shifted (fourierL2 V),
    shiftedRead, burnolZeroOwnedUnitFourier_dirichlet_coeFn observation nontrivial rightHalf, countRead]
      with x smulAt outerAt innerAt shiftedAt fourierAt countAt
  rw [smulAt]
  change (((n : ℂ) + 2) / (coordinate.value / 2)) * (shifted - fourierL2 V - count : BurnolL2) x = _
  rw [outerAt]
  change (((n : ℂ) + 2) / (coordinate.value / 2)) * ((shifted - fourierL2 V : BurnolL2) x - count x) = _
  rw [innerAt]
  change (((n : ℂ) + 2) / (coordinate.value / 2)) * (shifted x - fourierL2 V x - count x) = _
  rw [shiftedAt, fourierAt, countAt]
  unfold burnolPaCombFourierResponseDirichletRaw
  dsimp only [coordinate, burnolDivisionZeroCompletedMellinCoordinate, b]
  ring

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
