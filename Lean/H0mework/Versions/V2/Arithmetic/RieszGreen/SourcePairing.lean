import H0mework.Versions.V2.Arithmetic.RieszSourceKernel.Generated

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSourceGreen

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource

noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

def centeredRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (star coordinate.value - 1 / 2) * burnolRieszFourierForcingRaw coordinate x +
    (star coordinate.value * GapEuler.gapMean q coordinate) *
      (Edge.raw q x - Translator.ForcingMeanZero.edgeMean) +
    (Constructor.secondEulerRaw coordinate x -
      burnolQuarterMeanCoefficient (Constructor.secondEulerAmbient coordinate))

def weightedRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  centeredRaw coordinate x + Kernel.beta coordinate

def weightedState (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterIntervalL2 :=
  (Euler.sourceEuler coordinate : BurnolQuarterIntervalL2) +
    Kernel.beta coordinate • intervalConstant q

theorem weightedState_read (coordinate : BurnolCompletedMellinCoordinate) :
    (weightedState coordinate : ℝ → ℂ) =ᵐ[μq] weightedRaw coordinate := by
  filter_upwards [Lp.coeFn_add (Euler.sourceEuler coordinate : BurnolQuarterIntervalL2)
      (Kernel.beta coordinate • intervalConstant q),
    Lp.coeFn_smul (Kernel.beta coordinate) (intervalConstant q),
    intervalConstant_coeFn q, Euler.sourceEuler_read coordinate] with x added scaled one centered
  simp only [Pi.add_apply] at added
  simp only [Pi.smul_apply, smul_eq_mul] at scaled
  change ((Euler.sourceEuler coordinate : BurnolQuarterIntervalL2) +
    Kernel.beta coordinate • intervalConstant q : BurnolQuarterIntervalL2) x = _
  rw [added, scaled, one, centered]
  simp only [mul_one]
  rfl

theorem weightedState_centered (coordinate : BurnolCompletedMellinCoordinate) :
    Constructor.zeroMean (weightedState coordinate) = Euler.sourceEuler coordinate := by
  unfold weightedState
  simp only [map_add, map_smul, Constructor.zeroMean_constant, smul_zero, add_zero]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _

def sourcePairDensity (left right : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  star (weightedRaw left x) * burnolRieszSingleFourierSourceRaw right x +
    star (burnolRieszSingleFourierSourceRaw left x) * weightedRaw right x

private theorem raw_pair_integrable (left right : BurnolQuarterIntervalL2)
    (leftRaw rightRaw : ℝ → ℂ) (leftRead : (left : ℝ → ℂ) =ᵐ[μq] leftRaw)
    (rightRead : (right : ℝ → ℂ) =ᵐ[μq] rightRaw) :
    Integrable (fun x : ℝ => star (leftRaw x) * rightRaw x) μq := by
  apply (L2.integrable_inner (𝕜 := ℂ) left right).congr
  filter_upwards [leftRead, rightRead] with x hl hr
  rw [hl, hr]
  simp only [RCLike.inner_apply, starRingEnd_apply, mul_comm]

theorem sourcePairDensity_integrable (left right : BurnolCompletedMellinCoordinate) :
    IntegrableOn (sourcePairDensity left right) (symmetricInterval q) :=
  (raw_pair_integrable (weightedState left)
    (burnolRieszSingleFourierSource right : BurnolQuarterIntervalL2) _ _
    (weightedState_read left) (burnolRieszSingleFourierSource_ae_raw right)).add
    (raw_pair_integrable (burnolRieszSingleFourierSource left : BurnolQuarterIntervalL2)
      (weightedState right) _ _ (burnolRieszSingleFourierSource_ae_raw left)
      (weightedState_read right))

theorem sourcePairDensity_intervalIntegrable (left right : BurnolCompletedMellinCoordinate) :
    IntervalIntegrable (sourcePairDensity left right) volume (-q) q := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : -q ≤ q)]
  exact sourcePairDensity_integrable left right

private theorem raw_pair_read (left right : BurnolQuarterIntervalL2)
    (leftRaw rightRaw : ℝ → ℂ) (leftRead : (left : ℝ → ℂ) =ᵐ[μq] leftRaw)
    (rightRead : (right : ℝ → ℂ) =ᵐ[μq] rightRaw) :
    inner ℂ left right = ∫ x : ℝ, star (leftRaw x) * rightRaw x ∂μq := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [leftRead, rightRead] with x hl hr
  rw [hl, hr]
  simp only [RCLike.inner_apply, starRingEnd_apply, mul_comm]

/-- The constants remain in the raw Euler source; the original mean-zero faces remove them here. -/
theorem sourcePairDensity_integral (left right : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ in (-q)..q, sourcePairDensity left right x) =
      inner ℂ (Euler.sourceEuler left) (burnolRieszSingleFourierSource right) +
        inner ℂ (burnolRieszSingleFourierSource left) (Euler.sourceEuler right) := by
  have leftProjection :=
    (burnolQuarterMeanZeroClosedFace.toSubmodule).inner_orthogonalProjectionOnto_eq_of_mem_right
      (burnolRieszSingleFourierSource right) (weightedState left)
  have rightProjection :=
    (burnolQuarterMeanZeroClosedFace.toSubmodule).inner_orthogonalProjectionOnto_eq_of_mem_left
      (burnolRieszSingleFourierSource left) (weightedState right)
  change inner ℂ (Constructor.zeroMean (weightedState left))
    (burnolRieszSingleFourierSource right) = _ at leftProjection
  change inner ℂ (burnolRieszSingleFourierSource left)
    (Constructor.zeroMean (weightedState right)) = _ at rightProjection
  rw [weightedState_centered] at leftProjection rightProjection
  rw [leftProjection, rightProjection,
    raw_pair_read _ _ _ _ (weightedState_read left) (burnolRieszSingleFourierSource_ae_raw right),
    raw_pair_read _ _ _ _ (burnolRieszSingleFourierSource_ae_raw left) (weightedState_read right)]
  rw [intervalIntegral.integral_of_le (by norm_num : -q ≤ q), ← integral_Icc_eq_integral_Ioc]
  exact integral_add
    (raw_pair_integrable _ _ _ _ (weightedState_read left) (burnolRieszSingleFourierSource_ae_raw right))
    (raw_pair_integrable _ _ _ _ (burnolRieszSingleFourierSource_ae_raw left) (weightedState_read right))

end
end OriginalRieszSourceGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
