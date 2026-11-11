import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingDual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.DualSourceGram

open Complex Filter
open scoped Topology InnerProductSpace
noncomputable section

/-- The same complete counting action generates both finite source Grams. -/
theorem finite_gram (N : ℕ) (left right : BurnolL2) :
    inner ℂ (FiniteForcing.source N left) (FiniteForcing.source N right) =
      inner ℂ (DualSource.source N left) (DualSource.source N right) := by
  let action := CountingDual.sourceCLM N
  have commute := (CountingDual.source_dual_commute N N).eq
  calc
    _ = inner ℂ left ((action.adjoint * action) right) := by
      exact (ContinuousLinearMap.adjoint_inner_right action left (action right)).symm
    _ = inner ℂ left ((action * action.adjoint) right) := by rw [← commute]
    _ = inner ℂ (action.adjoint left) (action.adjoint right) :=
      (ContinuousLinearMap.adjoint_inner_left action (action.adjoint right) left).symm
    _ = _ := by rw [← CountingDual.dual_eq_adjoint, ← CountingDual.dual_eq_adjoint]

/-- Both actual ambient limits consume the finite normal source, with their complete common Gram. -/
theorem original_gram (left right : BurnolCompletedMellinCoordinate) :
    inner ℂ (AmbientCounting.value left) (AmbientCounting.value right) =
      inner ℂ (CountingDual.value left) (CountingDual.value right) := by
  have forward := (AmbientCounting.original_ambient_limit left).inner (𝕜 := ℂ)
    (AmbientCounting.original_ambient_limit right)
  have reverse := (CountingDual.original_dual_tendsto left).inner (𝕜 := ℂ)
    (CountingDual.original_dual_tendsto right)
  have same := forward.congr' (Eventually.of_forall (fun N => finite_gram N _ _))
  exact tendsto_nhds_unique same reverse

/-- The original source pairing uses the two independently generated sides of the same action. -/
theorem original_pairing (left right : BurnolCompletedMellinCoordinate) :
    inner ℂ (AmbientCounting.value left) (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource right : BurnolQuarterIntervalL2)) =
    inner ℂ (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource left : BurnolQuarterIntervalL2)) (CountingDual.value right) := by
  have forward := (AmbientCounting.original_ambient_limit left).inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource right : BurnolQuarterIntervalL2)))
  have reverse := (tendsto_const_nhds (x := burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource left : BurnolQuarterIntervalL2))).inner (𝕜 := ℂ)
    (CountingDual.original_dual_tendsto right)
  have same := forward.congr' (Eventually.of_forall (fun N => CountingDual.source_pairing N _ _))
  exact tendsto_nhds_unique same reverse

end
end OriginalRieszFinitePairing.CoPoisson.Ward.DualSourceGram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
