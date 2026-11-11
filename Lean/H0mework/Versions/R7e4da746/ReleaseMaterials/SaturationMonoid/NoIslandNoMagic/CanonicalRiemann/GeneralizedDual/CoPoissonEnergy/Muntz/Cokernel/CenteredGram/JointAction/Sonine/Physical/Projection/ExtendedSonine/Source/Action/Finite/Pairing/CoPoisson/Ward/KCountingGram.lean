import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.KCounting
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSourceGram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.KCountingGram

open Complex Filter
open scoped Topology InnerProductSpace
noncomputable section

local notation "K" => burnolCompletedMellinRieszVector

/-- The original K has a forward limit because its complete reverse source is strongly Cauchy. -/
theorem forward_cauchy (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    CauchySeq (fun N : ℕ => FiniteForcing.source N (K coordinate : BurnolL2)) := by
  have actual := (KCounting.original_tendsto coordinate zero).cauchySeq
  rw [Metric.cauchySeq_iff] at actual ⊢
  intro epsilon positive
  obtain ⟨N, after⟩ := actual epsilon positive
  refine ⟨N, ?_⟩
  intro m hm n hn
  simpa only [dist_eq_norm, CountingDual.difference_norm] using after m hm n hn

def value (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  limUnder atTop (fun N : ℕ => FiniteForcing.source N (K coordinate : BurnolL2))

theorem forward_tendsto (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    Tendsto (fun N : ℕ => FiniteForcing.source N (K coordinate : BurnolL2)) atTop
      (𝓝 (value coordinate)) :=
  (forward_cauchy coordinate zero).tendsto_limUnder

/-- The original two K sources consume actual finite normality before either limit is read. -/
theorem original_gram (left right : BurnolCompletedMellinCoordinate)
    (leftZero : riemannZeta left.value = 0) (rightZero : riemannZeta right.value = 0) :
    inner ℂ (value left) (value right) =
      inner ℂ (-PositionCounting.value left leftZero - burnolTateReciprocalL2 (CountingDual.value left))
        (-PositionCounting.value right rightZero - burnolTateReciprocalL2 (CountingDual.value right)) := by
  have forward := (forward_tendsto left leftZero).inner (𝕜 := ℂ) (forward_tendsto right rightZero)
  have reverse := (KCounting.original_tendsto left leftZero).inner (𝕜 := ℂ)
    (KCounting.original_tendsto right rightZero)
  have same := forward.congr' (Eventually.of_forall (fun N => DualSourceGram.finite_gram N _ _))
  exact tendsto_nhds_unique same reverse

/-- Complete counting adjointness now reads directly on the original Riesz pair. -/
theorem original_pairing (left right : BurnolCompletedMellinCoordinate)
    (leftZero : riemannZeta left.value = 0) (rightZero : riemannZeta right.value = 0) :
    inner ℂ (value left) (K right : BurnolL2) =
      inner ℂ (K left : BurnolL2)
        (-PositionCounting.value right rightZero - burnolTateReciprocalL2 (CountingDual.value right)) := by
  have forward := (forward_tendsto left leftZero).inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := (K right : BurnolL2)))
  have reverse := (tendsto_const_nhds (x := (K left : BurnolL2))).inner (𝕜 := ℂ)
    (KCounting.original_tendsto right rightZero)
  have same := forward.congr' (Eventually.of_forall (fun N => CountingDual.source_pairing N _ _))
  exact tendsto_nhds_unique same reverse

theorem fourier_source_gram (left right : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta left.value = 0) :
    inner ℂ (value left) (AmbientCounting.value right) =
      inner ℂ (-PositionCounting.value left zero - burnolTateReciprocalL2 (CountingDual.value left))
        (CountingDual.value right) := by
  have forward := (forward_tendsto left zero).inner (𝕜 := ℂ) (AmbientCounting.original_ambient_limit right)
  have reverse := (KCounting.original_tendsto left zero).inner (𝕜 := ℂ) (CountingDual.original_dual_tendsto right)
  have same := forward.congr' (Eventually.of_forall (fun N => DualSourceGram.finite_gram N _ _))
  exact tendsto_nhds_unique same reverse

theorem fourier_source_pairing (left right : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta left.value = 0) :
    inner ℂ (value left) (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource right : BurnolQuarterIntervalL2)) =
      inner ℂ (K left : BurnolL2) (CountingDual.value right) := by
  have forward := (forward_tendsto left zero).inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource right : BurnolQuarterIntervalL2)))
  have reverse := (tendsto_const_nhds (x := (K left : BurnolL2))).inner (𝕜 := ℂ)
    (CountingDual.original_dual_tendsto right)
  have same := forward.congr' (Eventually.of_forall (fun N => CountingDual.source_pairing N _ _))
  exact tendsto_nhds_unique same reverse

/-- The actual nonzero constant source is retained in the original K adjoint reading. -/
theorem constant_pairing (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    inner ℂ (value coordinate) ConstantDual.seed =
      inner ℂ (K coordinate : BurnolL2) ConstantDual.value := by
  have forward := (forward_tendsto coordinate zero).inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := ConstantDual.seed))
  have reverse := (tendsto_const_nhds (x := (K coordinate : BurnolL2))).inner (𝕜 := ℂ)
    ConstantDual.original_tendsto
  have same := forward.congr' (Eventually.of_forall (fun N => CountingDual.source_pairing N _ _))
  exact tendsto_nhds_unique same reverse

end
end OriginalRieszFinitePairing.CoPoisson.Ward.KCountingGram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
