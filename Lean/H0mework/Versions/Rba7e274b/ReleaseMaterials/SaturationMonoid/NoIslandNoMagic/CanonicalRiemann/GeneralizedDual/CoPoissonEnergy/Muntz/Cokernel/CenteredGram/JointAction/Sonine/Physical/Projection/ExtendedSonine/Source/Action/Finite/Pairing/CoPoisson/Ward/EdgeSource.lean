import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.EdgeSource

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace SchwartzMap
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)

/-- The original sawtooth source pays the entire contact, including its exterior tail. -/
theorem programme_limit (test : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ => DualEuler.edgeProgramme N test) atTop
      (𝓝 (-GapEuler.euler (ConstantDual.value : TemperedDistribution ℝ ℂ) test -
        (1 / 2 : ℂ) * (ConstantDual.value : TemperedDistribution ℝ ℂ) test)) := by
  have source := ((ConstantDual.edgeRead test).continuous.tendsto ConstantDual.value).comp
    ConstantDual.original_tendsto
  exact source.congr' (Eventually.of_forall (fun N => (ConstantDual.finite_edge N test).symm))

/-- The integer comb and its accumulating origin value are jointly computed. -/
theorem integer_comb_limit (test : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ico 1 N, DualEuler.edgeChannel (n : ℝ) test) atTop
      (𝓝 (-GapEuler.euler (ConstantDual.value : TemperedDistribution ℝ ℂ) test -
        (1 / 2 : ℂ) * (ConstantDual.value : TemperedDistribution ℝ ℂ) test -
        (2 * (q : ℂ)) * test 0)) := by
  have source := (programme_limit test).add (DualEuler.edgeChannel_continuous_limit test)
  simpa only [DualEuler.edgeProgramme, sub_add_cancel, ← sub_eq_add_neg, neg_mul] using source

/-- The original inverse Euler consumer now has a computed complete contact.
The two response terms retain their original joint finite source. -/
theorem original_response_limit (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ =>
      Kernel.A coordinate * (DualSource.source N (burnolQuarterZeroExtension
        (Response.u : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test -
      Kernel.beta coordinate * (DualSource.source N (burnolQuarterZeroExtension
        (Response.v : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test) atTop
      (𝓝 (GapEuler.euler (CountingDual.value coordinate : TemperedDistribution ℝ ℂ) test -
        (star coordinate.value - 1 / 2) * (CountingDual.value coordinate : TemperedDistribution ℝ ℂ) test -
        Kernel.beta coordinate * (GapEuler.euler (ConstantDual.value : TemperedDistribution ℝ ℂ) test +
          (1 / 2 : ℂ) * (ConstantDual.value : TemperedDistribution ℝ ℂ) test))) := by
  have source := (DualEuler.original_weak_limit coordinate test).add
    ((integer_comb_limit test).const_mul (Kernel.beta coordinate))
  simp only [sub_add_cancel] at source
  convert source using 1
  congr 1
  ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward.EdgeSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
