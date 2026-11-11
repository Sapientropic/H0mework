import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.PrimeThree.Gram.Physical
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.PrimeThree.Physical.Finite

/-! Every physical cutoff computes the same original projected residual against its full finite prime residue. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def primeThreeGramCount (N : ℕ) : ℕ := ⌈4 * (((N : ℝ) + 1) / Real.sqrt 3)⌉₊

theorem primeThreeGramCount_original_covers (N : ℕ) :
    4 * ((N : ℝ) + 1) ≤ (3 * primeThreeGramCount N : ℕ) := by
  have positive : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have aboveOne : 1 ≤ Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
  calc
    4 * ((N : ℝ) + 1) ≤ 4 * (Real.sqrt 3 * ((N : ℝ) + 1)) := by nlinarith
    _ ≤ _ := prime_three_source_window_cover ((N : ℝ) + 1) (primeThreeGramCount N) (Nat.le_ceil _)

def originalPrimeThreeSourceGram {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (N : ℕ) : ℂ :=
  let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
  let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
  let sigma := burnolMobiusSourceL2 p
  let mean := burnolConstantGapCoefficient burnolUnscaledCommonGapRadius p
  let K := primeThreeGramCount N
  ∫ x : ℝ in symmetricInterval ((N : ℝ) + 1),
    star (burnolPaCombPairedDirichletRaw observation.coordinate 0 x -
      (finiteSourceCoSum sigma (3 * K) x + mean)) *
      ((Real.sqrt 3 : ℂ) * finitePrimeThreeSourceCoSum sigma K x +
        ((Real.sqrt 3 : ℂ) - (Real.sqrt 3 : ℂ)⁻¹) * mean)

/-- The two finite inventories, source mean and original B₀ forcing are generated at the same cutoff. -/
theorem originalPrimeThreeSourceGram_eq_physical {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (N : ℕ) :
    originalPrimeThreeSourceGram observation nontrivial rightHalf N =
      originalPrimeThreeResidualGram observation nontrivial rightHalf N := by
  let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
  let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
  have originalPa : p ∈ burnolCompactCoPoissonClosedRange := Submodule.starProjection_apply_mem _ _
  rw [originalPrimeThreeResidualGram_integral]
  unfold originalPrimeThreeSourceGram
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (burnolPaCombPairedPhysicalResponse_coeFn observation nontrivial rightHalf 0),
    original_pa_finite_source_window p originalPa ((N : ℝ) + 1) (3 * primeThreeGramCount N)
      (primeThreeGramCount_original_covers N),
    primeThreePhysicalResidue_finite_window p originalPa ((N : ℝ) + 1) (primeThreeGramCount N)
      (Nat.le_ceil _)] with x BRead pRead residueRead
  change star (burnolPaCombPairedDirichletRaw observation.coordinate 0 x - _) * _ =
    star ((B : BurnolL2) x - (p : BurnolL2) x) * primeThreePhysicalResidue (p : BurnolL2) x
  rw [BRead, pRead, residueRead]

theorem originalPrimeThreeSourceGram_tendsto {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
    let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
    let Z := burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf
    let c : ℂ := (Real.sqrt (Real.sqrt 3) : ℝ)
    Tendsto (originalPrimeThreeSourceGram observation nontrivial rightHalf) atTop
      (𝓝 (star (burnolPaCombResponseCoefficient observation.coordinate 0) * (c - c⁻¹) *
        inner ℂ (Z : BurnolPaAmbientCarrier)
          (burnolPairedAmbientCompression (Real.log (Real.sqrt 3)) p))) :=
  (originalPrimeThreeResidualGram_tendsto observation nontrivial rightHalf).congr
    (fun N => (originalPrimeThreeSourceGram_eq_physical observation nontrivial rightHalf N).symm)

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
