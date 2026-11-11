import H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.Window

import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.PrimeThree.Source.Recovery

/-! The source gap generates the full finite divisor inventory on each actual physical window. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def finiteSourceCoSum (source : ℝ → ℂ) (K : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range K, (((n + 1 : ℕ) : ℂ)⁻¹) * source (x / ((n + 1 : ℕ) : ℝ))

theorem source_gap_forward_finite_window (source : ℝ → ℂ)
    (gap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → source x = 0)
    (X : ℝ) (K : ℕ) (covers : 4 * X ≤ K) (x : ℝ) (window : |x| ≤ X) :
    burnolInnerGapForward source x = finiteSourceCoSum source K x := by
  have reindex : burnolInnerGapForward source x =
      ∑' n : ℕ, (((n + 1 : ℕ) : ℂ)⁻¹) * source (x / ((n + 1 : ℕ) : ℝ)) :=
    (Equiv.tsum_eq (Equiv.pnatEquivNat.symm)
      (fun n : ℕ+ => (((n : ℕ) : ℂ)⁻¹) * source (x / (n : ℕ)))).symm
  rw [reindex]
  apply tsum_eq_sum
  intro n outside
  have beyond : K ≤ n := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using outside)
  have positive : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have order : 4 * X ≤ (n + 1 : ℕ) := by
    exact covers.trans (by exact_mod_cast (show K ≤ n + 1 by omega))
  have vanishes : source (x / ((n + 1 : ℕ) : ℝ)) = 0 := by
    apply gap
    rw [abs_div, abs_of_pos positive]
    apply (div_le_iff₀ positive).mpr
    nlinarith
  rw [vanishes, mul_zero]

theorem finiteSourceCoSum_ae_congr (left right : ℝ → ℂ) (same : left =ᵐ[volume] right) (K : ℕ) :
    finiteSourceCoSum left K =ᵐ[volume] finiteSourceCoSum right K := by
  have reads (n : ℕ) : ∀ᵐ x : ℝ ∂volume,
      left (x / ((n + 1 : ℕ) : ℝ)) = right (x / ((n + 1 : ℕ) : ℝ)) := by
    have qmp := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
      (r := (((n + 1 : ℕ) : ℝ))⁻¹) (by positivity)
    simpa only [smul_eq_mul, inv_mul_eq_div] using qmp.ae same
  filter_upwards [ae_all_iff.mpr reads] with x read
  unfold finiteSourceCoSum
  exact Finset.sum_congr rfl (fun n _ => by rw [read n])

/-- The finite inventory is read from the actual ν(p), including its original physical mean. -/
theorem original_pa_finite_source_window
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange)
    (X : ℝ) (K : ℕ) (covers : 4 * X ≤ K) :
    (p : BurnolL2) =ᵐ[volume.restrict (symmetricInterval X)] fun x =>
      finiteSourceCoSum (burnolMobiusSourceL2 p) K x +
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius p := by
  obtain ⟨raw, same, gap, actual⟩ :=
    primeThreePa_source_representative p inside
  filter_upwards [ae_restrict_of_ae actual, ae_restrict_of_ae (finiteSourceCoSum_ae_congr _ _ same K),
    ae_restrict_mem (measurableSet_symmetricInterval X)] with x actualRead finiteRead window
  rw [actualRead, source_gap_forward_finite_window raw gap X K covers x (abs_le.mpr window),
    ← finiteRead]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
