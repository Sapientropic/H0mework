import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.PrimeThree.Source.Finite

/-! Exact finite divisor incidence: deleting multiples of three retains both nonzero residues. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def finitePrimeThreeSourceCoSum (source : ℝ → ℂ) (K : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range K,
    ((((3 * n + 1 : ℕ) : ℂ)⁻¹) * source (Real.sqrt 3 * x / ((3 * n + 1 : ℕ) : ℝ)) +
      (((3 * n + 2 : ℕ) : ℂ)⁻¹) * source (Real.sqrt 3 * x / ((3 * n + 2 : ℕ) : ℝ)))

private theorem finiteSourceCoSum_succ (source : ℝ → ℂ) (K : ℕ) (x : ℝ) :
    finiteSourceCoSum source (K + 1) x = finiteSourceCoSum source K x +
      (((K + 1 : ℕ) : ℂ)⁻¹) * source (x / ((K + 1 : ℕ) : ℝ)) := by
  exact Finset.sum_range_succ _ _

theorem finiteSourceCoSum_prime_three (source : ℝ → ℂ) (K : ℕ) (x : ℝ) :
    (Real.sqrt 3 : ℂ) * finiteSourceCoSum source (3 * K) (Real.sqrt 3 * x) -
      (Real.sqrt 3 : ℂ)⁻¹ * finiteSourceCoSum source K (x / Real.sqrt 3) =
        (Real.sqrt 3 : ℂ) * finitePrimeThreeSourceCoSum source K x := by
  have rootPositive : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have rootNe : Real.sqrt 3 ≠ 0 := ne_of_gt rootPositive
  have rootSq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have complexRootNe : (Real.sqrt 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr rootNe
  have complexRootSq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by exact_mod_cast rootSq
  induction K with
  | zero => simp [finiteSourceCoSum, finitePrimeThreeSourceCoSum]
  | succ K ih =>
    have count : 3 * (K + 1) = ((3 * K + 1) + 1) + 1 := by omega
    rw [count, finiteSourceCoSum_succ, finiteSourceCoSum_succ, finiteSourceCoSum_succ,
      finiteSourceCoSum_succ]
    have realDenom : (((3 * K + 1) + 1 + 1 : ℕ) : ℝ) = 3 * ((K + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    have complexDenom : (((3 * K + 1) + 1 + 1 : ℕ) : ℂ) = 3 * ((K + 1 : ℕ) : ℂ) := by
      push_cast
      ring
    have samePoint : Real.sqrt 3 * x / (((3 * K + 1) + 1 + 1 : ℕ) : ℝ) =
        (x / Real.sqrt 3) / ((K + 1 : ℕ) : ℝ) := by
      rw [realDenom]
      have denomNe : ((K + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      rw [rootSq]
      ring
    have sameWeight : (Real.sqrt 3 : ℂ) *
        ((((3 * K + 1) + 1 + 1 : ℕ) : ℂ)⁻¹) =
          (Real.sqrt 3 : ℂ)⁻¹ * (((K + 1 : ℕ) : ℂ)⁻¹) := by
      rw [complexDenom]
      have denomNe : ((K + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero K
      field_simp
      exact complexRootSq
    simp only [finitePrimeThreeSourceCoSum, Finset.sum_range_succ] at ih ⊢
    rw [samePoint]
    have lastCancels := congrArg (fun c : ℂ => c * source
      ((x / Real.sqrt 3) / ((K + 1 : ℕ) : ℝ))) sameWeight
    norm_num only [show 3 * K + 1 + 1 = 3 * K + 2 by omega] at ⊢
    linear_combination ih + lastCancels

theorem finitePrimeThreeSourceCoSum_ae_congr (left right : ℝ → ℂ)
    (same : left =ᵐ[volume] right) (K : ℕ) :
    finitePrimeThreeSourceCoSum left K =ᵐ[volume] finitePrimeThreeSourceCoSum right K := by
  have reads (m : ℕ) (positive : 0 < m) : ∀ᵐ x : ℝ ∂volume,
      left (Real.sqrt 3 * x / (m : ℝ)) = right (Real.sqrt 3 * x / (m : ℝ)) := by
    have scalarNe : Real.sqrt 3 / (m : ℝ) ≠ 0 := by positivity
    have qmp := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
      (r := Real.sqrt 3 / (m : ℝ)) scalarNe
    simpa only [smul_eq_mul, div_mul_eq_mul_div] using qmp.ae same
  have first (n : ℕ) := reads (3 * n + 1) (by omega)
  have second (n : ℕ) := reads (3 * n + 2) (by omega)
  filter_upwards [ae_all_iff.mpr first, ae_all_iff.mpr second] with x firstRead secondRead
  unfold finitePrimeThreeSourceCoSum
  exact Finset.sum_congr rfl (fun n _ => by rw [firstRead n, secondRead n])

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
