import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.PrimeThree.Gram.Source

/-! The finite divisor inventories act in the original L² space; the constant cell stays in their Gram. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def finiteSourceAction (source : BurnolL2) (K : ℕ) : BurnolL2 :=
  ∑ n ∈ Finset.range K, burnolSourceScalePrimitive source (1 / ((n + 1 : ℕ) : ℝ))

def finitePrimeThreeSourceAction (source : BurnolL2) (K : ℕ) : BurnolL2 :=
  ∑ n ∈ Finset.range K,
    (burnolSourceScalePrimitive source (Real.sqrt 3 / ((3 * n + 1 : ℕ) : ℝ)) +
      burnolSourceScalePrimitive source (Real.sqrt 3 / ((3 * n + 2 : ℕ) : ℝ)))

def physicalMeanCell (X : ℝ) : BurnolL2 :=
  indicatorConstLp 2 (measurableSet_symmetricInterval X) measure_Icc_lt_top.ne (1 : ℂ)

theorem physicalMeanCell_coeFn (X : ℝ) :
    (physicalMeanCell X : ℝ → ℂ) =ᵐ[volume]
      (symmetricInterval X).indicator (fun _ => (1 : ℂ)) := indicatorConstLp_coeFn

theorem finiteSourceAction_coeFn (source : BurnolL2) (K : ℕ) :
    (finiteSourceAction source K : ℝ → ℂ) =ᵐ[volume] finiteSourceCoSum source K := by
  have terms (n : ℕ) := burnolSourceScalePrimitive_coeFn source source (Filter.EventuallyEq.refl _ _)
    (1 / ((n + 1 : ℕ) : ℝ)) (by positivity)
  filter_upwards [Lp.coeFn_finsetSum (Finset.range K)
    (fun n => burnolSourceScalePrimitive source (1 / ((n + 1 : ℕ) : ℝ))),
    ae_all_iff.mpr terms] with x sumRead termRead
  rw [finiteSourceAction, sumRead]
  simp only [Finset.sum_apply]
  unfold finiteSourceCoSum
  apply Finset.sum_congr rfl
  intro n _
  rw [termRead n]
  simp only [one_div, inv_mul_eq_div]
  push_cast
  ring

theorem finitePrimeThreeSourceAction_coeFn (source : BurnolL2) (K : ℕ) :
    (finitePrimeThreeSourceAction source K : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.sqrt 3 : ℂ) * finitePrimeThreeSourceCoSum source K x := by
  have first (n : ℕ) := burnolSourceScalePrimitive_coeFn source source (Filter.EventuallyEq.refl _ _)
    (Real.sqrt 3 / ((3 * n + 1 : ℕ) : ℝ)) (by positivity)
  have second (n : ℕ) := burnolSourceScalePrimitive_coeFn source source (Filter.EventuallyEq.refl _ _)
    (Real.sqrt 3 / ((3 * n + 2 : ℕ) : ℝ)) (by positivity)
  have adds (n : ℕ) := Lp.coeFn_add
    (burnolSourceScalePrimitive source (Real.sqrt 3 / ((3 * n + 1 : ℕ) : ℝ)))
    (burnolSourceScalePrimitive source (Real.sqrt 3 / ((3 * n + 2 : ℕ) : ℝ)))
  filter_upwards [Lp.coeFn_finsetSum (Finset.range K) (fun n =>
    burnolSourceScalePrimitive source (Real.sqrt 3 / ((3 * n + 1 : ℕ) : ℝ)) +
      burnolSourceScalePrimitive source (Real.sqrt 3 / ((3 * n + 2 : ℕ) : ℝ))),
    ae_all_iff.mpr adds, ae_all_iff.mpr first, ae_all_iff.mpr second]
    with x sumRead addRead firstRead secondRead
  rw [finitePrimeThreeSourceAction, sumRead]
  simp only [Finset.sum_apply]
  unfold finitePrimeThreeSourceCoSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [addRead n]
  simp only [Pi.add_apply]
  rw [firstRead n, secondRead n]
  simp only [Complex.ofReal_div, div_mul_eq_mul_div]
  push_cast
  ring

theorem original_pa_finite_source_action (p : BurnolPaAmbientCarrier)
    (inside : p ∈ burnolCompactCoPoissonClosedRange) (X : ℝ) (K : ℕ) (covers : 4 * X ≤ K) :
    originalPhysicalCutoff X (p : BurnolL2) =
      originalPhysicalCutoff X (finiteSourceAction (burnolMobiusSourceL2 p) K) +
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius p • physicalMeanCell X := by
  have raw := (ae_restrict_iff' (measurableSet_symmetricInterval X)).mp
    (original_pa_finite_source_window p inside X K covers)
  apply Lp.ext
  filter_upwards [originalPhysicalCutoff_coeFn X (p : BurnolL2),
    originalPhysicalCutoff_coeFn X (finiteSourceAction (burnolMobiusSourceL2 p) K),
    finiteSourceAction_coeFn (burnolMobiusSourceL2 p) K, physicalMeanCell_coeFn X,
    Lp.coeFn_add (originalPhysicalCutoff X (finiteSourceAction (burnolMobiusSourceL2 p) K))
      (burnolConstantGapCoefficient burnolUnscaledCommonGapRadius p • physicalMeanCell X),
    Lp.coeFn_smul (burnolConstantGapCoefficient burnolUnscaledCommonGapRadius p) (physicalMeanCell X),
    raw] with x pCut sourceCut sourceRead meanRead addRead smulRead pRead
  rw [addRead, pCut]
  change _ = originalPhysicalCutoff X (finiteSourceAction (burnolMobiusSourceL2 p) K) x +
    (burnolConstantGapCoefficient burnolUnscaledCommonGapRadius p • physicalMeanCell X : BurnolL2) x
  rw [sourceCut, smulRead]
  change _ = _ + _ * physicalMeanCell X x
  rw [meanRead]
  by_cases window : x ∈ symmetricInterval X
  · simp only [Set.indicator_of_mem window, sourceRead, mul_one]
    exact pRead window
  · simp only [Set.indicator_of_notMem window, mul_zero, add_zero]

theorem primeThree_finite_source_action (p : BurnolPaAmbientCarrier)
    (inside : p ∈ burnolCompactCoPoissonClosedRange) (X : ℝ) (K : ℕ)
    (covers : 4 * (X / Real.sqrt 3) ≤ K) :
    originalPhysicalCutoff X (primeThreePhysicalResidue (p : BurnolL2)) =
      originalPhysicalCutoff X (finitePrimeThreeSourceAction (burnolMobiusSourceL2 p) K) +
        (((Real.sqrt 3 : ℂ) - (Real.sqrt 3 : ℂ)⁻¹) *
          burnolConstantGapCoefficient burnolUnscaledCommonGapRadius p) • physicalMeanCell X := by
  have raw := (ae_restrict_iff' (measurableSet_symmetricInterval X)).mp
    (primeThreePhysicalResidue_finite_window p inside X K covers)
  apply Lp.ext
  filter_upwards [originalPhysicalCutoff_coeFn X (primeThreePhysicalResidue (p : BurnolL2)),
    originalPhysicalCutoff_coeFn X (finitePrimeThreeSourceAction (burnolMobiusSourceL2 p) K),
    finitePrimeThreeSourceAction_coeFn (burnolMobiusSourceL2 p) K, physicalMeanCell_coeFn X,
    Lp.coeFn_add (originalPhysicalCutoff X (finitePrimeThreeSourceAction (burnolMobiusSourceL2 p) K))
      ((((Real.sqrt 3 : ℂ) - (Real.sqrt 3 : ℂ)⁻¹) *
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius p) • physicalMeanCell X),
    Lp.coeFn_smul (((Real.sqrt 3 : ℂ) - (Real.sqrt 3 : ℂ)⁻¹) *
      burnolConstantGapCoefficient burnolUnscaledCommonGapRadius p) (physicalMeanCell X),
    raw] with x pCut sourceCut sourceRead meanRead addRead smulRead pRead
  rw [addRead, pCut]
  change _ = originalPhysicalCutoff X (finitePrimeThreeSourceAction (burnolMobiusSourceL2 p) K) x +
    (_ • physicalMeanCell X : BurnolL2) x
  rw [sourceCut, smulRead]
  change _ = _ + _ * physicalMeanCell X x
  rw [meanRead]
  by_cases window : x ∈ symmetricInterval X
  · simp only [Set.indicator_of_mem window, sourceRead, mul_one]
    exact pRead window
  · simp only [Set.indicator_of_notMem window, mul_zero, add_zero]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
