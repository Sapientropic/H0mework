import H0mework.Versions.Y.Arithmetic.RiemannUnitFourier.Difference

/-! The same zero's original physical gap eliminates the dyadic homogeneous component on the whole real line. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private theorem dirichlet_inner (s : ℂ) (x : ℝ) (inside : |x| ≤ 1) :
    burnolUnitTailDirichletRaw s 1 x = 1 / s := by
  have bound : ⌈|x|⌉₊ ≤ 1 := Nat.ceil_le.mpr (by exact_mod_cast inside)
  have empty : Finset.Ico 1 ⌈|x|⌉₊ = ∅ := Finset.Ico_eq_empty_of_le bound
  simp only [burnolUnitTailDirichletRaw, Complex.ofReal_one, Complex.one_cpow,
    burnolUnitTailDirichletChannels, div_one, empty, Finset.sum_empty, mul_zero, sub_zero]

private theorem dyadic_gap_elimination (d : ℝ → ℂ) (beta c : ℂ) (nonzero : beta ≠ 0)
    (nonunit : beta ≠ 1)
    (step : ∀ᵐ x : ℝ ∂volume, d x = beta * d (2 * x))
    (gap : d =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => c) :
    d =ᵐ[volume] fun _ => 0 := by
  have qmp := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (r := (1 / 2 : ℝ)) (by norm_num)
  have wholeGap : ∀ᵐ x : ℝ ∂volume, |x| ≤ (1 / 4 : ℝ) → d x = c := by
    have read := (ae_restrict_iff' (measurableSet_symmetricInterval (1 / 4 : ℝ))).mp gap
    filter_upwards [read] with x hx inside
    exact hx (abs_le.mp inside)
  have halfGap : ∀ᵐ x : ℝ ∂volume, |x / 2| ≤ (1 / 4 : ℝ) → d (x / 2) = c := by
    simpa only [smul_eq_mul, one_div, inv_mul_eq_div] using qmp.ae wholeGap
  have halfStep : ∀ᵐ x : ℝ ∂volume, d (x / 2) = beta * d x := by
    filter_upwards [qmp.ae step] with x hx
    norm_num [smul_eq_mul, ← mul_assoc] at hx
    simpa only [one_div, inv_mul_eq_div] using hx
  have constantLaw : c = beta * c := by
    by_contra failed
    have impossible : ∀ᵐ x : ℝ ∂volume.restrict (symmetricInterval (1 / 4 : ℝ)), False := by
      filter_upwards [ae_restrict_of_ae wholeGap, ae_restrict_of_ae halfGap,
        ae_restrict_of_ae halfStep,
        ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))]
        with x wholeAt halfAt stepAt inside
      have bound := abs_le.mpr inside
      have halfBound : |x / 2| ≤ (1 / 4 : ℝ) := by rw [abs_div]; norm_num; linarith [abs_nonneg x]
      rw [wholeAt bound, halfAt halfBound] at stepAt
      exact failed stepAt
    have measureZero : (volume.restrict (symmetricInterval (1 / 4 : ℝ))) univ = 0 := by
      simpa only [ae_iff, not_false_eq_true, ofPred_true] using impossible
    norm_num [symmetricInterval] at measureZero
  have cZero : c = 0 := by
    have product : (beta - 1) * c = 0 := by linear_combination -constantLaw
    exact (mul_eq_zero.mp product).resolve_left (sub_ne_zero.mpr nonunit)
  have iterate (n : ℕ) : ∀ᵐ x : ℝ ∂volume, |x| ≤ (2 : ℝ) ^ n / 4 → d x = 0 := by
    induction n with
    | zero => simpa only [pow_zero, cZero] using wholeGap
    | succ n ih =>
        have pulled : ∀ᵐ x : ℝ ∂volume, |x / 2| ≤ (2 : ℝ) ^ n / 4 → d (x / 2) = 0 := by
          simpa only [smul_eq_mul, one_div, inv_mul_eq_div] using qmp.ae ih
        filter_upwards [pulled, halfStep] with x hx stepAt bound
        have smaller : |x / 2| ≤ (2 : ℝ) ^ n / 4 := by
          rw [abs_div]
          norm_num only [abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
          rw [pow_succ] at bound
          linarith
        rw [hx smaller] at stepAt
        exact (mul_eq_zero.mp stepAt.symm).resolve_left nonzero
  filter_upwards [ae_all_iff.mpr iterate] with x every
  obtain ⟨n, bound⟩ := pow_unbounded_of_one_lt (4 * |x|) (by norm_num : (1 : ℝ) < 2)
  exact every n (by linarith)

private theorem dyadicCoefficient_ne_one (coordinate : BurnolCompletedMellinCoordinate) :
    (2 : ℂ) ^ (1 - coordinate.value) ≠ 1 := by
  intro same
  rw [Complex.cpow_def_of_ne_zero (by norm_num),
    show Complex.log (2 : ℂ) = (Real.log 2 : ℂ) from
      (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm] at same
  have magnitude := congrArg norm same
  rw [Complex.norm_exp, norm_one] at magnitude
  have positive : 0 < ((Real.log 2 : ℂ) * (1 - coordinate.value)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.sub_re, Complex.one_re]
    exact mul_pos (Real.log_pos (by norm_num)) (sub_pos.mpr coordinate.belowOne)
  have larger := Real.one_lt_exp_iff.mpr positive
  linarith

theorem burnolZeroOwnedUnitFourier_dirichlet_coeFn {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    (fourierL2 (burnolUnitTailResponse
      (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) 1) : ℝ → ℂ) =ᵐ[volume]
      fun x => -burnolUnitTailDirichletRaw (1 - observation.coordinate) 1 x := by
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  let value := fourierL2 (burnolUnitTailResponse coordinate 1)
  let d : ℝ → ℂ := fun x => value x + burnolUnitTailDirichletRaw (1 - coordinate.value) 1 x
  let physical := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
    (burnolZeroOwnedUnitOneState observation nontrivial rightHalf)
  let c := burnolConstantGapCoefficient burnolUnscaledCommonGapRadius physical + 1 / (1 - coordinate.value)
  have gap : d =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => c := by
    have actual := burnolAmbientGap_ae physical
    change (value : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))]
      fun _ => burnolConstantGapCoefficient burnolUnscaledCommonGapRadius physical at actual
    filter_upwards [actual, ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))]
      with x read inside
    change value x + burnolUnitTailDirichletRaw (1 - coordinate.value) 1 x = c
    rw [read, dirichlet_inner _ x (by linarith [abs_le.mpr inside])]
  have killed := dyadic_gap_elimination d ((2 : ℂ) ^ (1 - coordinate.value)) c
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))) (dyadicCoefficient_ne_one coordinate)
    (burnolUnitFourierComplement_dyadic coordinate) gap
  filter_upwards [killed] with x zeroAt
  exact eq_neg_iff_add_eq_zero.mpr zeroAt

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
