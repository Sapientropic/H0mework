import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.GaussianWindow.Gaussiansource

set_option autoImplicit false

namespace P23.GaussianWindow.Consumer

open scoped BigOperators
noncomputable section

/-! These consumers share the raw kernel. They accept legal NoClick effects,
not supplied photon-count laws, Born probabilities, tail or Wick certificates. -/

theorem source_count_contract (s : RawKernel) :
    (∀ h v, 0 ≤ numberMass s h v) ∧
      (∑' hv : ℕ × ℕ, numberMass s hv.1 hv.2) = 1 ∧
      (∑' hv : ℕ × ℕ, Complex.normSq (amplitude s hv.1 hv.2)) = 1 ∧
      (∑' n : ℕ, sectorMass s n) = 1 :=
  ⟨numberMass_nonneg s, (numberMass_hasSum s).tsum_eq,
    amplitude_normalized s, sectorMass_tsum s⟩

theorem source_pgf_contract (s : RawKernel) {zH zV : ℝ}
    (hH0 : 0 ≤ zH) (hV0 : 0 ≤ zV) (hH1 : s.tH * zH < 1)
    (hV1 : s.tV * zV < 1) :
    countPGF s zH zV =
      (1 - s.tH) * (1 - s.tV) / ((1 - s.tH * zH) * (1 - s.tV * zV)) := by
  rw [countPGF_eq s hH0 hV0 hH1 hV1]
  exact div_mul_div_comm _ _ _ _

theorem source_orders_zero_to_three (s : RawKernel) :
    mixedFactorialMoment s 0 0 = 1 ∧
      mixedFactorialMoment s 1 0 = meanNumber s.tH ∧
      mixedFactorialMoment s 0 1 = meanNumber s.tV ∧
      mixedFactorialMoment s 2 0 = 2 * meanNumber s.tH ^ 2 ∧
      mixedFactorialMoment s 0 2 = 2 * meanNumber s.tV ^ 2 ∧
      mixedFactorialMoment s 1 1 = meanNumber s.tH * meanNumber s.tV ∧
      mixedFactorialMoment s 3 0 = 6 * meanNumber s.tH ^ 3 ∧
      mixedFactorialMoment s 0 3 = 6 * meanNumber s.tV ^ 3 ∧
      mixedFactorialMoment s 2 1 = 2 * meanNumber s.tH ^ 2 * meanNumber s.tV ∧
      mixedFactorialMoment s 1 2 = 2 * meanNumber s.tH * meanNumber s.tV ^ 2 := by
  simp only [mixedFactorialMoment_eq]
  norm_num [Nat.factorial]
  ring

theorem cutoff_six_contract (s : RawKernel) (e : NumberConservingEffect) :
    sourcePrefix s 6 + sourceTail s 6 = 1 ∧
      sourceTail s 6 = 1 - (1 - s.tH) * (1 - s.tV) *
        ∑ n ∈ Finset.range 7,
          ∑ h ∈ Finset.range (n + 1), s.tH ^ h * s.tV ^ (n - h) ∧
      0 ≤ fullBorn s e - prefixBorn s e 6 ∧
      fullBorn s e - prefixBorn s e 6 ≤ sourceTail s 6 ∧
      0 ≤ fullBorn s e ∧ fullBorn s e ≤ 1 := by
  have htail := born_truncation_budget s e 6
  have hborn := fullBorn_bounds s e
  exact ⟨sourcePrefix_add_tail s 6, sourceTail_raw s 6,
    htail.1, htail.2, hborn.1, hborn.2⟩

theorem three_no_click_cutoff_six (s : RawKernel)
    (eA eB eAB : NumberConservingEffect) :
    (0 ≤ fullBorn s eA - prefixBorn s eA 6 ∧
      fullBorn s eA - prefixBorn s eA 6 ≤ sourceTail s 6) ∧
      (0 ≤ fullBorn s eB - prefixBorn s eB 6 ∧
        fullBorn s eB - prefixBorn s eB 6 ≤ sourceTail s 6) ∧
      (0 ≤ fullBorn s eAB - prefixBorn s eAB 6 ∧
        fullBorn s eAB - prefixBorn s eAB 6 ≤ sourceTail s 6) :=
  ⟨born_truncation_budget s eA 6, born_truncation_budget s eB 6,
    born_truncation_budget s eAB 6⟩

theorem generated_no_click_enclosure (s : RawKernel) (e : NumberConservingEffect)
    {lo hi : ℝ} (hlo : lo ≤ prefixBorn s e 6) (hhi : prefixBorn s e 6 ≤ hi) :
    lo ≤ fullBorn s e ∧ fullBorn s e ≤ hi + sourceTail s 6 := by
  have htail := born_truncation_budget s e 6
  constructor <;> linarith

theorem single_pol_seed_readback {N L A B : ℝ} (hN : 0 < N) (hL : 0 < L)
    (hA : 0 < A) (hB : 0 < B) (hden : 0 < calibrationDen N L A B) :
    0 ≤ calibrationRatio N L A B ∧ calibrationRatio N L A B < 1 ∧
      meanNumber (calibrationRatio N L A B) = calibrationMean N L A B ∧
      calibrationMean N L A B / (1 + calibrationMean N L A B) =
        calibrationRatio N L A B ∧
      N * calibrationMean N L A B * calibrationTA N L A B = A ∧
      N * calibrationMean N L A B * calibrationTB N L A B = B ∧
      N * calibrationMean N L A B * (1 + calibrationMean N L A B) *
        calibrationTA N L A B * calibrationTB N L A B = L := by
  have hratio := calibrationRatio_bounds hN hL hA.le hB.le hden
  exact ⟨hratio.1, hratio.2, calibration_mapping hN hL hA hB hden⟩

end
end P23.GaussianWindow.Consumer
