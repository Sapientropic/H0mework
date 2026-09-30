import H0mework.Physics.LowEnergy.Quantum.SourceQuantumFockGauge

/-! The original full504 CAR exponential and residual configuration pullback
act on the same number-weighted source Fock Hilbert space. Number preservation
cancels the existing half densities exactly; the resulting action is the literal
inverse CAR action times configuration pullback and preserves the original
compact-inside smooth test domain.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.SourceQuantumFockGaugeHilbert
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open SourceQuantumHalfDensityHilbert SourceQuantumResidualChartFlow SourceQuantumFockGauge
open scoped BigOperators ComplexConjugate

def flatGamma (a : stabilizer) (t : ℝ) : FlatFockHilbert →ₗ[ℂ] FlatFockHilbert where
  toFun psi := WithLp.toLp 2 (fun output => ∑ input : Occupation, gammaMatrix a t output input • psi input)
  map_add' psi phi := by ext word; simp [smul_add, Finset.sum_add_distrib]
  map_smul' c psi := by ext word; simp [Finset.smul_sum, smul_smul, mul_comm]

theorem flatGamma_apply (a : stabilizer) (t : ℝ) (psi : FlatFockHilbert) (output : Occupation) :
    flatGamma a t psi output = ∑ input : Occupation, gammaMatrix a t output input • psi input := rfl

theorem flatGamma_inner (a : stabilizer) (t : ℝ) (psi phi : FlatFockHilbert) :
    inner ℂ (flatGamma a t psi) (flatGamma a t phi) = inner ℂ psi phi := by
  simp only [PiLp.inner_apply, flatGamma_apply, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext w
    rw [Finset.sum_comm]
  calc
    (∑ w : Occupation, ∑ i : Occupation, ∑ j : Occupation,
      gammaMatrix a t w j * (star (gammaMatrix a t w i) * inner ℂ (psi i) (phi j))) =
      ∑ i : Occupation, ∑ j : Occupation, (∑ w : Occupation,
        star (gammaMatrix a t w i) * gammaMatrix a t w j) * inner ℂ (psi i) (phi j) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro w _
          ring
    _ = ∑ i : Occupation, inner ℂ (psi i) (phi i) := by
      simp only [gammaMatrix_columns, ite_mul, one_mul, zero_mul]
      simp

theorem flatGamma_inverse (a : stabilizer) (t : ℝ) (psi : FlatFockHilbert) :
    flatGamma a (-t) (flatGamma a t psi) = psi := by
  apply PiLp.ext
  intro output
  simp only [flatGamma_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  calc
    (∑ input : Occupation, ∑ middle : Occupation,
      (gammaMatrix a (-t) output middle * gammaMatrix a t middle input) • psi input) =
      ∑ input : Occupation, (∑ middle : Occupation,
        gammaMatrix a (-t) output middle * gammaMatrix a t middle input) • psi input := by
          apply Finset.sum_congr rfl
          intro input _
          rw [Finset.sum_smul]
    _ = psi output := by simp [gammaMatrix_inverse]

def flatGammaUnitary (a : stabilizer) (t : ℝ) : FlatFockHilbert ≃ₗᵢ[ℂ] FlatFockHilbert where
  toFun := flatGamma a t
  invFun := flatGamma a (-t)
  left_inv := flatGamma_inverse a t
  right_inv psi := by simpa only [neg_neg] using flatGamma_inverse a (-t) psi
  map_add' := (flatGamma a t).map_add
  map_smul' := (flatGamma a t).map_smul
  norm_map' psi := by
    change ‖flatGamma a t psi‖ = ‖psi‖
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), flatGamma_inner]

def fiberUnitary (a : stabilizer) (t : ℝ) : FockHilbert ≃ₗᵢ[ℂ] FockHilbert :=
  fockHalfDensityEquiv.trans ((flatGammaUnitary a t).trans fockHalfDensityEquiv.symm)

def configurationUnitary (a : stabilizer) : FockHilbert ≃ₗᵢ[ℂ] FockHilbert :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun word => sectorUnitary word.card a)

def fullGaugeUnitary (a : stabilizer) : FockHilbert ≃ₗᵢ[ℂ] FockHilbert :=
  (configurationUnitary a).trans (fiberUnitary a (-1))

theorem fiberUnitary_component (a : stabilizer) (t : ℝ) (psi : FockHilbert) (output : Occupation) :
    fiberUnitary a t psi output = (halfDensityEquiv output.card).symm
      (∑ input : Occupation, gammaMatrix a t output input • halfDensityEquiv input.card (psi input)) := rfl

theorem fiberUnitary_testDomain (a : stabilizer) (t : ℝ) (psi : FockHilbert)
    (hpsi : psi ∈ fockTestDomain) : fiberUnitary a t psi ∈ fockTestDomain := by
  intro output
  rw [fiberUnitary_component, map_sum]
  apply (testDomain output.card).sum_mem
  intro input _
  by_cases hn : input.card = output.card
  · rw [← hn, map_smul, LinearIsometryEquiv.symm_apply_apply]
    exact (testDomain input.card).smul_mem _ (hpsi input)
  · rw [gammaMatrix_number_zero a t output input (Ne.symm hn), zero_smul, map_zero]
    exact (testDomain output.card).zero_mem


theorem fiberUnitary_inverse (a : stabilizer) (t : ℝ) (psi : FockHilbert) :
    fiberUnitary a (-t) (fiberUnitary a t psi) = psi := by
  change fockHalfDensityEquiv.symm
    (flatGamma a (-t) (fockHalfDensityEquiv (fockHalfDensityEquiv.symm
      (flatGamma a t (fockHalfDensityEquiv psi))))) = psi
  rw [LinearIsometryEquiv.apply_symm_apply, flatGamma_inverse,
    LinearIsometryEquiv.symm_apply_apply]

theorem fiberUnitary_testDomain_iff (a : stabilizer) (t : ℝ) (psi : FockHilbert) :
    fiberUnitary a t psi ∈ fockTestDomain ↔ psi ∈ fockTestDomain := by
  constructor
  · intro h
    have hi := fiberUnitary_testDomain a (-t) (fiberUnitary a t psi) h
    simpa only [fiberUnitary_inverse] using hi
  · exact fiberUnitary_testDomain a t psi

theorem configurationUnitary_testDomain_iff (a : stabilizer) (psi : FockHilbert) :
    configurationUnitary a psi ∈ fockTestDomain ↔ psi ∈ fockTestDomain := by
  change (∀ word : Occupation, sectorUnitary word.card a (psi word) ∈ testDomain word.card) ↔
    ∀ word : Occupation, psi word ∈ testDomain word.card
  simp only [sectorUnitary_testDomain_iff]

theorem fullGaugeUnitary_testDomain_iff (a : stabilizer) (psi : FockHilbert) :
    fullGaugeUnitary a psi ∈ fockTestDomain ↔ psi ∈ fockTestDomain := by
  change fiberUnitary a (-1) (configurationUnitary a psi) ∈ fockTestDomain ↔ _
  rw [fiberUnitary_testDomain_iff, configurationUnitary_testDomain_iff]

open MeasureTheory Filter

private theorem transfer_term_ae (a : stabilizer) (t : ℝ) (psi : FockHilbert)
    (output input : Occupation) :
    (halfDensityEquiv output.card).symm
      (gammaMatrix a t output input • halfDensityEquiv input.card (psi input)) =ᵐ[chartMeasure]
        fun z => gammaMatrix a t output input * psi input z := by
  by_cases hn : output.card = input.card
  · rw [hn, map_smul, LinearIsometryEquiv.symm_apply_apply]
    exact (Lp.coeFn_smul (gammaMatrix a t output input) (psi input)).filter_mono
      (weighted_null_sets input.card).ae_le
  · rw [gammaMatrix_number_zero a t output input hn, zero_smul, map_zero]
    filter_upwards [(Lp.coeFn_zero ℂ 2 (numberMeasure output.card)).filter_mono
      (weighted_null_sets output.card).ae_le] with z hz
    exact hz.trans (zero_mul (psi input z)).symm

theorem fiberUnitary_apply_ae (a : stabilizer) (t : ℝ) (psi : FockHilbert) (output : Occupation) :
    fiberUnitary a t psi output =ᵐ[chartMeasure]
      fun z => ∑ input : Occupation, gammaMatrix a t output input * psi input z := by
  rw [fiberUnitary_component, map_sum]
  have hs := (Lp.coeFn_fun_finsetSum Finset.univ (fun input : Occupation =>
    (halfDensityEquiv output.card).symm
      (gammaMatrix a t output input • halfDensityEquiv input.card (psi input)))).filter_mono
        (weighted_null_sets output.card).ae_le
  have hall : ∀ᵐ z ∂chartMeasure, ∀ input : Occupation,
      (halfDensityEquiv output.card).symm
        (gammaMatrix a t output input • halfDensityEquiv input.card (psi input)) z =
          gammaMatrix a t output input * psi input z :=
    ae_all_iff.mpr (fun input => transfer_term_ae a t psi output input)
  filter_upwards [hs, hall] with z hz h
  exact hz.trans (Finset.sum_congr rfl (fun input _ => h input))

theorem fullGaugeUnitary_apply_ae (a : stabilizer) (psi : FockHilbert) (output : Occupation) :
    fullGaugeUnitary a psi output =ᵐ[chartMeasure]
      fun z => ∑ input : Occupation, gammaMatrix a (-1) output input * psi input (chartFlow a z) := by
  have h := fiberUnitary_apply_ae a (-1) (configurationUnitary a psi) output
  have hall : ∀ᵐ z ∂chartMeasure, ∀ input : Occupation,
      configurationUnitary a psi input z = psi input (chartFlow a z) :=
    ae_all_iff.mpr (fun input => (sectorUnitary_apply_ae input.card a (psi input)).filter_mono
      (weighted_null_sets input.card).ae_le)
  filter_upwards [h, hall] with z hz hi
  exact hz.trans (Finset.sum_congr rfl (fun input _ => congrArg
    (fun v : ℂ => gammaMatrix a (-1) output input * v) (hi input)))

end LowEnergy.SourceQuantumFockGaugeHilbert
