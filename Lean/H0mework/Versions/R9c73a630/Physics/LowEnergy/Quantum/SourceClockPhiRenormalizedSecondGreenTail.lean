import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRenormalizedSecondGreenBudget
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiFixedSecondGreenTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiRenormalizedSecondGreenTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory SourceClockPhiNativeJointPayment
open SourceClockPhiRenormalizedSecondGreen SourceClockPhiRenormalizedSecondGreenBudget
open SourceClockPhiFixedSecondGreenTail SourceLocalizedInverseFormPayment SourceResolventBandLimit
open MeasureTheory Filter
attribute [local irreducible] diagonalAction GaussAdjointHistory.coreStep

private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    (actualFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,SourceResolventBandLimit.line_im,neg_ne_zero] using hμ.ne'
private theorem six_price_bound (a b x0 x1 y0 y1 m0 m1 c0 c1 c2 μ η : ℝ)
    (hm0 : 0 ≤ m0) (hm1 : 0 ≤ m1) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hμ : 0 ≤ μ) :
    c0*(4*η+a*b+μ*a^2)+c1*(x0^2*m0+x1^2*m1)+c2*(y0^2*m0+y1^2*m1) ≤
      4*c0*η+(c0*(1+μ)+(c1+c2)*(m0+m1))*(a^2+b^2+x0^2+x1^2+y0^2+y1^2) := by
  let S:=a^2+b^2+x0^2+x1^2+y0^2+y1^2
  have ha : a*b ≤ S := by
    dsimp only [S]
    nlinarith only [sq_nonneg (a-b),sq_nonneg a,sq_nonneg b,
      sq_nonneg x0,sq_nonneg x1,sq_nonneg y0,sq_nonneg y1]
  have h0 : a^2 ≤ S := by
    dsimp only [S]
    nlinarith only [sq_nonneg b,sq_nonneg x0,sq_nonneg x1,sq_nonneg y0,sq_nonneg y1]
  have hx0 : x0^2 ≤ S := by
    dsimp only [S]
    nlinarith only [sq_nonneg a,sq_nonneg b,sq_nonneg x1,sq_nonneg y0,sq_nonneg y1]
  have hx1 : x1^2 ≤ S := by
    dsimp only [S]
    nlinarith only [sq_nonneg a,sq_nonneg b,sq_nonneg x0,sq_nonneg y0,sq_nonneg y1]
  have hy0 : y0^2 ≤ S := by
    dsimp only [S]
    nlinarith only [sq_nonneg a,sq_nonneg b,sq_nonneg x0,sq_nonneg x1,sq_nonneg y1]
  have hy1 : y1^2 ≤ S := by
    dsimp only [S]
    nlinarith only [sq_nonneg a,sq_nonneg b,sq_nonneg x0,sq_nonneg x1,sq_nonneg y0]
  have hbase:c0*(4*η+a*b+μ*a^2) ≤ c0*(4*η+S+μ*S) :=
    mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl ha)
      (mul_le_mul_of_nonneg_left h0 hμ)) hc0
  have hX:x0^2*m0+x1^2*m1 ≤ S*(m0+m1) := by
    have h:=add_le_add (mul_le_mul_of_nonneg_right hx0 hm0) (mul_le_mul_of_nonneg_right hx1 hm1)
    exact h.trans_eq (by ring)
  have hY:y0^2*m0+y1^2*m1 ≤ S*(m0+m1) := by
    have h:=add_le_add (mul_le_mul_of_nonneg_right hy0 hm0) (mul_le_mul_of_nonneg_right hy1 hm1)
    exact h.trans_eq (by ring)
  have h:=add_le_add (add_le_add hbase (mul_le_mul_of_nonneg_left hX hc1))
    (mul_le_mul_of_nonneg_left hY hc2)
  dsimp only [S] at h
  exact h.trans_eq (by ring)

private def fixedSquareSum (m ell : ℕ) (g : diagonal.domain) : ℝ :=
  ‖embed (fixedColumn m ell g)‖^2+‖embed (diagonalAction (fixedColumn m ell g))‖^2+
    ∑i : Fin 2,(‖embed (fixedSecondTester m ell g i)‖^2+‖embed (fixedFirstTester m ell g i)‖^2)
private def secondSourceMass (g : diagonal.domain) : ℝ :=
  ∑i : Fin 2,‖(GaussAdjointHistory.coreStep (GaussAdjointHistory.coreStep (inputSeed g i)) : H)‖^2
private def fixedPriceCoefficient (μ η : ℝ) (g : diagonal.domain) : ℝ :=
  Real.pi/μ*(1+μ)+(Real.pi/(4*η*μ^3)+Real.pi/(4*η*μ))*secondSourceMass g
private theorem coefficient_nonnegative (μ η : ℝ) (hμ : 0 < μ) (hη : 0 < η) (g : diagonal.domain) :
    0 ≤ fixedPriceCoefficient μ η g := by
  unfold fixedPriceCoefficient secondSourceMass
  positivity
private theorem actual_fixed_price_bound (μ η : ℝ) (hμ : 0 < μ) (hη : 0 < η)
    (m ell : ℕ) (g : diagonal.domain) :
    fixedFrequencyPrice m ell μ η g ≤ 4*Real.pi/μ*η+
      fixedPriceCoefficient μ η g*fixedSquareSum m ell g := by
  have h:=six_price_bound
    ‖embed (fixedColumn m ell g)‖ ‖embed (diagonalAction (fixedColumn m ell g))‖
    ‖embed (fixedSecondTester m ell g 0)‖ ‖embed (fixedSecondTester m ell g 1)‖
    ‖embed (fixedFirstTester m ell g 0)‖ ‖embed (fixedFirstTester m ell g 1)‖
    (‖(GaussAdjointHistory.coreStep (GaussAdjointHistory.coreStep (inputSeed g 0)) : H)‖^2)
    (‖(GaussAdjointHistory.coreStep (GaussAdjointHistory.coreStep (inputSeed g 1)) : H)‖^2)
    (Real.pi/μ) (Real.pi/(4*η*μ^3)) (Real.pi/(4*η*μ)) μ η
    (sq_nonneg _) (sq_nonneg _) (by positivity) (by positivity) (by positivity) hμ.le
  unfold fixedFrequencyPrice fixedPriceCoefficient fixedSquareSum secondSourceMass
  simp only [Fin.sum_univ_two]
  convert h using 1
  ring

/-- The actual four-order source jets and original spectral masses produce one absolute all-frequency endpoint tail. -/
theorem actual_renormalized_endpoint_absolute_common_tail (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain)
    (ε : ℝ) (hε : 0 < ε) :
    ∃N : ℕ,∀m,N  ≤  m → ∀ell,m  ≤  ell → ∀ᶠ F in (sourceFilter : Filter Index),∀advanced : Bool,
      (∫⁻w : ℝ,ENNReal.ofReal (|renormalizedEndpoint m ell F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g|)) ≤ ENNReal.ofReal ε := by
  let η:=ε*μ/(8*Real.pi)
  have hη:0<η := by dsimp only [η];positivity
  let C:=fixedPriceCoefficient μ η g
  have hC:0 ≤ C := coefficient_nonnegative μ η hμ hη g
  obtain ⟨N,hN⟩:=actual_fixed_second_green_endpoint_common_tail g (ε/(2*(C+1))) (by positivity)
  refine ⟨N,fun m hm ell he=>?_⟩
  filter_upwards [actual_renormalized_fixed_frequency_budget μ hμ g η hη] with F hF
  intro advanced
  have hs:fixedSquareSum m ell g ≤ ε/(2*(C+1)) := hN m hm ell he
  have hb:=actual_fixed_price_bound μ η hμ hη m ell g
  have hηε:4*Real.pi/μ*η=ε/2 := by
    dsimp only [η]
    field_simp [ne_of_gt hμ,Real.pi_ne_zero]
    ring
  have hscaled:C*fixedSquareSum m ell g ≤ C*(ε/(2*(C+1))) := mul_le_mul_of_nonneg_left hs hC
  have hp:C*(ε/(2*(C+1))) ≤ ε/2 := by
    have hd:0<2*(C+1) := by positivity
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith only [hε]
  calc
    _ ≤ ENNReal.ofReal (fixedFrequencyPrice m ell μ η g) := hF m ell advanced
    _ ≤ ENNReal.ofReal ε := by
      apply ENNReal.ofReal_le_ofReal
      change fixedFrequencyPrice m ell μ η g ≤ _ at hb
      rw [hηε] at hb
      nlinarith only [hb,hscaled,hp]

end LowEnergy.SourceClockPhiRenormalizedSecondGreenTail
