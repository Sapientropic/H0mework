import H0mework.Versions.X.NavierStokes.WindowSourceGreen.FormProduct
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.Weights

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowGreenTestForm
open NativeUnheatedTreeRieszKernel (Wave E)
open NativeWindowGreenProduct
open NativeUnheatedQuinticWeights (eta eta_nonnegative eta_square_summable)
open NativeCompleteStressCarrier (weight weight_pos)
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
noncomputable section

theorem weight_le_one (k : Wave) : weight k ≤ 1 := NativeUnheatedPairWindowTail.weight_le_one k

def testKernel : Kernel where
  value k p := Real.sqrt (eta p*eta (k-p))
  cap := ∑' k, eta k^2
  cap_nonnegative := tsum_nonneg fun _ => sq_nonneg _
  nonnegative _ _ := Real.sqrt_nonneg _
  squares k F := by
    have first := eta_square_summable.sum_le_tsum F (fun _ _ => sq_nonneg _)
    have last := eta_square_summable.sum_le_tsum (F.image (fun p => k-p)) (fun _ _ => sq_nonneg _)
    rw [Finset.sum_image (fun _ _ _ _ equal => sub_right_injective equal)] at last
    have each := Finset.sum_le_sum (s := F) (fun p _ =>
      show eta p*eta (k-p) ≤ (eta p^2+eta (k-p)^2)/2 by nlinarith [sq_nonneg (eta p-eta (k-p))])
    rw [← Finset.sum_div,Finset.sum_add_distrib] at each
    simpa only [Real.sq_sqrt (mul_nonneg (eta_nonnegative _) (eta_nonnegative _))] using
      each.trans (by linarith)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
abbrev Test (H : Type*) [NormedAddCommGroup H] := lp (fun _ : Wave => H) 2

def decode (T : Test H) : Test H :=
  ⟨fun k => Real.sqrt (weight k) • T k, (lp.memℓp T).mono' fun k => by
    rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.sqrt_le_one.mpr (weight_le_one k))⟩

def fractional (T : Test H) : E :=
  ⟨fun k => weight k^(1/16 : ℝ)*‖T k‖, (lp.memℓp (lp.toNorm T)).mono' fun k => by
    change ‖weight k^(1/16 : ℝ)*‖T k‖‖ ≤ ‖‖T k‖‖
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (weight_pos k).le _) (norm_nonneg _)),norm_norm]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one (weight_pos k).le (weight_le_one k) (by norm_num))⟩

theorem decode_square (T : Test H) (k : Wave) : ‖decode T k‖^2 = weight k*‖T k‖^2 := by
  change ‖Real.sqrt (weight k) • T k‖^2 = _
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (weight_pos k).le]

theorem fractional_read (T : Test H) (k : Wave) :
    ‖decode T k‖ = Real.sqrt (eta k)*fractional T k := by
  change ‖Real.sqrt (weight k) • T k‖ = Real.sqrt (eta k)*(weight k^(1/16 : ℝ)*‖T k‖)
  rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sqrt_eq_rpow,eta,Real.sqrt_eq_rpow,
    ← Real.rpow_mul (weight_pos k).le,← mul_assoc,← Real.rpow_add (weight_pos k)]
  norm_num

omit [NormedSpace ℝ H] in
theorem fractional_nonnegative (T : Test H) (k : Wave) : 0 ≤ fractional T k := by
  change 0 ≤ weight k^(1/16 : ℝ)*‖T k‖
  positivity [weight_pos k]

theorem norm_square {E' : Type*} [NormedAddCommGroup E'] (T : Test E') : ‖T‖^2 = ∑' k, ‖T k‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) T

theorem square_summable {E' : Type*} [NormedAddCommGroup E'] (T : Test E') : Summable (fun k => ‖T k‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) T).summable

theorem fractional_eighth (T : Test H) : ‖fractional T‖^16 ≤ ‖decode T‖^2*‖T‖^14 := by
  have finite (F : Finset Wave) : (∑ k ∈ F, ‖fractional T k‖^2)^8 ≤ ‖decode T‖^2*(‖T‖^2)^7 := by
    have paid := NativeMovingCriticalProductWeights.dyadic_interpolation F
      (fun k => weight k^(-1/8 : ℝ)) (fun k => ‖decode T k‖) (fun k => Real.rpow_nonneg (weight_pos k).le _)
    have powers (k : Wave) (n : ℕ) : (weight k^(-1/8 : ℝ))^n*‖decode T k‖^2 =
        weight k^(1-(n : ℝ)/8)*‖T k‖^2 := by
      rw [decode_square,← Real.rpow_mul_natCast (weight_pos k).le]
      calc
        _ = (weight k^((-1/8 : ℝ)*n)*weight k^((1 : ℝ)))*‖T k‖^2 := by rw [Real.rpow_one]; ring
        _ = _ := by rw [← Real.rpow_add (weight_pos k)]; congr 2; ring
    have low := (square_summable (decode T)).sum_le_tsum F (fun _ _ => sq_nonneg _)
    have high := (square_summable T).sum_le_tsum F (fun _ _ => sq_nonneg _)
    rw [← norm_square] at low high
    have first : (∑ k ∈ F, (weight k^(-1/8 : ℝ))^7*‖decode T k‖^2) = ∑ k ∈ F, ‖fractional T k‖^2 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [powers]
      change weight k^(1-(7 : ℝ)/8)*‖T k‖^2 = ‖weight k^(1/16 : ℝ)*‖T k‖‖^2
      rw [Real.norm_eq_abs,sq_abs,mul_pow,← Real.rpow_mul_natCast (weight_pos k).le]
      norm_num
    rw [first] at paid
    simp only [powers] at paid
    norm_num at paid
    simpa only [Real.norm_eq_abs,sq_abs] using paid.trans (mul_le_mul low (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => sq_nonneg _) high 7)
      (pow_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) 7) (sq_nonneg _))
  have limit : Filter.Tendsto (fun F : Finset Wave => ∑ k ∈ F, ‖fractional T k‖^2) Filter.atTop (nhds (‖fractional T‖^2)) := by
    have paid : HasSum (fun k => ‖fractional T k‖^2) (‖fractional T‖^2) := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (fractional T)
    exact paid
  convert! le_of_tendsto (limit.pow 8) (Filter.Eventually.of_forall finite) using 1 <;> ring

def gradient (T : Test H) : ℝ := ∑' k, integerWaveNormSq k*‖decode T k‖^2

theorem gradient_summable (T : Test H) : Summable (fun k => integerWaveNormSq k*‖decode T k‖^2) := by
  apply (square_summable T).of_nonneg_of_le (fun k => mul_nonneg (integerWaveNormSq_nonneg k) (sq_nonneg _))
  intro k
  rw [decode_square,← mul_assoc]
  by_cases zero : k = 0
  · subst k; simp [integerWaveNormSq]
  · rw [weight,if_neg zero,mul_inv_cancel₀ (integerWaveNormSq_pos zero).ne',one_mul]

theorem high_le_gradient_mass (T : Test H) : ‖T‖^2 ≤ gradient T+‖decode T‖^2 := by
  rw [gradient,norm_square T,norm_square (decode T),← (gradient_summable T).tsum_add (square_summable (decode T))]
  apply (square_summable T).tsum_le_tsum _ ((gradient_summable T).add (square_summable (decode T)))
  intro k
  rw [decode_square]
  by_cases zero : k = 0
  · subst k; simp [weight,integerWaveNormSq]
  · rw [weight,if_neg zero,← mul_assoc, mul_inv_cancel₀ (integerWaveNormSq_pos zero).ne',one_mul]
    exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr (integerWaveNormSq_nonneg k)) (sq_nonneg _))

theorem eta_neg (k : Wave) : eta (-k) = eta k := by
  simp only [eta,weight,neg_eq_zero,integerWaveNormSq,Pi.neg_apply,Int.cast_neg,neg_sq]

variable [InnerProductSpace ℂ H]

def integrand (c : ComplexSpace) (A : H →L[ℂ] H) (T : Test H) (index : Wave × Wave) : ℂ :=
  c index.1*inner ℂ (decode T index.2) (A (decode T (index.2-index.1)))

theorem integrand_bound (c : ComplexSpace) (A : H →L[ℂ] H) (T : Test H) (index : Wave × Wave) :
    ‖integrand c A T index‖ ≤ ‖A‖*term testKernel (fractional T) (NativeUnheatedTreeRieszPermutations.flip (fractional T))
      (lp.toNorm c) index := by
  have paid := (norm_inner_le_norm (𝕜 := ℂ) (decode T index.2) (A (decode T (index.2-index.1))))
    |>.trans (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _))
  have scaled := mul_le_mul_of_nonneg_left paid (norm_nonneg (c index.1))
  rw [integrand,norm_mul]
  apply scaled.trans_eq
  rw [fractional_read,fractional_read,term]
  simp only [NativeUnheatedTreeRieszPermutations.flip_apply,lp.toNorm,abs_of_nonneg (fractional_nonnegative T _),
    abs_of_nonneg (norm_nonneg _),testKernel,neg_sub]
  have same : eta (index.2-index.1) = eta (index.1-index.2) := by
    rw [← neg_sub index.1 index.2,eta_neg]
  rw [same,Real.sqrt_mul (eta_nonnegative _)]
  ring

theorem form_summable (c : ComplexSpace) (A : H →L[ℂ] H) (T : Test H) : Summable (fun index => ‖integrand c A T index‖) :=
  ((summable testKernel (fractional T) (NativeUnheatedTreeRieszPermutations.flip (fractional T)) (lp.toNorm c)).mul_left ‖A‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) (integrand_bound c A T)

def form (c : ComplexSpace) (A : H →L[ℂ] H) (T : Test H) : ℂ := ∑' index, integrand c A T index

theorem form_bound (c : ComplexSpace) (A : H →L[ℂ] H) (T : Test H) :
    ‖form c A T‖ ≤ (‖A‖*Real.sqrt testKernel.cap*‖c‖)*‖fractional T‖^2 := by
  apply (norm_tsum_le_tsum_norm (form_summable c A T)).trans
  apply ((form_summable c A T).tsum_le_tsum (integrand_bound c A T)
    ((summable testKernel (fractional T) (NativeUnheatedTreeRieszPermutations.flip (fractional T)) (lp.toNorm c)).mul_left ‖A‖)).trans
  rw [tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left (bound testKernel (fractional T)
    (NativeUnheatedTreeRieszPermutations.flip (fractional T)) (lp.toNorm c)) (norm_nonneg A)).trans_eq (by
      rw [NativeUnheatedTreeRieszPermutations.flip_norm,lp.norm_toNorm]; ring)

theorem absorb {x a m h epsilon : ℝ} (_x0 : 0 ≤ x) (_a0 : 0 ≤ a) (m0 : 0 ≤ m) (h0 : 0 ≤ h)
    (positive : 0 < epsilon) (paid : x^8 ≤ a^8*m*h^7) : x ≤ epsilon*h+(a^8*epsilon⁻¹^7)*m := by
  by_cases low : x ≤ epsilon*h
  · exact low.trans (le_add_of_nonneg_right (by positivity))
  · have xPositive : 0 < x := lt_of_le_of_lt (mul_nonneg positive.le h0) (lt_of_not_ge low)
    have high : h ≤ epsilon⁻¹*x := by
      rw [mul_comm epsilon⁻¹]
      apply (le_mul_inv_iff₀ positive).mpr
      simpa only [mul_comm] using (lt_of_not_ge low).le
    have estimate := paid.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 high 7) (by positivity))
    have bound : x ≤ (a^8*epsilon⁻¹^7)*m := by
      apply (mul_le_mul_iff_right₀ (pow_pos xPositive 7)).mp
      convert! estimate using 1
      ring
    exact bound.trans (le_add_of_nonneg_left (mul_nonneg positive.le h0))

theorem form_absorption (c : ComplexSpace) (A : H →L[ℂ] H) (T : Test H) (epsilon : ℝ) (positive : 0 < epsilon) :
    ‖form c A T‖ ≤ epsilon*gradient T+
      (epsilon+(‖A‖*Real.sqrt testKernel.cap*‖c‖)^8*epsilon⁻¹^7)*‖decode T‖^2 := by
  have power := pow_le_pow_left₀ (norm_nonneg _) (form_bound c A T) 8
  rw [mul_pow,← pow_mul,show (2 : ℕ)*8=16 from rfl] at power
  have paid := power.trans (mul_le_mul_of_nonneg_left (fractional_eighth T) (by positivity))
  have estimate := absorb (norm_nonneg (form c A T)) (by positivity) (sq_nonneg ‖decode T‖) (sq_nonneg ‖T‖) positive
    (show ‖form c A T‖^8 ≤ (‖A‖*Real.sqrt testKernel.cap*‖c‖)^8*‖decode T‖^2*(‖T‖^2)^7 by convert! paid using 1; ring)
  nlinarith only [estimate,mul_le_mul_of_nonneg_left (high_le_gradient_mass T) positive.le]

open PhysicsCore.DiracCliffordRepresentation
open PhysicsCore.StageNineFullDiracAdjointMaterial (diracAdjointSpinSwap)
abbrev SpinFiber (G : Type*) := PiLp 2 (fun _ : Fin 4 × Fin 2 => G)

def spinAction {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] (matrix : DiracMatrix) :
    SpinFiber G →L[ℂ] SpinFiber G :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 4 × Fin 2 => G)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun entry => ∑ other : Fin 4,
      matrix entry.1 other • PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 4 × Fin 2 => G) (other,entry.2))

theorem spinAction_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] (matrix : DiracMatrix)
    (field : SpinFiber G) (entry : Fin 4 × Fin 2) :
    spinAction matrix field entry = ∑ other : Fin 4, matrix entry.1 other • field (other,entry.2) := by
  simp [spinAction]

def spatialOperator {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (direction : Fin 3) : SpinFiber G →L[ℂ] SpinFiber G :=
  (spinAction (G := G) diracAdjointSpinSwap).adjoint.comp (spinAction (Complex.I • diracGamma direction.succ))

theorem spatialOperator_current (data : NativeStressPairingCarrier.Data) (direction : Fin 3)
    (first last : NativeHilbertDiracCurrent.Spinor data) :
    inner ℂ (WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => first entry.1 entry.2))
      (spatialOperator direction (WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => last entry.1 entry.2))) =
      NativeHilbertDiracCurrent.canonicalDual data first
        (NativeHilbertDiracCurrent.action data (Complex.I • diracGamma direction.succ) last) := by
  rw [spatialOperator,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,PiLp.inner_apply,Fintype.sum_prod_type]
  simp only [spinAction_apply,NativeHilbertDiracCurrent.canonicalDual,
    NativeHilbertDiracCurrent.action,LinearMap.coe_mk,AddHom.coe_mk]

theorem swap_norm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] (field : SpinFiber G) :
    ‖spinAction diracAdjointSpinSwap field‖ = ‖field‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type,spinAction_apply]
  simp [diracAdjointSpinSwap,Fin.sum_univ_four,Fin.sum_univ_two]
  ring

theorem gamma_norm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] (direction : Fin 3) (field : SpinFiber G) :
    ‖spinAction (Complex.I • diracGamma direction.succ) field‖ = ‖field‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type,spinAction_apply]
  fin_cases direction <;> simp [diracGamma,diracGammaOne,diracGammaTwo,diracGammaThree,
    Fin.sum_univ_four,Fin.sum_univ_two,norm_smul] <;> ring

theorem spatialOperator_norm {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (direction : Fin 3) : ‖spatialOperator (G := G) direction‖ ≤ 1 := by
  have swap : ‖spinAction (G := G) diracAdjointSpinSwap‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun field => by rw [swap_norm,one_mul])
  have gamma : ‖spinAction (G := G) (Complex.I • diracGamma direction.succ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun field => by rw [gamma_norm,one_mul])
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    rw [LinearIsometryEquiv.norm_map]
    exact (mul_le_mul swap gamma (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

end
end SaturationMonoid.NavierStokes.NativeWindowGreenTestForm
