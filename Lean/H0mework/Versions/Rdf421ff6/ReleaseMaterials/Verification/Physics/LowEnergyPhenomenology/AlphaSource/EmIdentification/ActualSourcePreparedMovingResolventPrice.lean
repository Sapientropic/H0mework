import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedMovingNoetherResolvent

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedMovingResolventPrice
open CanonicalGradedSpatialSource GaussCoreHilbert PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback (PhysicalResponsePoint)
open PreparationVacuumGaugeSourceInjection (laplaceWeight)
open PreparationVacuumPhysicalHalfAxis (laplace_norm)
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalTailPrice PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPropagationPencil SourcePropagationResolvent SourcePropagationCommonMomentum
open ActualDressedFullCoulomb ActualDressedNoether ActualSourcePreparedMovingNoetherResolvent
open MeasureTheory Set
open scoped BigOperators
private abbrev SourceOp := SourcePropagationResolvent.Op
private abbrev SourceTransferOp := SourcePropagationResolvent.TransferOp
local instance : AddCommGroup SourceTransferOp := ContinuousLinearMap.addCommGroup
local instance : NormedAlgebra ℝ SourceOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ SourceTransferOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedSpace ℝ SourceTransferOp := ContinuousLinearMap.toNormedSpace
local instance : NormSMulClass ℂ SourceTransferOp := by
  convert! (NormedSpace.toNormSMulClass (𝕜:=ℂ) (E:=SourceTransferOp)) using 1
local instance : ContinuousENorm SourceTransferOp := by
  convert! (SeminormedAddGroup.toContinuousENorm (E:=SourceTransferOp)) using 1
attribute [local irreducible] actualA actualGrowth factorialBudget sourceInverse

private theorem common_budget (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (eta : ℝ) :
    factorialBudget p F eta = factorialBudget 0 F eta := by
  unfold factorialBudget
  exact congrArg (fun A : SourceOp => ∑ j ∈ Finset.range 57, (j.factorial:ℝ)*(‖A‖/eta)^j)
    (actualA_common p F)

private theorem exponential_integral_price {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (B a : ℝ) (positive : 0 < a)
    (bound : ∀ t, 0 < t → ‖f t‖ ≤ B*Real.exp (-a*t)) :
    ‖∫ t in Ioi (0:ℝ), f t‖ ≤ B/a := by
  have integrable : IntegrableOn (fun t : ℝ => B*Real.exp (-a*t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos positive) 0).const_mul B
  have paid := norm_integral_le_of_norm_le integrable
    ((ae_restrict_mem measurableSet_Ioi).mono (fun t future => bound t future))
  have evaluated : (∫ t : ℝ in Ioi 0, B*Real.exp (-a*t)) = B/a := by
    rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos positive)]
    simp only [mul_zero, Real.exp_zero, div_neg, neg_div, neg_neg]
    ring
  exact paid.trans_eq evaluated

/-- The uncut source retainer is the same on both moving momentum legs. -/
theorem source_inverse_common_laplace_price (q : PhysicalResponsePoint) (lambda : ℂ)
    (eta : ℝ) (positive : 0 < eta) (margin : 2*eta < lambda.re) :
    ‖sourceInverse q lambda‖ ≤ (factorialBudget 0 q.F eta)^2/(lambda.re-2*eta) := by
  have budget_nonnegative := factorialBudget_nonnegative 0 q.F eta positive
  have time (t : ℝ) (future : 0 ≤ t) :
      ‖twoTimeMap q t‖ ≤ (factorialBudget 0 q.F eta)^2*Real.exp ((2*eta)*t) := by
    have left := actualGrowth_envelope (q.p+q.k) q.F eta t positive future
    have right := actualGrowth_envelope q.p q.F eta t positive future
    have original := twoTimeMap_bound q t
    rw [abs_of_nonneg future] at original
    rw [common_budget] at left right
    have product := mul_le_mul left right (actualGrowth_nonnegative _ _ _ future)
      (mul_nonneg budget_nonnegative (Real.exp_pos _).le)
    refine original.trans (product.trans_eq ?_)
    calc
      _ = (factorialBudget 0 q.F eta)^2*(Real.exp (eta*t)*Real.exp (eta*t)) := by ring
      _ = _ := by rw [←Real.exp_add]; congr 2; ring
  have estimate (t : ℝ) (future : 0 < t) :
      ‖laplaceWeight lambda t • twoTimeMap q t‖ ≤
        (factorialBudget 0 q.F eta)^2*Real.exp (-(lambda.re-2*eta)*t) := by
    rw [norm_smul, laplace_norm]
    have paid := mul_le_mul_of_nonneg_left (time t future.le) (Real.exp_pos (-lambda.re*t)).le
    refine paid.trans_eq ?_
    calc
      _ = (factorialBudget 0 q.F eta)^2*
          (Real.exp (-lambda.re*t)*Real.exp ((2*eta)*t)) := by ring
      _ = _ := by rw [←Real.exp_add]; congr 2; ring
  unfold sourceInverse
  exact exponential_integral_price (fun t => laplaceWeight lambda t • twoTimeMap q t)
    _ _ (sub_pos.mpr margin) estimate

def sourceClockResolventBudget (F : GaussUnitaryHistory.Index) (sigma : ℝ) : ℝ :=
  2*(factorialBudget 0 F (sigma/4))^2/sigma

theorem source_clock_resolvent_budget (q : PhysicalResponsePoint) (sigma : ℝ) (positive : 0 < sigma) :
    ‖sourceInverse q (sigma:ℂ)‖ ≤ sourceClockResolventBudget q.F sigma := by
  have original := source_inverse_common_laplace_price q (sigma:ℂ) (sigma/4)
    (by positivity) (by simpa only [Complex.ofReal_re] using (show 2*(sigma/4) < sigma by linarith))
  refine original.trans_eq ?_
  simp only [Complex.ofReal_re, sourceClockResolventBudget]
  field_simp [ne_of_gt positive]
  ring

/-- Both source resolvents in the moving update receive one common clock
price. The complete uncut retainer and actual momentum insertion stay present. -/
theorem source_moving_resolvent_correction_price (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (sigma : ℝ) (positive : 0 < sigma) :
    ‖sourceMovingResolventCorrection event eps n (sigma:ℂ)‖ ≤
      (sourceClockResolventBudget event.frame sigma)^2*‖momentumCompressionMap event.frame n‖ := by
  with_reducible_and_instances
  have left := source_clock_resolvent_budget (dressedKinematicPoint event (eps^2 • n)) sigma positive
  have right := source_clock_resolvent_budget (dressedKinematicPoint event 0) sigma positive
  dsimp only [dressedKinematicPoint] at left right
  have nonnegative : 0 ≤ sourceClockResolventBudget event.frame sigma := by
    unfold sourceClockResolventBudget
    positivity
  have insertion := ContinuousLinearMap.opNorm_mul_apply_le ℂ SourceOp (momentumCompressionMap event.frame n)
  have paid := (norm_mul_le
    (sourceInverse (dressedKinematicPoint event (eps^2 • n)) (sigma:ℂ) *
      ContinuousLinearMap.mul ℂ SourceOp (momentumCompressionMap event.frame n))
    (sourceInverse (dressedKinematicPoint event 0) (sigma:ℂ))).trans
    (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul left insertion (norm_nonneg _) nonnegative))
      right (norm_nonneg (sourceInverse (dressedKinematicPoint event 0) (sigma:ℂ)))
      (mul_nonneg nonnegative (norm_nonneg (momentumCompressionMap event.frame n))))
  have rearrange : sourceClockResolventBudget event.frame sigma*‖momentumCompressionMap event.frame n‖*
      sourceClockResolventBudget event.frame sigma =
        (sourceClockResolventBudget event.frame sigma)^2*‖momentumCompressionMap event.frame n‖ := by ring
  simpa only [sourceMovingResolventCorrection] using paid.trans_eq rearrange

private theorem scaled_update_price {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u v k : E) (eps B : ℝ) (update : u=v+(-Complex.I*(eps:ℂ)^2) • k)
    (price : ‖k‖ ≤ B) : ‖u-v‖ ≤ eps^2*B := by
  rw [update, add_sub_cancel_left, norm_smul, norm_mul, norm_neg, Complex.norm_I,
    one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact mul_le_mul_of_nonneg_left price (sq_nonneg eps)

theorem source_moving_resolvent_difference_price (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (sigma : ℝ) (positive : 0 < sigma) :
    ‖sourceInverse (dressedKinematicPoint event (eps^2 • n)) (sigma:ℂ)-
      sourceInverse (dressedKinematicPoint event 0) (sigma:ℂ)‖ ≤
      eps^2*(sourceClockResolventBudget event.frame sigma)^2*‖momentumCompressionMap event.frame n‖ := by
  have clock : 0 < (sigma:ℂ).re := by simpa only [Complex.ofReal_re] using positive
  have update := source_moving_resolvent_update event eps n (sigma:ℂ) clock
  have paid := scaled_update_price
    (sourceInverse (dressedKinematicPoint event (eps^2 • n)) (sigma:ℂ))
    (sourceInverse (dressedKinematicPoint event 0) (sigma:ℂ))
    (sourceMovingResolventCorrection event eps n (sigma:ℂ)) eps
    ((sourceClockResolventBudget event.frame sigma)^2*‖momentumCompressionMap event.frame n‖)
    update (source_moving_resolvent_correction_price event eps n sigma positive)
  exact paid.trans_eq (by ring)

end LowEnergy.GaussComposite.ActualSourcePreparedMovingResolventPrice
