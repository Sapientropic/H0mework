import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusContactClosureConsumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusContactPsiPriceSource
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource
open OriginalWholeDebtRJointMobiusContactClosureSource OriginalWholeDebtRAdjointContactSource
open scoped InnerProductSpace Topology
open private source_inner_hasDerivAt source_outer_hasDerivAt
  source_inner_continuousOn source_inner_slope_continuousOn
  source_outer_continuousOn source_outer_slope_continuousOn native_pair_read native_pair_integrable from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource
open private power_raw_weight from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRQuarterUnitSettlementSource
open private even_half_integral from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSourceRaw
local notation "q" => (1/4 : ℝ)
local notation "p" => junctionPoint
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "W" => SingularCounting.powerL2
local notation "w" => SingularCounting.centeredPower

def contactDiagonal (radius : ℝ) : M := TwoPieceFourierAction.eta radius+
  burnolMeanZeroTruncatedFourier (burnolMeanZeroBlockInverse
    (burnolMeanZeroTruncatedFourier (TwoPieceFourierAction.eta radius)))

def contactCross (radius : ℝ) : M := burnolMeanZeroTruncatedFourier
  (burnolMeanZeroBlockInverse (TwoPieceFourierAction.eta radius))

def contactPayment (c d : BurnolCompletedMellinCoordinate) : ℂ :=
  sourceTrace c 0*inner ℂ (w (barC d)) (contactDiagonal q)-
    (((p/q : ℝ) : ℂ)*sourceJump c 0)*inner ℂ (w (barC d)) (contactDiagonal p)+
    sourceTrace c 1*inner ℂ (w (barC d)) (contactCross q)-
    (((p/q : ℝ) : ℂ)*sourceJump c 1)*inner ℂ (w (barC d)) (contactCross p)

private theorem actual_contact_source (c : BurnolCompletedMellinCoordinate) :
    PsiDrive.contactV c=sourceTrace c 0 • contactDiagonal q-
      (((p/q : ℝ) : ℂ)*sourceJump c 0) • contactDiagonal p+
        sourceTrace c 1 • contactCross q-(((p/q : ℝ) : ℂ)*sourceJump c 1) • contactCross p := by
  unfold PsiDrive.contactV PsiDrive.contactU sourceContact contactDiagonal contactCross
  simp only [map_add,map_sub,map_smul]
  module

private theorem actual_contact_payment (c d : BurnolCompletedMellinCoordinate) :
    inner ℂ (w (barC d)) (PsiDrive.contactV c)=contactPayment c d := by
  rw [actual_contact_source]
  simp only [inner_sub_right,inner_add_right,inner_smul_right]
  rfl

/-- Only the fixed Psi sources and actual contact solve are read by this payment. -/
def psiPayment (c d : BurnolCompletedMellinCoordinate) : ℂ :=
  (-OriginalRieszSource.Kernel.A c)*inner ℂ (w (barC d)) PsiDrive.psiV+
    (-OriginalRieszSource.Kernel.beta c)*inner ℂ (w (barC d)) PsiDrive.psiU-
      contactPayment c d

def ordinaryMean (c : BurnolCompletedMellinCoordinate) : ℂ :=
  sourceTrace c 1-((p/q : ℝ) : ℂ)*sourceJump c 1

def endpointCharge (c d : BurnolCompletedMellinCoordinate) : ℂ :=
  2*(q : ℂ)^(star d.value)*sourceTrace c 1-2*(p : ℂ)^(star d.value)*sourceJump c 1

def powerUnitPrice (d : BurnolCompletedMellinCoordinate) : ℂ := 2*(q : ℂ)^(star d.value)/(star d.value)

/-- No original B pairing or target value enters this actual finite Psi/contact/mean calculation. -/
def nativeGamma (c d : BurnolCompletedMellinCoordinate) : ℂ :=
  2*psiPayment c d+2*ordinaryMean c*powerUnitPrice d-2*endpointCharge c d

private theorem exponent_positive (d : BurnolCompletedMellinCoordinate) : 0<(star d.value).re := by
  simpa only [Complex.star_def,Complex.conj_re] using lt_trans (by norm_num : (0 : ℝ)<1/2) d.rightHalf

private theorem exponent_ne_zero (d : BurnolCompletedMellinCoordinate) : star d.value≠0 := by
  intro zero
  have real:=congrArg Complex.re zero
  have positive:=exponent_positive d
  rw [real] at positive
  norm_num at positive

private theorem power_pair (d : BurnolCompletedMellinCoordinate) (value : Hq) (raw : ℝ → ℂ)
    (read : (value : ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval q)] raw)
    (even : ∀ x,raw (-x)=raw x) :
    IntervalIntegrable (fun x : ℝ=>(x : ℂ)^(star d.value-1)*raw x) volume 0 q ∧
      inner ℂ (W (barC d)) value=2*(∫ x : ℝ in 0..q,(x : ℂ)^(star d.value-1)*raw x) := by
  have native:=native_pair_integrable (W (barC d)) value _ _ (SingularCounting.power_coeFn (barC d)) read
  have positive : IntegrableOn (fun x : ℝ=>star (SingularCounting.powerRaw (barC d) x)*raw x) (Icc 0 q) :=
    native.mono_measure (Measure.restrict_mono (by change Icc 0 q ⊆ Icc (-q) q;exact Icc_subset_Icc (by norm_num) le_rfl) le_rfl)
  have same : (fun x : ℝ=>star (SingularCounting.powerRaw (barC d) x)*raw x)=ᵐ[volume.restrict (Icc 0 q)]
      (fun x : ℝ=>(x : ℂ)^(star d.value-1)*raw x) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with x inside nonzero
    rw [power_raw_weight (barC d) x (lt_of_le_of_ne inside.1 nonzero.symm)]
    rfl
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ)≤q)).mpr
    (positive.congr same),?_⟩
  rw [native_pair_read _ _ _ _ (SingularCounting.power_coeFn (barC d)) read,
    intervalIntegral.integral_of_le (by norm_num : -q≤q),←integral_Icc_eq_integral_Ioc]
  have half:=even_half_integral (fun x : ℝ=>star (SingularCounting.powerRaw (barC d) x)*raw x)
    native (fun x=>by rw [even];simp only [SingularCounting.powerRaw,abs_neg])
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤q)]
  exact half.trans (by
    simpa only [integral_Icc_eq_integral_Ioc] using congrArg (fun z : ℂ=>2*z) (integral_congr_ae same))

private theorem weighted_green (d : BurnolCompletedMellinCoordinate) (a b : ℝ)
    (nonnegative : 0≤a) (ordered : a≤b) (f df : ℝ → ℂ)
    (cf : ContinuousOn f (Icc a b)) (cdf : ContinuousOn df (Icc a b))
    (derivative : ∀ x∈Ioo a b,HasDerivAt f (df x) x) :
    (∫ x : ℝ in a..b,(x : ℂ)^(star d.value-1)*((x : ℂ)*df x+(1/2 : ℂ)*f x))=
      (b : ℂ)^(star d.value)*f b-(a : ℂ)^(star d.value)*f a+
        (1/2-star d.value)*(∫ x : ℝ in a..b,(x : ℂ)^(star d.value-1)*f x) := by
  have exponent : -1<(star d.value-1).re := by
    have positive:=exponent_positive d
    simp only [Complex.sub_re,Complex.one_re]
    linarith
  have weight : IntervalIntegrable (fun x : ℝ=>(x : ℂ)^(star d.value-1)) volume a b :=
    intervalIntegral.intervalIntegrable_cpow' exponent
  have ccast : ContinuousOn (fun x : ℝ=>(x : ℂ)) (Icc a b) := Complex.continuous_ofReal.continuousOn
  have bulkContinuous : ContinuousOn (fun x : ℝ=>(x : ℂ)*df x+(1/2 : ℂ)*f x) (Icc a b) :=
    (ccast.mul cdf).add (continuousOn_const.mul cf)
  have bulk:=weight.mul_continuousOn (by simpa only [uIcc_of_le ordered] using bulkContinuous)
  have price:=weight.mul_continuousOn (by simpa only [uIcc_of_le ordered] using cf)
  have regular : ContinuousOn (fun x : ℝ=>(x : ℂ)^(star d.value)*f x) (Icc a b) :=
    (Complex.continuous_ofReal_cpow_const (exponent_positive d)).continuousOn.mul cf
  have generated:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ordered regular
    (f':=fun x : ℝ=>(x : ℂ)^(star d.value-1)*((x : ℂ)*df x+(1/2 : ℂ)*f x)+
      (star d.value-1/2)*((x : ℂ)^(star d.value-1)*f x)) ?_ (bulk.add (price.const_mul _))
  · rw [intervalIntegral.integral_add bulk (price.const_mul _),intervalIntegral.integral_const_mul] at generated
    linear_combination generated
  · intro x inside
    have positive : 0<x := lt_of_le_of_lt nonnegative inside.1
    have actual:=(hasDerivAt_ofReal_cpow_const positive.ne' (exponent_ne_zero d)).mul (derivative x inside)
    have power : (x : ℂ)^(star d.value)=(x : ℂ)^(star d.value-1)*(x : ℂ) := by
      have add:=Complex.cpow_add (star d.value-1) 1 (Complex.ofReal_ne_zero.mpr positive.ne')
      simpa only [sub_add_cancel,Complex.cpow_one] using add
    convert! actual using 1
    rw [power]
    ring

private theorem power_centered (d : BurnolCompletedMellinCoordinate) (state : M) :
    inner ℂ (W (barC d)) (state : Hq)=inner ℂ (w (barC d)) state :=
  (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right state _).symm

private theorem source_green (c d : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    inner ℂ (W (barC d)) (sourceBulk c i)=
      (2*(q : ℂ)^(star d.value)*sourceTrace c i-2*(p : ℂ)^(star d.value)*sourceJump c i)+
        (1/2-star d.value)*inner ℂ (W (barC d)) (sourceCorrection c i : Hq) := by
  have bulk:=power_pair d (sourceBulk c i) (sourceBulkRaw c i) (source_bulk_read c i)
    (fun x=>by simp only [sourceBulkRaw,TwoPieceFourierAction.bulkRaw,TwoPieceFourierAction.pieceRaw,abs_neg])
  have price:=power_pair d (sourceCorrection c i : Hq) (sourceRaw c i) (source_correction_read c i)
    (fun x=>by simp only [sourceRaw,abs_neg])
  have first:=weighted_green d 0 p (by norm_num) junctionPoint_bounds.1.le
    (sourceInnerRaw c i) (sourceInnerSlope c i) (source_inner_continuousOn c i) (source_inner_slope_continuousOn c i)
    (fun x _=>source_inner_hasDerivAt c i x)
  have second:=weighted_green d p q junctionPoint_bounds.1.le junctionPoint_bounds.2.le
    (sourceOuterRaw c i) (sourceOuterSlope c i) (source_outer_continuousOn c i) (source_outer_slope_continuousOn c i)
    (fun x inside=>source_outer_hasDerivAt c i x inside.1)
  have restrict0 : uIcc 0 p ⊆ uIcc 0 q := by
    rw [uIcc_of_le junctionPoint_bounds.1.le,uIcc_of_le (by norm_num : (0 : ℝ)≤q)]
    exact Icc_subset_Icc le_rfl junctionPoint_bounds.2.le
  have restrict1 : uIcc p q ⊆ uIcc 0 q := by
    rw [uIcc_of_le junctionPoint_bounds.2.le,uIcc_of_le (by norm_num : (0 : ℝ)≤q)]
    exact Icc_subset_Icc junctionPoint_bounds.1.le le_rfl
  have b0:=bulk.1.mono_set restrict0
  have b1:=bulk.1.mono_set restrict1
  have p0:=price.1.mono_set restrict0
  have p1:=price.1.mono_set restrict1
  have rb0 : EqOn (fun x : ℝ=>(x : ℂ)^(star d.value-1)*sourceBulkRaw c i x)
      (fun x : ℝ=>(x : ℂ)^(star d.value-1)*((x : ℂ)*sourceInnerSlope c i x+(1/2 : ℂ)*sourceInnerRaw c i x)) (uIoo 0 p) := by
    rw [uIoo_of_le junctionPoint_bounds.1.le]
    intro x hx
    simp only [sourceBulkRaw,TwoPieceFourierAction.bulkRaw,TwoPieceFourierAction.pieceRaw,abs_of_pos hx.1,if_pos hx.2.le]
  have rb1 : EqOn (fun x : ℝ=>(x : ℂ)^(star d.value-1)*sourceBulkRaw c i x)
      (fun x : ℝ=>(x : ℂ)^(star d.value-1)*((x : ℂ)*sourceOuterSlope c i x+(1/2 : ℂ)*sourceOuterRaw c i x)) (uIoo p q) := by
    rw [uIoo_of_le junctionPoint_bounds.2.le]
    intro x hx
    simp only [sourceBulkRaw,TwoPieceFourierAction.bulkRaw,TwoPieceFourierAction.pieceRaw,abs_of_pos (junctionPoint_bounds.1.trans hx.1),if_neg hx.1.not_ge]
  have rp0 : EqOn (fun x : ℝ=>(x : ℂ)^(star d.value-1)*sourceRaw c i x)
      (fun x : ℝ=>(x : ℂ)^(star d.value-1)*sourceInnerRaw c i x) (uIoo 0 p) := by
    rw [uIoo_of_le junctionPoint_bounds.1.le]
    intro x hx
    simp only [sourceRaw,abs_of_pos hx.1,if_pos hx.2.le]
  have rp1 : EqOn (fun x : ℝ=>(x : ℂ)^(star d.value-1)*sourceRaw c i x)
      (fun x : ℝ=>(x : ℂ)^(star d.value-1)*sourceOuterRaw c i x) (uIoo p q) := by
    rw [uIoo_of_le junctionPoint_bounds.2.le]
    intro x hx
    simp only [sourceRaw,abs_of_pos (junctionPoint_bounds.1.trans hx.1),if_neg hx.1.not_ge]
  rw [bulk.2,price.2,←intervalIntegral.integral_add_adjacent_intervals b0 b1,
    ←intervalIntegral.integral_add_adjacent_intervals p0 p1,
    intervalIntegral.integral_congr_uIoo rb0,intervalIntegral.integral_congr_uIoo rb1,
    intervalIntegral.integral_congr_uIoo rp0,intervalIntegral.integral_congr_uIoo rp1,
    first,second,Complex.ofReal_zero,Complex.zero_cpow (exponent_ne_zero d),zero_mul,sub_zero]
  unfold sourceTrace
  linear_combination -2*(p : ℂ)^(star d.value)*(source_internal_jump c i)

private theorem power_constant (d : BurnolCompletedMellinCoordinate) :
    inner ℂ (W (barC d)) (intervalConstant q)=powerUnitPrice d := by
  have pair:=power_pair d (intervalConstant q) (fun _=>1) (intervalConstant_coeFn q) (fun _=>rfl)
  rw [pair.2]
  simp only [mul_one]
  rw [integral_cpow (Or.inl (by
    have positive:=exponent_positive d
    simp only [Complex.sub_re,Complex.one_re]
    linarith))]
  simp only [sub_add_cancel,Complex.ofReal_zero,Complex.zero_cpow (exponent_ne_zero d),sub_zero]
  unfold powerUnitPrice
  ring

private theorem force_payment (c d : BurnolCompletedMellinCoordinate) :
    inner ℂ (W (barC d)) (BandSourceAction.sourceForce c 1 : Hq)=psiPayment c d := by
  rw [power_centered]
  change inner ℂ (w (barC d)) ((-OriginalRieszSource.Kernel.A c) • PsiDrive.psiV+
    (-OriginalRieszSource.Kernel.beta c) • PsiDrive.psiU-PsiDrive.contactV c)=_
  simp only [inner_sub_right,inner_add_right,inner_smul_right]
  rw [actual_contact_payment]
  rfl

/-- The actual second-B Psi action pays the complete coefficient, including q trace, p jump and ordinary mean. -/
theorem actual_native_gamma (c d : BurnolCompletedMellinCoordinate) :
    nativeGamma c d=coefficient c d := by
  have source:=(PsiDrive.source_B_Psi_full_action c).2
  change sourceBulk c 1-(star c.value-1/2) • (sourceSecond c : Hq)=
    (BandSourceAction.sourceForce c 1 : Hq)+ordinaryMean c • intervalConstant q at source
  have paid:=congrArg (fun value : Hq=>inner ℂ (W (barC d)) value) source
  rw [inner_sub_right,inner_smul_right,inner_add_right,inner_smul_right,source_green,
    power_centered,force_payment,power_constant] at paid
  simp only [sourceCorrection,Matrix.cons_val_one,Matrix.cons_val_zero] at paid
  rw [power_centered] at paid
  change (endpointCharge c d+(1/2-star d.value)*finitePrice c d)-
    (star c.value-1/2)*finitePrice c d=psiPayment c d+ordinaryMean c*powerUnitPrice d at paid
  unfold nativeGamma coefficient sigma
  linear_combination -2*paid

/-- The same actual physical forcing input now consumes the source-calculated finite Psi payment. -/
theorem actual_calculated_input (c d : BurnolCompletedMellinCoordinate) :
    (closureInput c d : BurnolL2)=nativeGamma c d • fourierL2 (OriginalKSourceResolventReconstruction.generatedK d) := by
  rw [actual_native_gamma]
  exact actual_input c d

theorem actual_calculated_next (c d : BurnolCompletedMellinCoordinate) :
    OriginalWholeDebtRJointMobiusContactClosureSource.next c d=nativeGamma c d •
      OriginalKCrossParameterRAdjointSource.UnweightedCayleySource.sourceFKAction d := by
  rw [actual_native_gamma]
  exact actual_next c d

open OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKSourceResolventReconstruction
open OriginalWholeDebtRJointMobiusContactClosureConsumer

/-- The actual calculated coefficient updates the whole K/FK/B vector. -/
theorem actual_calculated_whole_next (c d : BurnolCompletedMellinCoordinate) :
    OriginalWholeDebtRJointMobiusContactClosureSource.next c d=nativeGamma c d •
      ((sourceForwardRatio d/(sourceDamping d : ℂ)) • generatedK (barC d)-
        (sourceDamping d : ℂ)⁻¹ • fourierL2 (generatedK d)-
        (2*((‖generatedK d‖^2 : ℝ) : ℂ)) • physicalOutsideColumn d) := by
  rw [actual_native_gamma]
  exact actual_whole_next c d

/-- The original coupled forcing consumes the finite source calculation with its literal coefficient. -/
theorem actual_calculated_contact_face (c : BurnolCompletedMellinCoordinate) :
    burnolEvenAmbientProjectionEndomorphism (OriginalWholeDebtRJointMobiusCoupledCayleySource.contactForcing c)=
      OriginalWholeDebtRJointMobiusCoupledCayleySource.coupling c •
        burnolEvenAmbientProjectionEndomorphism (OriginalWholeDebtRJointMobiusCoupledCayleySource.dualKernelBoundary c)+
      (OriginalWholeDebtRPowerWaveDilationSource.damping c : ℂ) •
        burnolEvenAmbientProjectionEndomorphism
          (OriginalWholeDebtRPowerWaveDilationSource.pairedSource c junctionShift)+
      (1/2 : ℂ) • (nativeGamma c (barC c) • fourierL2 (generatedK (barC c))) := by
  rw [actual_native_gamma]
  exact actual_coupled_contact_face c

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "b" => L.outsideCoefficient observation nontrivial half
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
local notation "Rpow" => CombSource.Division.rawIterate observation half.down
local notation "pi" => J.paJet observation nontrivial half m

/-- The same whole-loop cotest consumes the calculated source coefficient. -/
theorem actual_calculated_loop_cotest :
    inner ℂ (sourceEffect c c) (L.wholeLoop c)=(-1/2 : ℂ)*b*star (nativeGamma c c) := by
  rw [actual_loop_whole_cotest observation nontrivial half,actual_native_gamma]
  simp only [coefficient,star_mul,star_neg,star_ofNat]
  ring

/-- The independent actual exact-order Pa return reads the source-calculated forcing. -/
theorem actual_calculated_newPa_effect :
    inner ℂ (sourceEffect c c) (Rpow m (pi : BurnolL2))=
      star (nativeGamma c c)*J.feedback observation nontrivial half*e := by
  rw [actual_native_gamma]
  exact actual_newPa_finite_effect observation nontrivial half

/-- Its terminal-price zero question is now the finite actual Psi/contact/mean computation. -/
theorem actual_calculated_newPa_effect_zero_iff :
    inner ℂ (sourceEffect c c) (Rpow m (pi : BurnolL2))=0 ↔ nativeGamma c c=0 := by
  rw [actual_calculated_newPa_effect observation nontrivial half]
  have feedbackNe:=J.actual_feedback_ne_zero observation nontrivial half
  have eNe:=burnolAnalyticComplementExpectedPhysicalFourierRead_ne_zero observation nontrivial
  constructor
  · intro zero
    have pairZero:star (nativeGamma c c)*J.feedback observation nontrivial half=0 :=
      (mul_eq_zero.mp zero).resolve_right eNe
    have starredZero:star (nativeGamma c c)=0 := (mul_eq_zero.mp pairZero).resolve_right feedbackNe
    simpa only [star_eq_zero] using starredZero
  · intro zero
    simp only [zero,star_zero,zero_mul]

end OriginalWholeDebtRJointMobiusContactPsiPriceSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
