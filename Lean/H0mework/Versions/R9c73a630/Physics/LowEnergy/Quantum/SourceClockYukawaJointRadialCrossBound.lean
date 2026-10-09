import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaSpinNativeBudget
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialBoundaryBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaJointRadialCrossBound
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussNativePotential GaussRadialDomain GaussYukawaCoefficient GaussQuantumMultiplier GaussFockWeights
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourcePhysicalKineticSquare
open SourceClockYukawaTail SourceClockYukawaNormalizedCurrent SourceScalarPositiveBulkWard
open SourceLocalizedInverseFormPayment PositiveScalarWeakBudget PositiveScalarCoefficientDecay SourceRelativePowerTail SourceClockYukawaSpinNativeBudget
open SourceInverseNeutralSpinCurrent SourceClockYukawaRadialNativeBudget
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] state fullAction inverseRadius normalizedAction finiteResolvent sourceB constantBounded

private def peakCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  reciprocal z^2*SourceNativeCutoffContact.theta m ell z
private theorem peak_smooth (m ell : ℕ) : ContDiff ℝ ∞ (peakCoefficient m ell) :=
  (reciprocal_smooth.pow 2).mul (SourceNativeCutoffContact.theta_smooth m ell)

private theorem peak_bound (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) :
    |peakCoefficient m ell z| ≤ 1/(m+2:ℝ) := by
  have hs : 0 ≤ reciprocal z := (inv_pos.mpr (radius_pos z)).le
  have hs1 : reciprocal z ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius z)
  have hq : 0 ≤ 1-reciprocal z := sub_nonneg.mpr hs1
  have hq1 : 1-reciprocal z ≤ 1 := by linarith
  have hpow : (1-reciprocal z)^(ell+1) ≤ (1-reciprocal z)^(m+1) :=
    pow_le_pow_of_le_one hq hq1 (Nat.add_le_add_right hml 1)
  have hθ : 0 ≤ SourceNativeCutoffContact.theta m ell z := sub_nonneg.mpr hpow
  have hθu : SourceNativeCutoffContact.theta m ell z ≤ (1-reciprocal z)^(m+1) :=
    sub_le_self _ (pow_nonneg hq _)
  have hp := SourceNativeCutoffContact.squared_geometric_peak (reciprocal z) hs hs1 (m+1)
  have hd : 2/(m+3:ℝ) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0<(m+3:ℝ))).mpr
    have hm0 : 0 ≤ (m:ℝ) := by positivity
    linarith only [hm0]
  have hp' : reciprocal z^2*(1-reciprocal z)^(m+1) ≤ 1/(m+2:ℝ) := by
    apply (le_div_iff₀ (by positivity : 0<(m+2:ℝ))).mpr
    push_cast at hp
    have hd' : 2/((m:ℝ)+1+2) ≤ 1 := by convert hd using 1; ring
    nlinarith only [hp.trans hd']
  unfold peakCoefficient
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hθ)]
  exact (mul_le_mul_of_nonneg_left hθu (sq_nonneg _)).trans hp'

private def peakFiber (m ell : ℕ) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (peakCoefficient m ell z:ℂ) • ContinuousLinearMap.id ℂ FockFiber
private theorem peak_fiber_smooth (m ell : ℕ) : ContDiff ℝ ∞ (peakFiber m ell) :=
  (Complex.ofRealCLM.contDiff.comp (peak_smooth m ell)).smul contDiff_const
private theorem peak_weight (m ell : ℕ) (z : SourceCoordinateSlice) (w : ℕ → ℂ) :
    Commute (weight w) (peakFiber m ell z) :=
  (Commute.one_right (weight w)).smul_right _
private theorem peak_fiber_bound (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) (f : FockFiber) :
    ‖peakFiber m ell z f‖ ≤ (1/(m+2:ℝ))*‖f‖ := by
  change ‖(peakCoefficient m ell z:ℂ) • f‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (peak_bound m ell hml z) (norm_nonneg _)

private def peakRadius (m ell : ℕ) (hml : m ≤ ell) : Op :=
  GaussBoundedMultiplier.extension (peakFiber m ell) (fun _ => (peak_fiber_smooth m ell).contDiffAt)
    (fun z => peak_weight m ell z) (1/(m+2:ℝ)) (by positivity) (fun z => peak_fiber_bound m ell hml z)

private theorem peak_norm (m ell : ℕ) (hml : m ≤ ell) : ‖peakRadius m ell hml‖ ≤ 1/(m+2:ℝ) :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

private theorem inverse_power_apply (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((inverseAction^n) f) z=(reciprocal z:ℂ)^n • f z := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (reciprocal z:ℂ) • (((inverseAction^n) f) z)=_
    rw [ih,pow_succ',mul_smul]

private theorem theta_point (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    thetaAction m ell f z=(SourceNativeCutoffContact.theta m ell z:ℂ) • f z := by
  rw [thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  rfl

private theorem peak_core (m ell : ℕ) (hml : m ≤ ell) (f : QuantumTest) :
    peakRadius m ell hml (embed f)=embed ((inverseAction^2*thetaAction m ell) f) := by
  rw [peakRadius,GaussBoundedMultiplier.extension_core]
  congr 1
  apply DFunLike.ext
  intro z
  change (peakCoefficient m ell z:ℂ) • f z=((inverseAction^2) (thetaAction m ell f)) z
  rw [inverse_power_apply,theta_point]
  simp only [peakCoefficient,Complex.ofReal_mul,Complex.ofReal_pow,mul_smul]

private def firstCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  ((ell+1:ℝ)*(1-reciprocal z)^ell-(m+1:ℝ)*(1-reciprocal z)^m)*reciprocal z^2
private theorem first_smooth (m ell : ℕ) : ContDiff ℝ ∞ (firstCoefficient m ell) :=
  (((contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow ell)).sub
    (contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow m))).mul (reciprocal_smooth.pow 2))

private theorem first_bound (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) :
    |firstCoefficient m ell z| ≤ 4/(m+2:ℝ) := by
  have hs : 0 ≤ reciprocal z := (inv_pos.mpr (radius_pos z)).le
  have hs1 : reciprocal z ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius z)
  have hq : 0 ≤ 1-reciprocal z := sub_nonneg.mpr hs1
  have h₁ := SourceNativeCutoffContact.squared_geometric_peak (reciprocal z) hs hs1 ell
  have h₂ := SourceNativeCutoffContact.squared_geometric_peak (reciprocal z) hs hs1 m
  have hd : 2/(ell+2:ℝ) ≤ 2/(m+2:ℝ) := by gcongr
  have he : firstCoefficient m ell z=
      (ell+1:ℝ)*reciprocal z^2*(1-reciprocal z)^ell-
      (m+1:ℝ)*reciprocal z^2*(1-reciprocal z)^m := by unfold firstCoefficient;ring
  rw [he]
  calc
    _ ≤ |(ell+1:ℝ)*reciprocal z^2*(1-reciprocal z)^ell|+
        |(m+1:ℝ)*reciprocal z^2*(1-reciprocal z)^m| := abs_sub _ _
    _ ≤ 2/(ell+2:ℝ)+2/(m+2:ℝ) := by
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
      exact add_le_add h₁ h₂
    _ ≤ 4/(m+2:ℝ) := (add_le_add hd (le_refl _)).trans_eq (by ring)

private def realFiber (c : SourceCoordinateSlice → ℝ) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (c z:ℂ) • ContinuousLinearMap.id ℂ FockFiber
private theorem real_fiber_smooth (c : SourceCoordinateSlice → ℝ) (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (realFiber c) := (Complex.ofRealCLM.contDiff.comp hc).smul contDiff_const
private theorem real_fiber_weight (c : SourceCoordinateSlice → ℝ) (z : SourceCoordinateSlice) (w : ℕ → ℂ) :
    Commute (GaussFockWeights.weight w) (realFiber c z) := (Commute.one_right (GaussFockWeights.weight w)).smul_right _
private theorem real_fiber_bound (c : SourceCoordinateSlice → ℝ) (C : ℝ) (hb : ∀ z,|c z| ≤ C)
    (z : SourceCoordinateSlice) (f : FockFiber) : ‖realFiber c z f‖ ≤ C*‖f‖ := by
  change ‖(c z:ℂ) • f‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb z) (norm_nonneg _)

private def firstOp (m ell : ℕ) (hml : m ≤ ell) : Op :=
  GaussBoundedMultiplier.extension (realFiber (firstCoefficient m ell))
    (fun _ => (real_fiber_smooth _ (first_smooth m ell)).contDiffAt)
    (fun z => real_fiber_weight _ z) (4/(m+2:ℝ)) (by positivity)
    (fun z => real_fiber_bound _ _ (first_bound m ell hml) z)

private theorem first_norm (m ell : ℕ) (hml : m ≤ ell) : ‖firstOp m ell hml‖ ≤ 4/(m+2:ℝ) :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem first_core (m ell : ℕ) (hml : m ≤ ell) (f : QuantumTest) :
    firstOp m ell hml (embed f)=embed (multiply (firstCoefficient m ell)
      (fun _ => (first_smooth m ell).contDiffAt) f) := by
  rw [firstOp,GaussBoundedMultiplier.extension_core]
  rfl

private theorem inverse_pow_core (n : ℕ) (f : QuantumTest) :
    (inverseRadius^n) (embed f)=embed ((inverseAction^n) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change inverseRadius ((inverseRadius^n) (embed f))=_
    rw [ih,inverse_core]
    rfl

private theorem peak_return (m ell : ℕ) (hml : m ≤ ell) :
    peakRadius m ell hml=inverseRadius^2*relativeTail m ell := by
  apply GaussYukawaGrade.core_ext
  intro f
  rw [peak_core]
  simp only [mul_apply_eq_comp,SourceMixedNativeReturn.theta_core,inverse_pow_core,Module.End.mul_apply]

/-- The actual scalar window has an S² factor before taking its operator norm. -/
theorem original_inverse_square_theta_norm (m ell : ℕ) (hml : m ≤ ell) :
    ‖inverseRadius^2*relativeTail m ell‖ ≤ 1/(m+2:ℝ) := by
  rw [←peak_return m ell hml]
  exact peak_norm m ell hml

private theorem derivative_core (a : ScalarIndex) (f : QuantumTest) :
    inverseDerivative a (embed f)=embed (inverseDerivativeCore a f) := by
  simp only [inverseDerivative,inverseDerivativeCore,pow_two,mul_apply_eq_comp,Module.End.mul_apply,
    inverse_core,original_direction_core]

private def baseRow (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) (hml : m ≤ ell) : Op :=
  directionOperator a*peakRadius m ell hml*constantBounded sharp (scalarDirection a).1+
    directionOperator a^2*inverseRadius*firstOp m ell hml*sourceB sharp

private theorem direction_power_point (a : ScalarIndex) (n : ℕ) (f : QuantumTest)
    (z : SourceCoordinateSlice) : (directionAction a^n) f z=(directionWeight a z:ℂ)^n • f z := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (directionWeight a z:ℂ) • ((directionAction a^n) f z)=_
    rw [ih,pow_succ',mul_smul]
private theorem inverse_point (f : QuantumTest) (z : SourceCoordinateSlice) :
    inverseAction f z=(reciprocal z:ℂ) • f z := rfl
private theorem add_point (f g : QuantumTest) (z : SourceCoordinateSlice) :
    (f+g) z=f z+g z := rfl

private theorem base_row_return (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) (hml : m ≤ ell) :
    inverseDerivative a*boundedCoefficient sharp a m ell=baseRow sharp a m ell hml := by
  apply GaussYukawaGrade.core_ext
  intro f
  have hdir2 (q : QuantumTest) : (directionOperator a^2) (embed q)=embed ((directionAction a^2) q) := by
    simp only [pow_two,mul_apply_eq_comp,original_direction_core,Module.End.mul_apply]
  simp only [baseRow,mul_apply_eq_comp,add_apply,original_bounded_coefficient_core,derivative_core,
    constant_bounded_core,peak_core,original_direction_core,original_normalized_core,first_core,
    inverse_core,hdir2,←map_add]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  have ht := original_radial_derivative_peaks a m ell z
  have hs : directionWeight a z*((ell+1:ℝ)*reciprocal z*(1-reciprocal z)^ell-
      (m+1:ℝ)*reciprocal z*(1-reciprocal z)^m)*reciprocal z=
      SourceNativeCutoffContact.thetaDerivative (scalarDirection a) m ell z := by
    rw [←ht,reciprocal]
    field_simp [(radius_pos z).ne']
  rw [original_coefficient_split,add_point,direction_power_point]
  simp only [inverseDerivativeCore,Module.End.mul_apply,add_point,
    directionAction,multiply_apply,inverse_power_apply,theta_point,derivativeAction,
    SourceClockYukawaNormalizedCurrent.normalizedAction,inverse_point,firstCoefficient,smul_add,smul_smul]
  rw [←hs]
  push_cast
  module

private theorem inverse_norm : ‖inverseRadius‖ ≤ 1 := by
  unfold inverseRadius
  exact GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

private def rowPrice (sharp : Bool) (a : ScalarIndex) : ℝ :=
  (1/2)*‖constantBounded sharp (scalarDirection a).1‖+‖sourceB sharp‖

private theorem base_row_norm (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) (hml : m ≤ ell) :
    ‖inverseDerivative a*boundedCoefficient sharp a m ell‖ ≤ rowPrice sharp a/(m+2:ℝ) := by
  rw [base_row_return sharp a m ell hml]
  have hd := original_direction_norm a
  have hd2 : ‖directionOperator a^2‖ ≤ 1/4 := by
    rw [pow_two]
    exact (norm_mul_le _ _).trans (by nlinarith only [hd,norm_nonneg (directionOperator a)])
  have h1 := (norm_mul_le (directionOperator a*peakRadius m ell hml)
    (constantBounded sharp (scalarDirection a).1)).trans
    (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
      (mul_le_mul hd (peak_norm m ell hml) (norm_nonneg _) (by positivity))) (norm_nonneg _))
  have h2 := (norm_mul_le (directionOperator a^2*inverseRadius*firstOp m ell hml) (sourceB sharp)).trans
    (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
      (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul hd2 inverse_norm (norm_nonneg _) (by positivity)))
        (first_norm m ell hml) (norm_nonneg _) (by positivity))) (norm_nonneg _))
  unfold baseRow rowPrice
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

private theorem spin_core (j : Fin 4) (f : QuantumTest) :
    spinBounded j (embed f)=embed (activeSpin j f) := by
  unfold spinBounded
  exact GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f

private theorem derivative_spin (a : ScalarIndex) (j : Fin 4) :
    Commute (inverseDerivative a) (spinBounded j) := by
  apply GaussYukawaGrade.core_ext
  intro f
  simp only [mul_apply_eq_comp,spin_core,derivative_core]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  change (directionWeight a z:ℂ) • ((reciprocal z:ℂ) • ((reciprocal z:ℂ) •
    quantized (GaussCoframeSpin.full (activeIndex j)) (f z)))=
    quantized (GaussCoframeSpin.full (activeIndex j))
      ((directionWeight a z:ℂ) • ((reciprocal z:ℂ) • ((reciprocal z:ℂ) • f z)))
  simp only [map_smul]

private theorem left_bracket (D J A : Op) (h : Commute D J) :
    D*bracket J A=bracket J (D*A) := by
  unfold bracket
  have hc := congrArg (fun B : Op => B*A) h.eq
  simp only [mul_assoc] at hc
  simp only [mul_sub,mul_assoc,hc]

private theorem bracket_norm (J A : Op) : ‖bracket J A‖ ≤ 2*‖J‖*‖A‖ := by
  unfold bracket
  exact (norm_sub_le _ _).trans ((add_le_add (norm_mul_le J A) (norm_mul_le A J)).trans_eq (by ring))

private def jointFactor (mu : Fin 8) : ℝ :=
  if h0 : mu.val=0 then 1 else
  if h1 : mu.val<5 then 2*‖spinBounded ⟨mu.val-1,by omega⟩‖ else
    4*‖spinBounded ⟨mu.val-5,by omega⟩‖*‖spinBounded 3‖
private theorem factor_nonnegative (mu : Fin 8) : 0 ≤ jointFactor mu := by
  unfold jointFactor
  split
  · positivity
  · split <;> positivity

private theorem joint_row_norm (sharp : Bool) (mu : Fin 8) (a : ScalarIndex)
    (m ell : ℕ) (hml : m ≤ ell) :
    ‖inverseDerivative a*boundedJointCoefficient sharp mu a m ell‖ ≤
      jointFactor mu*rowPrice sharp a/(m+2:ℝ) := by
  have hbase := base_row_norm sharp a m ell hml
  unfold boundedJointCoefficient jointFactor
  split
  · simpa only [one_mul] using hbase
  · split
    · rw [left_bracket _ _ _ (derivative_spin a _)]
      exact (bracket_norm _ _).trans ((mul_le_mul_of_nonneg_left hbase (by positivity)).trans_eq (by ring))
    · rw [left_bracket _ _ _ (derivative_spin a _),left_bracket _ _ _ (derivative_spin a 3)]
      exact (bracket_norm _ _).trans ((mul_le_mul_of_nonneg_left
        ((bracket_norm _ _).trans (mul_le_mul_of_nonneg_left hbase (by positivity)))
          (by positivity)).trans_eq (by ring))

/-- The original fullX core has no external W or inverse-volume price. -/
def crossCore (sharp : Bool) (mu : Fin 8) (m ell : ℕ) : End :=
  ∑ a : ScalarIndex,inverseDerivativeCore a*jointCoefficient sharp mu a m ell

def crossBounded (sharp : Bool) (mu : Fin 8) (m ell : ℕ) : Op :=
  ∑ a : ScalarIndex,inverseDerivative a*boundedJointCoefficient sharp mu a m ell

def crossPrice (sharp : Bool) (mu : Fin 8) : ℝ :=
  ∑ a : ScalarIndex,jointFactor mu*rowPrice sharp a

/-- All eight closure coefficients return on the original QuantumTest carrier. -/
theorem original_cross_bounded_core (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (f : QuantumTest) :
    crossBounded sharp mu m ell (embed f)=embed (crossCore sharp mu m ell f) := by
  simp only [crossBounded,crossCore,sum_apply,LinearMap.sum_apply,
    mul_apply_eq_comp,Module.End.mul_apply,original_joint_coefficient_core,derivative_core,map_sum]

/-- Both boundary peaks and all seventy directions have an internally generated O(1/m) price. -/
theorem original_cross_norm (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (hml : m ≤ ell) :
    ‖crossBounded sharp mu m ell‖ ≤ crossPrice sharp mu/(m+2:ℝ) := by
  unfold crossBounded crossPrice
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun a _ => joint_row_norm sharp mu a m ell hml)).trans_eq
    (by rw [Finset.sum_div]))

private theorem cross_price_nonnegative (sharp : Bool) (mu : Fin 8) : 0 ≤ crossPrice sharp mu := by
  unfold crossPrice rowPrice
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (factor_nonnegative mu) (by positivity)

private def totalPrice : ℝ := ∑ sharp : Bool,∑ mu : Fin 8,(crossPrice sharp mu)^2
private theorem total_nonnegative : 0 ≤ totalPrice := by
  unfold totalPrice
  positivity
private theorem price_le_total (sharp : Bool) : (∑ mu : Fin 8,(crossPrice sharp mu)^2) ≤ totalPrice := by
  unfold totalPrice
  exact Finset.single_le_sum (fun s _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ sharp)

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem cross_state_bound (sharp : Bool) (m ell : ℕ) (hml : m ≤ ell)
    (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    (∑ mu : Fin 8,‖embed (crossCore sharp mu m ell (state F z hz g))‖^2) ≤
      (totalPrice/(m+2:ℝ)^2)*‖finiteResolvent F z (g:H)‖^2 := by
  simp_rw [←original_cross_bounded_core,state_embed]
  calc
    _ ≤ ∑ mu : Fin 8,(crossPrice sharp mu/(m+2:ℝ))^2*‖finiteResolvent F z (g:H)‖^2 := by
      apply Finset.sum_le_sum
      intro mu _
      have h := ((crossBounded sharp mu m ell).le_opNorm (finiteResolvent F z (g:H))).trans
        (mul_le_mul_of_nonneg_right (original_cross_norm sharp mu m ell hml) (norm_nonneg _))
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ((∑ mu : Fin 8,(crossPrice sharp mu)^2)/(m+2:ℝ)^2)*‖finiteResolvent F z (g:H)‖^2 := by
      simp only [div_pow,←Finset.sum_mul,←Finset.sum_div]
    _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (price_le_total sharp) (by positivity)) (sq_nonneg _)

/-- The small source operator pays the full-frequency state leg for all F and both branches at one N. -/
theorem actual_joint_cross_common_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,∀ sharp : Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (∑ mu : Fin 8,‖embed (crossCore sharp mu m ell
        (state F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := totalPrice*(Real.pi/μ*‖(g:H)‖^2)
  have hC : 0 ≤ C := mul_nonneg total_nonnegative (by positivity)
  obtain ⟨N,hN⟩ := exists_nat_gt (C/ε)
  refine ⟨N,fun m hm ell hml F sharp => ?_⟩
  have hden : 0<(m+2:ℝ) := by positivity
  have hN' : C/ε<(m:ℝ)+2 := by
    have hm' : (N:ℝ) ≤ m := by exact_mod_cast hm
    linarith only [hN,hm']
  have htail : (totalPrice/(m+2:ℝ)^2)*(Real.pi/μ*‖(g:H)‖^2) ≤ ε := by
    have hlin : C<ε*((m:ℝ)+2) := by simpa only [mul_comm] using (div_lt_iff₀ hε).mp hN'
    have hd2 : (m+2:ℝ) ≤ (m+2:ℝ)^2 := by
      have hm0 : (0:ℝ) ≤ m := by positivity
      nlinarith only [hm0]
    have hsq := mul_le_mul_of_nonneg_left hd2 hε.le
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    change C ≤ _
    linarith only [hlin,hsq]
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (totalPrice/(m+2:ℝ)^2)*
        ENNReal.ofReal (‖finiteResolvent F (line μ w) (g:H)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul (div_nonneg total_nonnegative (sq_nonneg _))]
      exact ENNReal.ofReal_le_ofReal (cross_state_bound sharp m ell hml F (line μ w)
        (by simpa only [line_im] using hμ.ne') g)
    _ = ENNReal.ofReal (totalPrice/(m+2:ℝ)^2)*ENNReal.ofReal (Real.pi/μ*‖(g:H)‖^2) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      simpa only [line,mul_comm (μ:ℂ) Complex.I] using SourceActualResolventEnergy.actual_square_lintegral F μ hμ (g:H)
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul (div_nonneg total_nonnegative (sq_nonneg _))]
      exact ENNReal.ofReal_le_ofReal htail

end LowEnergy.SourceClockYukawaJointRadialCrossBound
