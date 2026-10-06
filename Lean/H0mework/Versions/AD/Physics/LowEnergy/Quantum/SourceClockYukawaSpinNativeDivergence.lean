import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaSpinNativeJet
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaSpinNativeBudget
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaRadialNativeDivergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaSpinNativeDivergence
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussQuantumMultiplier
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourcePhysicalKineticSquare
open PositiveScalarWeakBudget PositiveScalarCoefficientDecay SourceLocalizedInverseFormPayment
open SourceClockYukawaSpinClosure SourceClockYukawaSpinNativeJet SourceInverseNeutralSpinCurrent
open SourceClockYukawaSpinNativeBudget SourceClockYukawaRadialNativeBudget
open SourceNativeCutoffContact SourceScalarGaugeForce SourceYukawaCoefficientCommutator
open scoped ContDiff InnerProductSpace BigOperators
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] fullAction compressionCore defectAction

private def ad (J : End) : End →ₗ[ℂ] End where
  toFun A := bracket J A
  map_add' A B := by unfold bracket;noncomm_ring
  map_smul' c A := by simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

private def recipe (mu : Fin 8) : End →ₗ[ℂ] End :=
  if h0 : mu.val=0 then LinearMap.id else
  if h1 : mu.val<5 then ad (activeSpin ⟨mu.val-1,by omega⟩) else
    (ad (activeSpin ⟨mu.val-5,by omega⟩)).comp (ad (activeSpin 3))

private theorem ad_bimodule (J L A R : End) (hL : Commute J L) (hR : Commute J R) :
    bracket J (L*A*R)=L*bracket J A*R := by
  unfold bracket
  linear_combination (norm := noncomm_ring) hL.eq*A*R+L*A*hR.eq

private theorem recipe_bimodule (mu : Fin 8) (L A R : End)
    (hL : ∀ j : Fin 4,Commute (activeSpin j) L)
    (hR : ∀ j : Fin 4,Commute (activeSpin j) R) :
    recipe mu (L*A*R)=L*recipe mu A*R := by
  unfold recipe
  split_ifs with h0 h1
  · rfl
  · exact ad_bimodule _ _ _ _ (hL _) (hR _)
  · change bracket _ (bracket _ (L*A*R))=L*bracket _ (bracket _ A)*R
    rw [ad_bimodule _ _ _ _ (hL 3) (hR 3),ad_bimodule _ _ _ _ (hL _) (hR _)]

private theorem recipe_left (mu : Fin 8) (L A : End) (hL : ∀ j : Fin 4,Commute (activeSpin j) L) :
    recipe mu (L*A)=L*recipe mu A := by
  simpa only [mul_one] using recipe_bimodule mu L A 1 hL (fun _ => Commute.one_right _)
private theorem recipe_right (mu : Fin 8) (A R : End) (hR : ∀ j : Fin 4,Commute (activeSpin j) R) :
    recipe mu (A*R)=recipe mu A*R := by
  simpa only [one_mul] using recipe_bimodule mu 1 A R (fun _ => Commute.one_right _) hR
private theorem recipe_bracket (mu : Fin 8) (P A : End) (hP : ∀ j : Fin 4,Commute (activeSpin j) P) :
    bracket P (recipe mu A)=recipe mu (bracket P A) := by
  simp only [bracket,map_sub,recipe_left mu P A hP,recipe_right mu A P hP]

private theorem recipe_commute (mu : Fin 8) (A B : End)
    (hB : ∀ j : Fin 4,Commute (activeSpin j) B) (hA : Commute B A) : Commute B (recipe mu A) := by
  apply sub_eq_zero.mp
  change bracket B (recipe mu A)=0
  rw [recipe_bracket mu B A hB,show bracket B A=0 from sub_eq_zero.mpr hA.eq,map_zero]

private theorem real_spin (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (j : Fin 4) :
    Commute (activeSpin j) (multiply c hc) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (quantized (GaussCoframeSpin.full (activeIndex j))) (c z:ℂ) (f z)
private theorem real_real (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val) : Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z:ℂ) (d z:ℂ) (f z)
private theorem real_full (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (fullAction sharp) := by
  unfold fullAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases sharp
  · exact (map_smul (sourceMap (scalarField z)) (c z:ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z)) (c z:ℂ) (f z)).symm
private theorem real_constant (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) (v : Scalar) :
    Commute (multiply c hc) (constantAction sharp v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (branchMap sharp v) (c z:ℂ) (f z)).symm
private theorem real_theta (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (m ell : ℕ) :
    Commute (multiply c hc) (SourceMixedNativeReturn.thetaAction m ell) := by
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  exact real_real _ _ _ _
private theorem real_contact (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (v : Ambient) (m ell : ℕ) :
    Commute (multiply c hc) (SourceNativeCutoffContact.contactAction v m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z:ℂ) ((-Complex.I)*(SourceNativeCutoffContact.thetaDerivative v m ell z:ℂ)) (f z)
private theorem real_coefficient (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) :
    Commute (multiply c hc) (coefficient sharp a m ell) := by
  unfold coefficient
  exact ((real_constant c hc sharp (scalarDirection a).1).mul_right (real_theta c hc m ell)).add_right
    (((real_full c hc sharp).mul_right (real_contact c hc (scalarDirection a) m ell)).smul_right Complex.I)

private theorem coefficient_recipe (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) (m ell : ℕ) :
    jointCoefficient sharp mu a m ell=recipe mu (coefficient sharp a m ell) := by
  unfold jointCoefficient recipe
  split_ifs <;> rfl
private theorem cutoff_recipe (sharp : Bool) (mu : Fin 8) (m ell : ℕ) :
    SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu=
      recipe mu (fullAction sharp*SourceMixedNativeReturn.thetaAction m ell) := by
  have hs : spinClosureCoefficient sharp mu=recipe mu (fullAction sharp) := by
    unfold spinClosureCoefficient SourceClockYukawaSpinRelativeForm.spinCoefficient recipe
    split_ifs <;> rfl
  unfold SourceClockYukawaSpinJointForce.cutoffCore
  rw [hs,recipe_right]
  intro j
  rw [SourceMixedNativeReturn.thetaAction,←theta_action_polynomial]
  exact real_spin _ _ j
private theorem real_cutoff (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) (mu : Fin 8) (m ell : ℕ) :
    Commute (multiply c hc) (SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu) := by
  rw [cutoff_recipe]
  exact recipe_commute mu _ _ (real_spin c hc) ((real_full c hc sharp).mul_right (real_theta c hc m ell))
private theorem real_joint (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) (m ell : ℕ) :
    Commute (multiply c hc) (jointCoefficient sharp mu a m ell) := by
  rw [coefficient_recipe]
  exact recipe_commute mu _ _ (real_spin c hc) (real_coefficient c hc sharp a m ell)

private theorem native_joined (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) :
    bracket (covariantMomentum (scalarDirection a)) (fullAction sharp*SourceMixedNativeReturn.thetaAction m ell)=
      (-Complex.I) • coefficient sharp a m ell := by
  have hy := original_spin_closure_native_jet sharp 0 (scalarDirection a)
  change bracket (covariantMomentum (scalarDirection a)) (fullAction sharp)=
    (-Complex.I) • constantAction sharp (scalarDirection a).1 at hy
  have ht : bracket (covariantMomentum (scalarDirection a)) (SourceMixedNativeReturn.thetaAction m ell)=
      SourceNativeCutoffContact.contactAction (scalarDirection a) m ell := by
    apply LinearMap.ext
    intro f
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply]
    rw [SourceMixedNativeReturn.thetaAction,←theta_action_polynomial,native_core_contact,add_sub_cancel_left]
  have hp (P A B : End) : bracket P (A*B)=bracket P A*B+A*bracket P B := by unfold bracket;noncomm_ring
  rw [hp,hy,ht]
  have hi : (-Complex.I)*Complex.I=1 := by rw [neg_mul,Complex.I_mul_I,neg_neg]
  simp only [coefficient,smul_add,smul_mul_assoc,smul_smul,hi,one_smul]
private theorem adjoint_joined (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) :
    bracket (GaussMomentumAdjoint.adjoint (scalarDirection a)) (fullAction sharp*SourceMixedNativeReturn.thetaAction m ell)=
      (-Complex.I) • coefficient sharp a m ell := by
  have hy := original_spin_closure_adjoint_native_jet sharp 0 (scalarDirection a)
  change bracket (GaussMomentumAdjoint.adjoint (scalarDirection a)) (fullAction sharp)=
    (-Complex.I) • constantAction sharp (scalarDirection a).1 at hy
  have ht : bracket (GaussMomentumAdjoint.adjoint (scalarDirection a)) (SourceMixedNativeReturn.thetaAction m ell)=
      SourceNativeCutoffContact.contactAction (scalarDirection a) m ell := by
    apply LinearMap.ext
    intro f
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply]
    rw [SourceMixedNativeReturn.thetaAction,←theta_action_polynomial,sharp_core_contact,add_sub_cancel_left]
  have hp (P A B : End) : bracket P (A*B)=bracket P A*B+A*bracket P B := by unfold bracket;noncomm_ring
  rw [hp,hy,ht]
  have hi : (-Complex.I)*Complex.I=1 := by rw [neg_mul,Complex.I_mul_I,neg_neg]
  simp only [coefficient,smul_add,smul_mul_assoc,smul_smul,hi,one_smul]
private theorem native_joint (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) (m ell : ℕ) :
    bracket (covariantMomentum (scalarDirection a)) (SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu)=
      (-Complex.I) • jointCoefficient sharp mu a m ell := by
  rw [cutoff_recipe,recipe_bracket mu _ _ (fun j => original_spin_native_commute (activeIndex j) _),
    native_joined,map_smul,←coefficient_recipe]
private theorem adjoint_joint (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) (m ell : ℕ) :
    bracket (GaussMomentumAdjoint.adjoint (scalarDirection a)) (SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu)=
      (-Complex.I) • jointCoefficient sharp mu a m ell := by
  rw [cutoff_recipe,recipe_bracket mu _ _ (fun j => original_spin_adjoint_native_commute (activeIndex j) _),
    adjoint_joined,map_smul,←coefficient_recipe]

private theorem sandwich_current (P A W X Z : End)
    (hP : bracket P X=(-Complex.I) • Z) (hA : bracket A X=(-Complex.I) • Z) (hw : Commute W X) :
    bracket (A*(W*P)) X=(-Complex.I) • (A*W*Z+Z*W*P) := by
  have he : bracket (A*(W*P)) X=A*W*bracket P X+bracket A X*W*P := by
    unfold bracket
    linear_combination (norm := noncomm_ring) A*hw.eq*P
  rw [he,hP,hA]
  simp only [mul_smul_comm,smul_mul_assoc,smul_add,mul_assoc]

/-- The all-eight scalar70 source current retains both original native momentum halves. -/
def jointScalarCurrent (sharp : Bool) (mu : Fin 8) (m ell : ℕ) : End := (-Complex.I/2:ℂ) • ∑ a : ScalarIndex,
  (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*jointCoefficient sharp mu a m ell+
    jointCoefficient sharp mu a m ell*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a))

theorem original_joint_scalar_source (sharp : Bool) (mu : Fin 8) (m ell : ℕ) :
    bracket scalarKinetic (SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu)=jointScalarCurrent sharp mu m ell := by
  have h (a : ScalarIndex) := sandwich_current (covariantMomentum (scalarDirection a))
    (GaussMomentumAdjoint.adjoint (scalarDirection a)) (multiply scalarWeight scalarWeight_smooth)
    (SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu) (jointCoefficient sharp mu a m ell)
    (native_joint sharp mu a m ell) (adjoint_joint sharp mu a m ell) (real_cutoff _ _ sharp mu m ell)
  unfold scalarKinetic jointScalarCurrent sandwich
  simp only [←Module.End.mul_eq_comp,bracket,smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum,
    ←Finset.sum_sub_distrib,←smul_sub]
  have he := Finset.sum_congr (s₁ := Finset.univ) rfl (fun a _ => h a)
  simp only [bracket] at he
  rw [he,←Finset.smul_sum,smul_smul]
  congr 1
  ring

private theorem inverse_derivative (a : ScalarIndex) :
    GaussRadialMomentum.commutatorAction (scalarDirection a)=(-Complex.I) • inverseDerivativeCore a := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (-Complex.I*(GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ)) • f z=
    (-Complex.I) • (directionAction a ((inverseAction^2) f)) z
  rw [pow_two]
  change _=(-Complex.I) • ((directionWeight a z:ℂ) • ((reciprocal z:ℂ) • ((reciprocal z:ℂ) • f z)))
  simp only [smul_smul]
  congr 1
  unfold GaussRadialMomentum.radialDerivative directionWeight reciprocal
  push_cast
  field_simp [(show (radius z:ℂ)≠0 by exact_mod_cast (radius_pos z).ne')]
  rfl
private theorem radial_native_form : GaussRadialHamiltonian.radialAction=(-Complex.I/2:ℂ) • ∑ a : ScalarIndex,
    (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*inverseDerivativeCore a+
      inverseDerivativeCore a*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)) := by
  simp only [GaussRadialHamiltonian.radialAction,GaussRadialHamiltonian.radialTerm,←Module.End.mul_eq_comp,inverse_derivative,
    mul_smul_comm,smul_mul_assoc,←smul_add,←Finset.smul_sum,smul_smul,mul_assoc]
  congr 1
  ring
private theorem direction_smooth (a : ScalarIndex) : ContDiff ℝ ∞ (directionWeight a) :=
  ((GaussRadialMomentum.scalarCoordinate.contDiff.inner ℝ contDiff_const).neg).div
    (contDiff_const.mul radius_smooth) (fun z => mul_ne_zero (by norm_num) (radius_pos z).ne')
private theorem derivative_real (a : ScalarIndex) : inverseDerivativeCore a=
    multiply (fun z => directionWeight a z*reciprocal z^2)
      (fun _ => (direction_smooth a).contDiffAt.mul (reciprocal_smooth.pow 2).contDiffAt) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  rw [SourceClockYukawaRadialNativeBudget.inverseDerivativeCore,pow_two]
  change (directionWeight a z:ℂ) • ((reciprocal z:ℂ) • ((reciprocal z:ℂ) • f z))=_
  simp only [multiply_apply,smul_smul,Complex.ofReal_mul,pow_two]

/-- The literal mixed scalar contact retains the true radial derivative and the joined eight-coefficient Z. -/
def jointCross (sharp : Bool) (mu : Fin 8) (m ell : ℕ) : End :=
  -(∑ a : ScalarIndex,multiply scalarWeight scalarWeight_smooth*inverseDerivativeCore a*jointCoefficient sharp mu a m ell)

private theorem cross_row (P B W d X Z : End)
    (hP : bracket P X=(-Complex.I) • Z) (hB : bracket B X=(-Complex.I) • Z)
    (hW : Commute W X) (hd : Commute d X) (hWd : Commute W d)
    (hWZ : Commute W Z) (hdZ : Commute d Z) :
    bracket (B*W*d+d*W*P) X=(-2*Complex.I:ℂ) • (W*d*Z) := by
  have hp (A B X : End) : bracket (A*B) X=A*bracket B X+bracket A X*B := by unfold bracket;noncomm_ring
  have ha (A B X : End) : bracket (A+B) X=bracket A X+bracket B X := by unfold bracket;noncomm_ring
  have hw : bracket W X=0 := sub_eq_zero.mpr hW.eq
  have hh : bracket d X=0 := sub_eq_zero.mpr hd.eq
  rw [ha,hp,hp,hp,hp,hw,hh,hP,hB]
  simp only [mul_zero,zero_mul,zero_add,add_zero,mul_smul_comm,smul_mul_assoc]
  have h : Z*W*d=W*d*Z := by
    rw [hWZ.eq.symm,mul_assoc,hdZ.eq.symm,←mul_assoc]
  have h2 : d*W*Z=W*d*Z := by rw [hWd.eq]
  rw [h,h2]
  module

theorem original_joint_radial_cross (sharp : Bool) (mu : Fin 8) (m ell : ℕ) :
    bracket GaussRadialHamiltonian.radialAction (SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu)=jointCross sharp mu m ell := by
  rw [radial_native_form]
  have hs : bracket ((-Complex.I/2:ℂ) • ∑ a : ScalarIndex,
      (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*inverseDerivativeCore a+
      inverseDerivativeCore a*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)))
      (SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu)=
    (-Complex.I/2:ℂ) • ∑ a : ScalarIndex,bracket
      (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*inverseDerivativeCore a+
      inverseDerivativeCore a*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a))
      (SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu) := by
    simp only [bracket,smul_mul_assoc,mul_smul_comm,←smul_sub,Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]
  rw [hs]
  have hr (a : ScalarIndex) : bracket
      (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*inverseDerivativeCore a+
      inverseDerivativeCore a*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a))
      (SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu)=
        (-2*Complex.I:ℂ) • (multiply scalarWeight scalarWeight_smooth*inverseDerivativeCore a*jointCoefficient sharp mu a m ell) := by
    apply cross_row
    · exact native_joint sharp mu a m ell
    · exact adjoint_joint sharp mu a m ell
    · exact real_cutoff _ _ sharp mu m ell
    · rw [derivative_real]
      exact real_cutoff _ _ sharp mu m ell
    · rw [derivative_real]
      exact real_real _ _ _ _
    · exact real_joint _ _ sharp mu a m ell
    · rw [derivative_real]
      exact real_joint _ _ sharp mu a m ell
  simp_rw [hr]
  rw [←Finset.smul_sum,smul_smul]
  have hc : (-Complex.I/2:ℂ)*(-2*Complex.I)= -1 := by
    calc
      _=Complex.I*Complex.I := by ring
      _= -1 := Complex.I_mul_I
  rw [hc,neg_one_smul]
  rfl

/-- Each local covariant/density source coefficient uses the same complete eight-spin recipe. -/
def jointZeroCore (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) (m ell : ℕ) : End :=
  recipe mu (SourceClockYukawaRadialNativeDivergence.joinedZeroCore sharp a m ell)

private theorem joint_zero_return (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) (m ell : ℕ) :
    jointCoefficient sharp mu a m ell*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)-
      GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*jointCoefficient sharp mu a m ell=
        jointZeroCore sharp mu a m ell := by
  have h := congrArg (recipe mu) (SourceClockYukawaRadialNativeDivergence.original_joined_native_divergence sharp a m ell)
  change recipe mu (coefficient sharp a m ell*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)-
    GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*coefficient sharp a m ell)=_ at h
  have hP (j : Fin 4) : Commute (activeSpin j) (multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)) :=
    (real_spin _ _ j).mul_right (original_spin_native_commute (activeIndex j) _)
  have hB (j : Fin 4) : Commute (activeSpin j) (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth) :=
    (original_spin_adjoint_native_commute (activeIndex j) _).mul_right (real_spin _ _ j)
  have ha : coefficient sharp a m ell*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)=
      coefficient sharp a m ell*(multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)) := mul_assoc _ _ _
  rw [ha,map_sub,recipe_right mu _ _ hP,recipe_left mu _ _ hB] at h
  simpa only [←coefficient_recipe,←mul_assoc,jointZeroCore] using h

/-- All seventy native coefficients enter the same original adjoint and paid G8 carrier. -/
def nativeDivergenceWord (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (rS rA : QuantumTest) : QuantumTest :=
  (-Complex.I) • ∑ a : ScalarIndex,GaussMomentumAdjoint.adjoint (scalarDirection a)
    (multiply scalarWeight scalarWeight_smooth (jointCoefficient sharp mu a m ell rS+inverseDerivativeCore a rA))

/-- The full scalar local word retains the actual covariant jet, density transpose and mixed product. -/
def scalarZeroOrderWord (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (rS rA q : QuantumTest) : QuantumTest :=
  (-Complex.I/2:ℂ) • (∑ a : ScalarIndex,
    (jointZeroCore sharp mu a m ell rS+SourceClockYukawaRadialNativeDivergence.inverseZeroCore a rA))+
  ∑ a : ScalarIndex,multiply scalarWeight scalarWeight_smooth (inverseDerivativeCore a (jointCoefficient sharp mu a m ell q))

theorem original_joint_scalar_forcing (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (rS rA q : QuantumTest) :
    jointScalarCurrent sharp mu m ell rS+GaussRadialHamiltonian.radialAction rA-jointCross sharp mu m ell q=
      nativeDivergenceWord sharp mu m ell rS rA+scalarZeroOrderWord sharp mu m ell rS rA q := by
  have hz : (∑ a : ScalarIndex,
      ((jointCoefficient sharp mu a m ell*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)) rS-
      (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*jointCoefficient sharp mu a m ell) rS))=
        ∑ a : ScalarIndex,jointZeroCore sharp mu a m ell rS := by
    apply Finset.sum_congr rfl
    intro a _
    exact LinearMap.congr_fun (joint_zero_return sharp mu a m ell) rS
  have hd : (∑ a : ScalarIndex,
      ((inverseDerivativeCore a*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)) rA-
      (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*inverseDerivativeCore a) rA))=
        ∑ a : ScalarIndex,SourceClockYukawaRadialNativeDivergence.inverseZeroCore a rA := by
    apply Finset.sum_congr rfl
    intro a _
    exact LinearMap.congr_fun (SourceClockYukawaRadialNativeDivergence.original_inverse_native_divergence a) rA
  simp only [Module.End.mul_apply,Finset.sum_sub_distrib] at hz hd
  simp only [jointScalarCurrent,radial_native_form,nativeDivergenceWord,jointCross,scalarZeroOrderWord,
    LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.add_apply,LinearMap.neg_apply,
    Module.End.mul_apply,map_add,Finset.sum_add_distrib]
  linear_combination (norm := module) (-Complex.I/2:ℂ) • hz+(-Complex.I/2:ℂ) • hd

/-- The scalar department keeps all three actual compression defects in its same-source forcing. -/
theorem actual_joint_scalar_forcing (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (F : Index) (rS rA q : QuantumTest) :
    (jointScalarCurrent sharp mu m ell-bracket (defectAction F) (SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu)) rS+
      SourceRadiusResponseDecay.radialCurrent F rA-
      (jointCross sharp mu m ell-bracket (bracket (defectAction F) inverseAction)
        (SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu)) q=
      nativeDivergenceWord sharp mu m ell rS rA+scalarZeroOrderWord sharp mu m ell rS rA q-
        bracket (defectAction F) (SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu) rS-
        bracket (defectAction F) inverseAction rA+
        bracket (bracket (defectAction F) inverseAction) (SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu) q := by
  have h := original_joint_scalar_forcing sharp mu m ell rS rA q
  simp only [SourceRadiusResponseDecay.radialCurrent,bracket,LinearMap.sub_apply] at *
  linear_combination (norm := module) h

end LowEnergy.SourceClockYukawaSpinNativeDivergence
