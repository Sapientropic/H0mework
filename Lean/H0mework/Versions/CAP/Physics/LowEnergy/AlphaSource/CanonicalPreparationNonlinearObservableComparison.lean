import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationNonlinearWeightedCurve

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNonlinearLaplace
open SourceFiniteUnitary CanonicalGradedVariation PreparationVacuumFieldPerturbation
open PreparationVacuumDampedFieldPerturbation PreparationVacuumNonlinearFieldCurve
open PreparationVacuumCausalFieldResponse PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open GaussCoreHilbert CanonicalPhysicalSpatial FullYSourceCutoffVolterra GaussUnitaryHistory
open CanonicalGradedSpatialSource MeasureTheory Set Filter
open scoped Topology Interval
local instance : NormedAlgebra ℚ PreparationVacuumFieldPerturbation.Op := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ PreparationVacuumFieldPerturbation.Op := NormedAlgebra.restrictScalars ℝ ℂ _

section Product
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _

theorem product_difference (U U0 V V0 A A0 : E →L[ℂ] E) :
    U*A*V-U0*A0*V0=(U-U0)*A*V+U0*(A-A0)*V+U0*A0*(V-V0) := by
  simp only [sub_mul,mul_sub,mul_assoc]
  abel

theorem product_difference_bound (U U0 V V0 A A0 : E →L[ℂ] E) (P a d e : ℝ)
    (hP : 0 ≤ P) (ha : 0 ≤ a) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hU : ‖U0‖≤P) (hV : ‖V‖≤P) (hA : ‖A‖≤a) (hA0 : ‖A0‖≤a)
    (hUd : ‖U-U0‖≤d) (hVd : ‖V-V0‖≤d) (hAd : ‖A-A0‖≤e) :
    ‖U*A*V-U0*A0*V0‖ ≤ 2*d*a*P+P^2*e := by
  have bound (X Y Z : E →L[ℂ] E) (x y z : ℝ)
      (hx : 0 ≤ x) (hy : 0 ≤ y) (hX : ‖X‖≤x) (hY : ‖Y‖≤y) (hZ : ‖Z‖≤z) :
      ‖X*Y*Z‖≤x*y*z :=
    (norm_mul_le _ _).trans (mul_le_mul
      ((norm_mul_le _ _).trans (mul_le_mul hX hY (norm_nonneg _) hx)) hZ (norm_nonneg _) (mul_nonneg hx hy))
  rw [product_difference]
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add (bound _ _ _ d a P hd ha hUd hA hV)
      (bound _ _ _ P e P hP he hU hAd hV))
      (bound _ _ _ P a d hP ha hU hA0 hVd)).trans_eq (by ring))
end Product

def readerSize (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) : ℝ :=
  ‖localizedGauss f p phi‖+‖contactGauss f g p (contactLocalizer phi psi)‖+readerSecondBound f g phi psi p

theorem readerSize_nonneg (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) :
    0 ≤ readerSize f g phi psi p := by
  unfold readerSize
  exact add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
    (readerSecondBound_nonneg f g phi psi p)

theorem actual_reader_size (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r|≤fieldRadius g psi) (unit : |r|≤1) :
    ‖actualReaderCurve f g phi psi p r‖ ≤ readerSize f g phi psi p := by
  have hm:=readerSecondBound_nonneg f g phi psi p
  have h:=readerIncrement_remainder f g phi psi p r small
  have identity : readerIncrement f g phi psi p r=
      (readerIncrement f g phi psi p r-r • contactGauss f g p (contactLocalizer phi psi))+
        r • contactGauss f g p (contactLocalizer phi psi) := by abel
  have quadratic : ‖r‖^2≤1 := by rw [Real.norm_eq_abs];nlinarith [abs_nonneg r]
  have middle : ‖readerIncrement f g phi psi p r‖≤readerSecondBound f g phi psi p+
      ‖contactGauss f g p (contactLocalizer phi psi)‖ := by
    rw [identity]
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    exact add_le_add
      (h.trans ((mul_le_mul_of_nonneg_left quadratic (readerSecondBound_nonneg f g phi psi p)).trans_eq (mul_one _)))
      ((mul_le_mul_of_nonneg_right unit (norm_nonneg _)).trans_eq (one_mul _))
  exact (norm_add_le _ _).trans ((add_le_add le_rfl middle).trans_eq (by unfold readerSize;ring))

def actualObservable (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (r t : ℝ) : PreparationVacuumFieldPerturbation.Op :=
  time (compression p F+cutoff cut+matterIncrement g psi p r) (-t)*actualReaderCurve f g phi psi p r*
    time (compression p F+cutoff cut+matterIncrement g psi p r) t

theorem actualObservable_zero (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (t : ℝ) : actualObservable cut F f g phi psi p 0 t=sourceFirstJet cut F f g phi psi p 0 t := by
  let K : PreparationVacuumFieldPerturbation.Op:=compression p F+cutoff cut
  let A : PreparationVacuumFieldPerturbation.Op:=localizedGauss f p phi
  have hf : (0:ℝ) • forceGauss g p psi=0 := _root_.zero_smul ℝ (forceGauss g p psi)
  have hd : (0:ℝ) • contactGauss f g p (contactLocalizer phi psi)=0 :=
    _root_.zero_smul ℝ (contactGauss f g p (contactLocalizer phi psi))
  have hK : K+(0:ℝ) • forceGauss g p psi=K :=
    (congrArg (fun X : PreparationVacuumFieldPerturbation.Op=>K+X) hf).trans (add_zero K)
  have hA : A+(0:ℝ) • contactGauss f g p (contactLocalizer phi psi)=A :=
    (congrArg (fun X : PreparationVacuumFieldPerturbation.Op=>A+X) hd).trans (add_zero A)
  have hC : K+matterIncrement g psi p 0=K :=
    (congrArg (fun X : PreparationVacuumFieldPerturbation.Op=>K+X) (matterIncrement_zero g psi p)).trans (add_zero K)
  have actual:=congrArg₂ (fun X Y : PreparationVacuumFieldPerturbation.Op=>time X (-t)*Y*time X t)
    hC (actualReaderCurve_zero f g phi psi p)
  have affine:=congrArg₂ (fun X Y : PreparationVacuumFieldPerturbation.Op=>time X (-t)*Y*time X t) hK hA
  exact actual.trans affine.symm

theorem actualObservable_continuous (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (r : ℝ) : Continuous (actualObservable cut F f g phi psi p r) :=
  (((time_continuous _).comp continuous_neg).mul continuous_const).mul (time_continuous _)

theorem nonlinear_time_window (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (cut : ℕ)
    (F : Index) (damping r t s : ℝ) (positive : 0<damping)
    (small : |r|≤nonlinearRadius g psi p cut damping) (within : |s|≤|t|) :
    ‖time (compression p F+cutoff cut+matterIncrement g psi p r) s‖≤observableWindow cut damping t := by
  have h:=nonlinear_time_envelope g psi p cut F damping r s positive small
  unfold observableWindow observableEnvelope
  rw [show damping/2/8=damping/16 by ring]
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left within (by positivity)))
    (zero_le_one.trans (sourceEnvelope_one_le cut _ (by positivity))))

theorem nonlinear_affine_observable_window (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (damping r t : ℝ) (positive : 0<damping)
    (small : |r|≤nonlinearRadius g psi p cut damping) :
    ‖actualObservable cut F f g phi psi p r t-sourceFirstJet cut F f g phi psi p r t‖≤
      ‖r‖^2*(observableWindow cut damping t)^4*
        (2*secondBound g psi p*readerSize f g phi psi p*|t|+readerSecondBound f g phi psi p) := by
  let P:=observableWindow cut damping t
  let a:=readerSize f g phi psi p
  let d:=secondBound g psi p*‖r‖^2*|t| *P^2
  let e:=readerSecondBound f g phi psi p*‖r‖^2
  have hm:=secondBound_nonneg g psi p
  have hc:=readerSecondBound_nonneg f g phi psi p
  have P1 : 1≤P := observableWindow_one_le cut damping t positive
  have P0 : 0≤P := zero_le_one.trans P1
  have a0 : 0≤a := readerSize_nonneg f g phi psi p
  have field:=nonlinearRadius_field g psi p cut damping r small
  have unit:=nonlinearRadius_unit g psi p cut damping r small
  have affine:=nonlinearRadius_affine g psi p cut damping r positive small
  have difference (s : ℝ) (hs : |s|=|t|) :
      ‖time (compression p F+cutoff cut+matterIncrement g psi p r) s-
        time (compression p F+cutoff cut+r • forceGauss g p psi) s‖≤d := by
    have h:=nonlinear_affine_time_window g psi p cut F damping r s positive small
    rw [hs] at h
    simpa only [d,P,observableWindow,observableEnvelope,show damping/2/8=damping/16 by ring] using h
  have A0 : ‖localizedGauss f p phi+r • contactGauss f g p (contactLocalizer phi psi)‖≤a := by
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    have h:=mul_le_mul_of_nonneg_right unit (norm_nonneg (contactGauss f g p (contactLocalizer phi psi)))
    dsimp [a,readerSize]
    linarith [readerSecondBound_nonneg f g phi psi p]
  have Ad : ‖actualReaderCurve f g phi psi p r-
      (localizedGauss f p phi+r • contactGauss f g p (contactLocalizer phi psi))‖≤e := by
    have identity : actualReaderCurve f g phi psi p r-
      (localizedGauss f p phi+r • contactGauss f g p (contactLocalizer phi psi))=
        readerIncrement f g phi psi p r-r • contactGauss f g p (contactLocalizer phi psi) := by
      unfold actualReaderCurve;abel
    rw [identity]
    exact readerIncrement_remainder f g phi psi p r field
  have h:=product_difference_bound
    (time (compression p F+cutoff cut+matterIncrement g psi p r) (-t))
    (time (compression p F+cutoff cut+r • forceGauss g p psi) (-t))
    (time (compression p F+cutoff cut+matterIncrement g psi p r) t)
    (time (compression p F+cutoff cut+r • forceGauss g p psi) t)
    (actualReaderCurve f g phi psi p r)
    (localizedGauss f p phi+r • contactGauss f g p (contactLocalizer phi psi)) P a d e P0 a0
    (by dsimp [d];positivity) (by dsimp [e];positivity)
    (original_observable_window p F cut g psi damping r t positive affine (-t) (by rw [abs_neg]))
    (nonlinear_time_window g psi p cut F damping r t t positive small le_rfl)
    (actual_reader_size f g phi psi p r field unit) A0 (difference (-t) (abs_neg t)) (difference t rfl) Ad
  change ‖actualObservable cut F f g phi psi p r t-sourceFirstJet cut F f g phi psi p r t‖≤_ at h
  apply h.trans
  have p3 : P^3≤P^4 := pow_le_pow_right₀ P1 (by decide)
  have p2 : P^2≤P^4 := pow_le_pow_right₀ P1 (by decide)
  calc
    _ = ‖r‖^2*((2*secondBound g psi p*a*|t|)*P^3+readerSecondBound f g phi psi p*P^2) := by dsimp [d,e];ring
    _ ≤ ‖r‖^2*((2*secondBound g psi p*a*|t|)*P^4+readerSecondBound f g phi psi p*P^4) := by
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left p3 (by positivity))
        (mul_le_mul_of_nonneg_left p2 (readerSecondBound_nonneg f g phi psi p))) (sq_nonneg _)
    _ = _ := by dsimp [P,a];ring

def comparisonScale (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (damping : ℝ) : ℝ :=
  observableEnvelope cut damping^4*(2*secondBound g psi p*readerSize f g phi psi p+readerSecondBound f g phi psi p)

theorem comparisonScale_nonneg (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (damping : ℝ) :
    0≤comparisonScale cut f g phi psi p damping := by
  unfold comparisonScale
  have hm:=secondBound_nonneg g psi p
  have hc:=readerSecondBound_nonneg f g phi psi p
  have ha:=readerSize_nonneg f g phi psi p
  positivity

theorem damped_linear_window (cut : ℕ) (damping t a b : ℝ) (future : 0≤t) (ha : 0≤a) (hb : 0≤b) :
    Real.exp (-damping*t)*(observableWindow cut damping t)^4*(a*t+b)≤
      observableEnvelope cut damping^4*(a+b)*laplaceMajorant damping t := by
  rw [observableWindow_weight cut damping t future]
  have poly : a*t+b≤(a+b)*(t+1)^2 := by
    nlinarith [mul_nonneg ha future,mul_nonneg hb future,mul_nonneg ha (sq_nonneg t),mul_nonneg hb (sq_nonneg t)]
  have h:=mul_le_mul_of_nonneg_left poly
    (mul_nonneg (by positivity : 0≤observableEnvelope cut damping^4) (Real.exp_pos (-(damping/2)*t)).le)
  exact h.trans_eq (by unfold laplaceMajorant dampedPolynomial;ring)

theorem actual_affine_damped_comparison (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (frequency damping r t : ℝ) (positive : 0<damping)
    (small : |r|≤nonlinearRadius g psi p cut damping) (future : 0≤t) :
    ‖CanonicalGradedFrequency.weight frequency damping t •
      (actualObservable cut F f g phi psi p r t-sourceFirstJet cut F f g phi psi p r t)‖≤
      ‖r‖^2*(comparisonScale cut f g phi psi p damping*laplaceMajorant damping t) := by
  have hm:=secondBound_nonneg g psi p
  have ha:=readerSize_nonneg f g phi psi p
  have h:=nonlinear_affine_observable_window cut F f g phi psi p damping r t positive small
  rw [abs_of_nonneg future] at h
  rw [norm_smul,CanonicalGradedFrequency.weight_norm]
  calc
    _ ≤ Real.exp (-damping*t)*(‖r‖^2*(observableWindow cut damping t)^4*
        (2*secondBound g psi p*readerSize f g phi psi p*t+readerSecondBound f g phi psi p)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = ‖r‖^2*(Real.exp (-damping*t)*(observableWindow cut damping t)^4*
        (2*secondBound g psi p*readerSize f g phi psi p*t+readerSecondBound f g phi psi p)) := by ring
    _ ≤ ‖r‖^2*(observableEnvelope cut damping^4*
        (2*secondBound g psi p*readerSize f g phi psi p+readerSecondBound f g phi psi p)*laplaceMajorant damping t) :=
      mul_le_mul_of_nonneg_left (damped_linear_window cut damping t _ _ future
        (by positivity) (readerSecondBound_nonneg f g phi psi p)) (sq_nonneg _)
    _ = _ := rfl

end LowEnergy.PreparationVacuumNonlinearLaplace
