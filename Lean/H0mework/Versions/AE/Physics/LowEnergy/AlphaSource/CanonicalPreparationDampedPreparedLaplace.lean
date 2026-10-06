import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationDampedLaplaceDerivative

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumDampedFieldPerturbation
open SourceFiniteUnitary CanonicalGradedVariation PreparationVacuumFieldPerturbation
open MeasureTheory Set Filter
open scoped Topology Interval

section Product
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _

private theorem norm_mul3 (U A V : E →L[ℂ] E) (u a v : ℝ)
    (hu : ‖U‖ ≤ u) (ha : ‖A‖ ≤ a) (hv : ‖V‖ ≤ v) (nu : 0 ≤ u) (na : 0 ≤ a) :
    ‖U*A*V‖ ≤ u*a*v :=
  (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul hu ha (norm_nonneg A) nu)) hv
    (norm_nonneg V) (mul_nonneg nu na))

omit [CompleteSpace E] in
theorem observable_remainder_identity (U U0 Ud V V0 Vd A D : E →L[ℂ] E) (r : ℝ) :
    U*(A+r • D)*V-U0*A*V0-r • ((Ud*A+U0*D)*V0+U0*A*Vd)=
      (U-U0-r • Ud)*A*V0+U*A*(V-V0-r • Vd)+
        r • ((U-U0)*A*Vd)+r • ((U-U0)*D*V0)+r • (U*D*(V-V0)) := by
  simp only [mul_add,add_mul,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_assoc,smul_add,smul_sub]
  module

theorem observable_remainder_bound (U U0 Ud V V0 Vd A D : E →L[ℂ] E) (r T P b : ℝ)
    (hT : 0 ≤ T) (hP : 0 ≤ P) (hb : 0 ≤ b)
    (hu : ‖U‖ ≤ P) (hv : ‖V0‖ ≤ P)
    (hd : ‖Vd‖ ≤ T*P^2*b)
    (du : ‖U-U0‖ ≤ ‖r‖*T*P^2*b) (dv : ‖V-V0‖ ≤ ‖r‖*T*P^2*b)
    (eu : ‖U-U0-r • Ud‖ ≤ ‖r‖^2*T^2*P^3*b^2)
    (ev : ‖V-V0-r • Vd‖ ≤ ‖r‖^2*T^2*P^3*b^2) :
    ‖U*(A+r • D)*V-U0*A*V0-r • ((Ud*A+U0*D)*V0+U0*A*Vd)‖ ≤
      ‖r‖^2*(3*T^2*P^4*b^2*‖A‖+2*T*P^3*b*‖D‖) := by
  have nR : 0 ≤ ‖r‖ := norm_nonneg r
  have nE : 0 ≤ ‖r‖^2*T^2*P^3*b^2 := by positivity
  have nD : 0 ≤ ‖r‖*T*P^2*b := by positivity
  have h1:=norm_mul3 (U-U0-r • Ud) A V0 _ _ _ eu le_rfl hv nE (norm_nonneg A)
  have h2:=norm_mul3 U A (V-V0-r • Vd) _ _ _ hu le_rfl ev hP (norm_nonneg A)
  have h3 : ‖r • ((U-U0)*A*Vd)‖ ≤ ‖r‖*((‖r‖*T*P^2*b)*‖A‖*(T*P^2*b)) := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_mul3 (U-U0) A Vd _ _ _ du le_rfl hd nD (norm_nonneg A)) nR
  have h4 : ‖r • ((U-U0)*D*V0)‖ ≤ ‖r‖*((‖r‖*T*P^2*b)*‖D‖*P) := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_mul3 (U-U0) D V0 _ _ _ du le_rfl hv nD (norm_nonneg D)) nR
  have h5 : ‖r • (U*D*(V-V0))‖ ≤ ‖r‖*(P*‖D‖*(‖r‖*T*P^2*b)) := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_mul3 U D (V-V0) _ _ _ hu le_rfl dv hP (norm_nonneg D)) nR
  rw [observable_remainder_identity]
  calc
    _ ≤ ‖(U-U0-r • Ud)*A*V0‖+‖U*A*(V-V0-r • Vd)‖+
        ‖r • ((U-U0)*A*Vd)‖+‖r • ((U-U0)*D*V0)‖+‖r • (U*D*(V-V0))‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add _ le_rfl
      apply (norm_add_le _ _).trans
      apply add_le_add _ le_rfl
      apply (norm_add_le _ _).trans
      exact add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (‖r‖^2*T^2*P^3*b^2)*‖A‖*P+P*‖A‖*(‖r‖^2*T^2*P^3*b^2)+
        ‖r‖*((‖r‖*T*P^2*b)*‖A‖*(T*P^2*b))+‖r‖*((‖r‖*T*P^2*b)*‖D‖*P)+
          ‖r‖*(P*‖D‖*(‖r‖*T*P^2*b)) := add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5
    _ = _ := by ring

def timeObservable (K B A D : E →L[ℂ] E) (r t : ℝ) : E →L[ℂ] E :=
  time (K+r • B) (-t)*(A+r • D)*time (K+r • B) t

def timeObservableDerivative (K B A D : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  (variation K B (-t)*A+time K (-t)*D)*time K t+time K (-t)*A*variation K B t

theorem timeObservable_remainder_window (K B A D : E →L[ℂ] E) (r t P : ℝ) (hP : 0 ≤ P)
    (base : ∀ s,|s| ≤ |t| → ‖time K s‖ ≤ P)
    (perturbed : ∀ s,|s| ≤ |t| → ‖time (K+r • B) s‖ ≤ P) :
    ‖timeObservable K B A D r t-timeObservable K B A D 0 t-r • timeObservableDerivative K B A D t‖ ≤
      ‖r‖^2*(3*|t|^2*P^4*‖B‖^2*‖A‖+2*|t| *P^3*‖B‖*‖D‖) := by
  have negWithin : |-t| ≤ |t| := by rw [abs_neg]
  have derivative : ‖variation K B t‖ ≤ |t| *P^2*‖B‖ := by
    have h:=variationBetween_window K B 0 |t| P P t hP hP le_rfl base (by simpa only [zero_smul,add_zero] using base)
    exact h.trans_eq (by ring)
  have difference (s : ℝ) (hs : |s|=|t|) : ‖time (K+r • B) s-time K s‖ ≤ ‖r‖*|t| *P^2*‖B‖ := by
    have h:=parameter_difference_window K B r |t| P P s hP hP hs.le base perturbed
    exact h.trans_eq (by rw [hs,Real.norm_eq_abs];ring)
  have error (s : ℝ) (hs : |s|=|t|) :
      ‖time (K+r • B) s-time K s-r • variation K B s‖ ≤ ‖r‖^2*|t|^2*P^3*‖B‖^2 := by
    have h:=parameter_remainder_window K B r |t| P P s hP hP hs.le base perturbed
    exact h.trans_eq (by rw [hs];ring)
  have h:=observable_remainder_bound (time (K+r • B) (-t)) (time K (-t)) (variation K B (-t))
    (time (K+r • B) t) (time K t) (variation K B t) A D r |t| P ‖B‖ (abs_nonneg t) hP (norm_nonneg B)
    (perturbed (-t) negWithin) (base t le_rfl) derivative (difference (-t) (abs_neg t)) (difference t rfl)
    (error (-t) (abs_neg t)) (error t rfl)
  simpa only [timeObservable,timeObservableDerivative,zero_smul,add_zero] using h

theorem timeObservable_derivative_window (K B A D : E →L[ℂ] E) (t P : ℝ) (hP : 0 ≤ P)
    (base : ∀ s,|s| ≤ |t| → ‖time K s‖ ≤ P) :
    ‖timeObservableDerivative K B A D t‖ ≤ 2*|t| *P^3*‖B‖*‖A‖+P^2*‖D‖ := by
  have derivative (s : ℝ) (hs : |s|=|t|) : ‖variation K B s‖ ≤ |t| *P^2*‖B‖ := by
    have h:=variationBetween_window K B 0 |t| P P s hP hP hs.le base (by simpa only [zero_smul,add_zero] using base)
    exact h.trans_eq (by rw [hs];ring)
  have nD : 0 ≤ |t| *P^2*‖B‖ := mul_nonneg (mul_nonneg (abs_nonneg t) (sq_nonneg P)) (norm_nonneg B)
  have h1:=norm_mul3 (variation K B (-t)) A (time K t) _ _ _ (derivative (-t) (abs_neg t)) le_rfl (base t le_rfl) nD (norm_nonneg A)
  have h2:=norm_mul3 (time K (-t)) D (time K t) _ _ _ (base (-t) (by rw [abs_neg])) le_rfl (base t le_rfl) hP (norm_nonneg D)
  have h3:=norm_mul3 (time K (-t)) A (variation K B t) _ _ _ (base (-t) (by rw [abs_neg])) le_rfl (derivative t rfl) hP (norm_nonneg A)
  unfold timeObservableDerivative
  rw [add_mul]
  calc
    _ ≤ ‖variation K B (-t)*A*time K t‖+‖time K (-t)*D*time K t‖+‖time K (-t)*A*variation K B t‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (|t| *P^2*‖B‖)*‖A‖*P+P*‖D‖*P+P*‖A‖*(|t| *P^2*‖B‖) := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

theorem timeObservable_window (K B A D : E →L[ℂ] E) (r t P : ℝ) (hP : 0 ≤ P) (small : |r| ≤ 1)
    (perturbed : ∀ s,|s| ≤ |t| → ‖time (K+r • B) s‖ ≤ P) :
    ‖timeObservable K B A D r t‖ ≤ P^2*(‖A‖+‖D‖) := by
  have middle : ‖A+r • D‖ ≤ ‖A‖+‖D‖ := by
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    exact add_le_add le_rfl ((mul_le_mul_of_nonneg_right small (norm_nonneg D)).trans_eq (one_mul _))
  apply (norm_mul3 _ _ _ P (‖A‖+‖D‖) P (perturbed (-t) (by rw [abs_neg])) middle (perturbed t le_rfl)
    hP (add_nonneg (norm_nonneg A) (norm_nonneg D))).trans_eq
  ring

private theorem timeObservable_continuous (K B A D : E →L[ℂ] E) (r : ℝ) : Continuous (timeObservable K B A D r) :=
  (((time_continuous (K+r • B)).comp continuous_neg).mul continuous_const).mul (time_continuous (K+r • B))

private theorem timeObservableDerivative_continuous (K B A D : E →L[ℂ] E) : Continuous (timeObservableDerivative K B A D) := by
  have hv : Continuous (variation K B) := by
    have same : variation K B=PreparationVacuumFieldPerturbation.Blocks.crossTime K K B := by
      funext t
      rw [PreparationVacuumFieldPerturbation.Blocks.crossTime_integral]
      simp only [variation,variationBetween,zero_smul,add_zero]
    rw [same]
    exact continuous_iff_continuousAt.mpr (fun t=>(PreparationVacuumFieldPerturbation.Blocks.crossTime_derivative K K B t).continuousAt)
  have hl : Continuous (fun t : ℝ=>variation K B (-t)*A+time K (-t)*D) :=
    ((hv.comp continuous_neg).mul continuous_const).add
      (((time_continuous K).comp continuous_neg).mul continuous_const)
  exact (hl.mul (time_continuous K)).add
    ((((time_continuous K).comp continuous_neg).mul continuous_const).mul hv)

end Product

open GaussCoreHilbert CanonicalPhysicalSpatial CanonicalGradedSpatialSource CanonicalPhysicalLaplace
open FullYSourceCutoffVolterra GaussUnitaryHistory SourceFamilyOperator SourceFamilyHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily PreparationVacuumCausalFieldResponse
local instance : NormedAlgebra ℚ Op := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : SecondCountableTopologyEither ℝ Op := ⟨Or.inl inferInstance⟩
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

def observableRadius (p : PhysicalMomentum) (cut : ℕ) (g : Field289) (psi : Localizer) (damping : ℝ) : ℝ :=
  min 1 (actualParameterRadius p cut g psi (damping/2))

theorem observableRadius_pos (p : PhysicalMomentum) (cut : ℕ) (g : Field289) (psi : Localizer) (damping : ℝ)
    (positive : 0 < damping) : 0 < observableRadius p cut g psi damping :=
  lt_min zero_lt_one (actual_parameter_neighborhood p cut g psi (damping/2) (by positivity))

def observableEnvelope (cut : ℕ) (damping : ℝ) : ℝ := sourceEnvelope cut ((damping/2)/8)
def observableWindow (cut : ℕ) (damping t : ℝ) : ℝ := observableEnvelope cut damping*Real.exp ((damping/8)*|t|)

theorem observableEnvelope_one_le (cut : ℕ) (damping : ℝ) (positive : 0 < damping) :
    1 ≤ observableEnvelope cut damping := sourceEnvelope_one_le cut _ (by positivity)

theorem observableWindow_one_le (cut : ℕ) (damping t : ℝ) (positive : 0 < damping) :
    1 ≤ observableWindow cut damping t :=
  one_le_mul_of_one_le_of_one_le (observableEnvelope_one_le cut damping positive)
    (Real.one_le_exp_iff.mpr (mul_nonneg (by positivity) (abs_nonneg t)))

theorem original_observable_window (p : PhysicalMomentum) (F : Index) (cut : ℕ) (g : Field289) (psi : Localizer)
    (damping r t : ℝ) (positive : 0 < damping) (small : |r| ≤ observableRadius p cut g psi damping)
    (s : ℝ) (within : |s| ≤ |t|) :
    ‖time (compression p F+cutoff cut+r • forceGauss g p psi) s‖ ≤ observableWindow cut damping t := by
  have h:=actual_damped_time_envelope p F cut g psi (damping/2) r s (by positivity)
    (small.trans (min_le_right _ _))
  have rate : (damping/2)/4=damping/8 := by ring
  rw [rate] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left within (by positivity)))
    (zero_le_one.trans (observableEnvelope_one_le cut damping positive)))

theorem original_observable_base (p : PhysicalMomentum) (F : Index) (cut : ℕ) (g : Field289) (psi : Localizer)
    (damping t : ℝ) (positive : 0 < damping) (s : ℝ) (within : |s| ≤ |t|) :
    ‖time (compression p F+cutoff cut) s‖ ≤ observableWindow cut damping t := by
  have zeroSmall : |(0:ℝ)| ≤ observableRadius p cut g psi damping :=
    abs_zero.trans_le (observableRadius_pos p cut g psi damping positive).le
  have h:=original_observable_window p F cut g psi damping 0 t positive zeroSmall s within
  rw [time_parameter_zero] at h
  exact h

def sourceJetDerivative (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (t : ℝ) : Op :=
  timeObservableDerivative (compression p F+cutoff cut) (forceGauss g p psi)
    (localizedGauss f p phi) (contactGauss f g p (contactLocalizer phi psi)) t

theorem actual_sourceFirstJet_read (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (r t : ℝ) :
    sourceFirstJet cut F f g phi psi p r t=timeObservable (compression p F+cutoff cut) (forceGauss g p psi)
      (localizedGauss f p phi) (contactGauss f g p (contactLocalizer phi psi)) r t := rfl

theorem sourceJet_remainder_window (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (damping r t : ℝ) (positive : 0 < damping) (small : |r| ≤ observableRadius p cut g psi damping) :
    ‖sourceFirstJet cut F f g phi psi p r t-sourceFirstJet cut F f g phi psi p 0 t-r • sourceJetDerivative cut F f g phi psi p t‖ ≤
      ‖r‖^2*(3*|t|^2*(observableWindow cut damping t)^4*‖forceGauss g p psi‖^2*‖localizedGauss f p phi‖+
        2*|t| *(observableWindow cut damping t)^3*‖forceGauss g p psi‖*‖contactGauss f g p (contactLocalizer phi psi)‖) :=
  timeObservable_remainder_window _ _ _ _ r t (observableWindow cut damping t)
    (zero_le_one.trans (observableWindow_one_le cut damping t positive))
    (original_observable_base p F cut g psi damping t positive)
    (original_observable_window p F cut g psi damping r t positive small)

private theorem scalar_polynomial_bound (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) :
    a*t^2+b*t ≤ (a+b)*(t+1)^2 := by
  nlinarith [mul_nonneg ha ht,mul_nonneg hb ht,mul_nonneg hb (sq_nonneg t)]

private theorem scalar_linear_bound (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) :
    a*t+b ≤ (a+b)*(t+1)^2 := by
  nlinarith [mul_nonneg ha ht,mul_nonneg ha (sq_nonneg t),mul_nonneg hb ht,mul_nonneg hb (sq_nonneg t)]

theorem observableWindow_weight (cut : ℕ) (damping t : ℝ) (future : 0 ≤ t) :
    Real.exp (-damping*t)*(observableWindow cut damping t)^4=
      observableEnvelope cut damping^4*Real.exp (-(damping/2)*t) := by
  unfold observableWindow
  rw [abs_of_nonneg future,mul_pow,←Real.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  calc
    _ = observableEnvelope cut damping^4*(Real.exp (-damping*t)*Real.exp (4*((damping/8)*t))) := by ring
    _ = _ := by rw [←Real.exp_add];congr 2;ring

def sourceJetTimeScale (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (damping : ℝ) : ℝ :=
  observableEnvelope cut damping^4*(‖localizedGauss f p phi‖+‖contactGauss f g p (contactLocalizer phi psi)‖)

def sourceJetDerivativeScale (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (damping : ℝ) : ℝ :=
  observableEnvelope cut damping^4*(2*‖forceGauss g p psi‖*‖localizedGauss f p phi‖+‖contactGauss f g p (contactLocalizer phi psi)‖)

def sourceJetRemainderScale (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (damping : ℝ) : ℝ :=
  observableEnvelope cut damping^4*(3*‖forceGauss g p psi‖^2*‖localizedGauss f p phi‖+
    2*‖forceGauss g p psi‖*‖contactGauss f g p (contactLocalizer phi psi)‖)

private theorem damped_window_time (cut : ℕ) (damping t a d : ℝ) (positive : 0 < damping)
    (future : 0 ≤ t) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    Real.exp (-damping*t)*((observableWindow cut damping t)^2*(a+d)) ≤
      (observableEnvelope cut damping^4*(a+d))*laplaceMajorant damping t := by
  have power : (observableWindow cut damping t)^2 ≤ (observableWindow cut damping t)^4 :=
    pow_le_pow_right₀ (observableWindow_one_le cut damping t positive) (by decide)
  have hM := zero_le_one.trans (observableEnvelope_one_le cut damping positive)
  calc
    _ ≤ Real.exp (-damping*t)*((observableWindow cut damping t)^4*(a+d)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right power (add_nonneg ha hd)) (Real.exp_pos _).le
    _ = (Real.exp (-damping*t)*(observableWindow cut damping t)^4)*(a+d) := by ring
    _ = (observableEnvelope cut damping^4*Real.exp (-(damping/2)*t))*(a+d) := by rw [observableWindow_weight cut damping t future]
    _ ≤ (observableEnvelope cut damping^4*Real.exp (-(damping/2)*t))*(a+d)*(t+1)^2 :=
      le_mul_of_one_le_right (mul_nonneg (mul_nonneg (pow_nonneg hM 4) (Real.exp_pos _).le) (add_nonneg ha hd))
        (by nlinarith [sq_nonneg t])
    _ = _ := by unfold laplaceMajorant dampedPolynomial;ring

private theorem damped_window_derivative (cut : ℕ) (damping t a b d : ℝ) (positive : 0 < damping)
    (future : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    Real.exp (-damping*t)*(2*t*(observableWindow cut damping t)^3*b*a+(observableWindow cut damping t)^2*d) ≤
      (observableEnvelope cut damping^4*(2*b*a+d))*laplaceMajorant damping t := by
  let P:=observableWindow cut damping t
  have h3 : P^3 ≤ P^4 := pow_le_pow_right₀ (observableWindow_one_le cut damping t positive) (by decide)
  have h2 : P^2 ≤ P^4 := pow_le_pow_right₀ (observableWindow_one_le cut damping t positive) (by decide)
  have hM := zero_le_one.trans (observableEnvelope_one_le cut damping positive)
  have increase : 2*t*P^3*b*a+P^2*d ≤ P^4*((2*b*a)*t+d) := by
    calc
      _ ≤ 2*t*P^4*b*a+P^4*d := add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h3 (mul_nonneg (by norm_num) future)) hb) ha)
        (mul_le_mul_of_nonneg_right h2 hd)
      _ = _ := by ring
  calc
    _ ≤ Real.exp (-damping*t)*(P^4*((2*b*a)*t+d)) := mul_le_mul_of_nonneg_left increase (Real.exp_pos _).le
    _ = (Real.exp (-damping*t)*P^4)*((2*b*a)*t+d) := by ring
    _ = (observableEnvelope cut damping^4*Real.exp (-(damping/2)*t))*((2*b*a)*t+d) := by rw [observableWindow_weight cut damping t future]
    _ ≤ (observableEnvelope cut damping^4*Real.exp (-(damping/2)*t))*((2*b*a+d)*(t+1)^2) :=
      mul_le_mul_of_nonneg_left (scalar_linear_bound (2*b*a) d t (by positivity) hd future)
        (mul_nonneg (pow_nonneg hM 4) (Real.exp_pos _).le)
    _ = _ := by unfold laplaceMajorant dampedPolynomial;ring

private theorem damped_window_remainder (cut : ℕ) (damping t a b d : ℝ) (positive : 0 < damping)
    (future : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    Real.exp (-damping*t)*(3*t^2*(observableWindow cut damping t)^4*b^2*a+2*t*(observableWindow cut damping t)^3*b*d) ≤
      (observableEnvelope cut damping^4*(3*b^2*a+2*b*d))*laplaceMajorant damping t := by
  let P:=observableWindow cut damping t
  have h3 : P^3 ≤ P^4 := pow_le_pow_right₀ (observableWindow_one_le cut damping t positive) (by decide)
  have hM := zero_le_one.trans (observableEnvelope_one_le cut damping positive)
  have increase : 3*t^2*P^4*b^2*a+2*t*P^3*b*d ≤ P^4*((3*b^2*a)*t^2+(2*b*d)*t) := by
    calc
      _ ≤ 3*t^2*P^4*b^2*a+2*t*P^4*b*d := add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h3 (mul_nonneg (by norm_num) future)) hb) hd)
      _ = _ := by ring
  calc
    _ ≤ Real.exp (-damping*t)*(P^4*((3*b^2*a)*t^2+(2*b*d)*t)) := mul_le_mul_of_nonneg_left increase (Real.exp_pos _).le
    _ = (Real.exp (-damping*t)*P^4)*((3*b^2*a)*t^2+(2*b*d)*t) := by ring
    _ = (observableEnvelope cut damping^4*Real.exp (-(damping/2)*t))*((3*b^2*a)*t^2+(2*b*d)*t) := by rw [observableWindow_weight cut damping t future]
    _ ≤ (observableEnvelope cut damping^4*Real.exp (-(damping/2)*t))*((3*b^2*a+2*b*d)*(t+1)^2) :=
      mul_le_mul_of_nonneg_left (scalar_polynomial_bound (3*b^2*a) (2*b*d) t (by positivity) (by positivity) future)
        (mul_nonneg (pow_nonneg hM 4) (Real.exp_pos _).le)
    _ = _ := by unfold laplaceMajorant dampedPolynomial;ring

def jetLaplaceIntegrand (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping r t : ℝ) : Op :=
  CanonicalGradedFrequency.weight frequency damping t • sourceFirstJet cut F f g phi psi p r t

def jetDerivativeIntegrand (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping t : ℝ) : Op :=
  CanonicalGradedFrequency.weight frequency damping t • sourceJetDerivative cut F f g phi psi p t

def jetErrorIntegrand (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping r t : ℝ) : Op :=
  CanonicalGradedFrequency.weight frequency damping t •
    (sourceFirstJet cut F f g phi psi p r t-sourceFirstJet cut F f g phi psi p 0 t-r • sourceJetDerivative cut F f g phi psi p t)

theorem jetLaplace_bound (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping r t : ℝ) (positive : 0 < damping) (small : |r| ≤ observableRadius p cut g psi damping)
    (future : 0 ≤ t) :
    ‖jetLaplaceIntegrand p F cut f g phi psi frequency damping r t‖ ≤ sourceJetTimeScale cut f g phi psi p damping*laplaceMajorant damping t := by
  have h:=timeObservable_window (compression p F+cutoff cut) (forceGauss g p psi)
    (localizedGauss f p phi) (contactGauss f g p (contactLocalizer phi psi)) r t (observableWindow cut damping t)
    (zero_le_one.trans (observableWindow_one_le cut damping t positive)) (small.trans (min_le_left _ _))
    (original_observable_window p F cut g psi damping r t positive small)
  rw [jetLaplaceIntegrand,norm_smul,CanonicalGradedFrequency.weight_norm]
  exact (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans
    (damped_window_time cut damping t _ _ positive future (norm_nonneg _) (norm_nonneg _))

theorem jetDerivative_bound (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping t : ℝ) (positive : 0 < damping) (future : 0 ≤ t) :
    ‖jetDerivativeIntegrand p F cut f g phi psi frequency damping t‖ ≤ sourceJetDerivativeScale cut f g phi psi p damping*laplaceMajorant damping t := by
  have h:=timeObservable_derivative_window (compression p F+cutoff cut) (forceGauss g p psi)
    (localizedGauss f p phi) (contactGauss f g p (contactLocalizer phi psi)) t (observableWindow cut damping t)
    (zero_le_one.trans (observableWindow_one_le cut damping t positive))
    (original_observable_base p F cut g psi damping t positive)
  rw [abs_of_nonneg future] at h
  rw [jetDerivativeIntegrand,norm_smul,CanonicalGradedFrequency.weight_norm]
  exact (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans
    (damped_window_derivative cut damping t _ _ _ positive future (norm_nonneg _) (norm_nonneg _) (norm_nonneg _))

theorem jetError_bound (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping r t : ℝ) (positive : 0 < damping) (small : |r| ≤ observableRadius p cut g psi damping)
    (future : 0 ≤ t) :
    ‖jetErrorIntegrand p F cut f g phi psi frequency damping r t‖ ≤
      ‖r‖^2*(sourceJetRemainderScale cut f g phi psi p damping*laplaceMajorant damping t) := by
  have h:=sourceJet_remainder_window cut F f g phi psi p damping r t positive small
  rw [abs_of_nonneg future] at h
  rw [jetErrorIntegrand,norm_smul,CanonicalGradedFrequency.weight_norm]
  calc
    _ ≤ Real.exp (-damping*t)*(‖r‖^2*(3*t^2*(observableWindow cut damping t)^4*‖forceGauss g p psi‖^2*‖localizedGauss f p phi‖+
        2*t*(observableWindow cut damping t)^3*‖forceGauss g p psi‖*‖contactGauss f g p (contactLocalizer phi psi)‖)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = ‖r‖^2*(Real.exp (-damping*t)*(3*t^2*(observableWindow cut damping t)^4*‖forceGauss g p psi‖^2*‖localizedGauss f p phi‖+
        2*t*(observableWindow cut damping t)^3*‖forceGauss g p psi‖*‖contactGauss f g p (contactLocalizer phi psi)‖)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (damped_window_remainder cut damping t _ _ _ positive future (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)) (sq_nonneg ‖r‖)

theorem sourceJetTimeScale_nonneg (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (damping : ℝ)
    (positive : 0 < damping) : 0 ≤ sourceJetTimeScale cut f g phi psi p damping :=
  mul_nonneg (pow_nonneg (zero_le_one.trans (observableEnvelope_one_le cut damping positive)) 4)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))

theorem sourceJetDerivativeScale_nonneg (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (damping : ℝ)
    (positive : 0 < damping) : 0 ≤ sourceJetDerivativeScale cut f g phi psi p damping :=
  mul_nonneg (pow_nonneg (zero_le_one.trans (observableEnvelope_one_le cut damping positive)) 4)
    (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _))

theorem sourceJetRemainderScale_nonneg (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p : PhysicalMomentum) (damping : ℝ)
    (positive : 0 < damping) : 0 ≤ sourceJetRemainderScale cut f g phi psi p damping :=
  mul_nonneg (pow_nonneg (zero_le_one.trans (observableEnvelope_one_le cut damping positive)) 4)
    (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (norm_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (norm_nonneg _)))

theorem jetLaplace_integrable (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping r : ℝ) (positive : 0 < damping) (small : |r| ≤ observableRadius p cut g psi damping) :
    IntegrableOn (jetLaplaceIntegrand p F cut f g phi psi frequency damping r) (Ioi 0) := by
  have continuous : Continuous (jetLaplaceIntegrand p F cut f g phi psi frequency damping r) :=
    (CanonicalGradedFrequency.weight_continuous frequency damping).smul (timeObservable_continuous _ _ _ _ r)
  apply ((laplaceMajorant_integrable damping positive).const_mul (sourceJetTimeScale cut f g phi psi p damping)).mono' continuous.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact jetLaplace_bound p F cut f g phi psi frequency damping r t positive small ht.le

theorem jetDerivative_integrable (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping : ℝ) (positive : 0 < damping) :
    IntegrableOn (jetDerivativeIntegrand p F cut f g phi psi frequency damping) (Ioi 0) := by
  have continuous : Continuous (jetDerivativeIntegrand p F cut f g phi psi frequency damping) :=
    (CanonicalGradedFrequency.weight_continuous frequency damping).smul (timeObservableDerivative_continuous _ _ _ _)
  apply ((laplaceMajorant_integrable damping positive).const_mul (sourceJetDerivativeScale cut f g phi psi p damping)).mono' continuous.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact jetDerivative_bound p F cut f g phi psi frequency damping t positive ht.le

def finiteJetLaplace (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping r : ℝ) : Op := ∫ t in Ioi 0,jetLaplaceIntegrand p F cut f g phi psi frequency damping r t

def finiteJetDerivative (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping : ℝ) : Op := ∫ t in Ioi 0,jetDerivativeIntegrand p F cut f g phi psi frequency damping t

theorem finiteJetLaplace_bound (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping r : ℝ) (positive : 0 < damping) (small : |r| ≤ observableRadius p cut g psi damping) :
    ‖finiteJetLaplace p F cut f g phi psi frequency damping r‖ ≤ sourceJetTimeScale cut f g phi psi p damping*laplaceMass damping := by
  have h:=norm_integral_le_of_norm_le ((laplaceMajorant_integrable damping positive).const_mul (sourceJetTimeScale cut f g phi psi p damping))
    (show ∀ᵐ t ∂volume.restrict (Ioi 0),‖jetLaplaceIntegrand p F cut f g phi psi frequency damping r t‖ ≤
      sourceJetTimeScale cut f g phi psi p damping*laplaceMajorant damping t from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact jetLaplace_bound p F cut f g phi psi frequency damping r t positive small ht.le)
  rw [integral_const_mul] at h
  exact h

theorem finiteJetDerivative_bound (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping : ℝ) (positive : 0 < damping) :
    ‖finiteJetDerivative p F cut f g phi psi frequency damping‖ ≤ sourceJetDerivativeScale cut f g phi psi p damping*laplaceMass damping := by
  have h:=norm_integral_le_of_norm_le ((laplaceMajorant_integrable damping positive).const_mul (sourceJetDerivativeScale cut f g phi psi p damping))
    (show ∀ᵐ t ∂volume.restrict (Ioi 0),‖jetDerivativeIntegrand p F cut f g phi psi frequency damping t‖ ≤
      sourceJetDerivativeScale cut f g phi psi p damping*laplaceMajorant damping t from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact jetDerivative_bound p F cut f g phi psi frequency damping t positive ht.le)
  rw [integral_const_mul] at h
  exact h

theorem finiteJetLaplace_remainder (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping r : ℝ) (positive : 0 < damping) (small : |r| ≤ observableRadius p cut g psi damping) :
    ‖finiteJetLaplace p F cut f g phi psi frequency damping r-finiteJetLaplace p F cut f g phi psi frequency damping 0-
      r • finiteJetDerivative p F cut f g phi psi frequency damping‖ ≤
      (sourceJetRemainderScale cut f g phi psi p damping*laplaceMass damping)*‖r‖^2 := by
  have zeroSmall : |(0:ℝ)| ≤ observableRadius p cut g psi damping := abs_zero.trans_le (observableRadius_pos p cut g psi damping positive).le
  have hr:=jetLaplace_integrable p F cut f g phi psi frequency damping r positive small
  have h0:=jetLaplace_integrable p F cut f g phi psi frequency damping 0 positive zeroSmall
  have hd:=jetDerivative_integrable p F cut f g phi psi frequency damping positive
  have identity : jetErrorIntegrand p F cut f g phi psi frequency damping r=
      (fun t=>jetLaplaceIntegrand p F cut f g phi psi frequency damping r t-
        jetLaplaceIntegrand p F cut f g phi psi frequency damping 0 t-r • jetDerivativeIntegrand p F cut f g phi psi frequency damping t) := by
    funext t
    exact weight_sub_smul _ _ _ _ _
  have integralIdentity : (∫ t in Ioi 0,jetErrorIntegrand p F cut f g phi psi frequency damping r t)=
      finiteJetLaplace p F cut f g phi psi frequency damping r-finiteJetLaplace p F cut f g phi psi frequency damping 0-
        r • finiteJetDerivative p F cut f g phi psi frequency damping := by
    rw [identity]
    exact integral_sub_smul (volume.restrict (Ioi 0)) _ _ _ r hr h0 hd
  rw [←integralIdentity]
  have h:=norm_integral_le_of_norm_le (((laplaceMajorant_integrable damping positive).const_mul
    (sourceJetRemainderScale cut f g phi psi p damping)).const_mul (‖r‖^2))
    (show ∀ᵐ t ∂volume.restrict (Ioi 0),‖jetErrorIntegrand p F cut f g phi psi frequency damping r t‖ ≤
      ‖r‖^2*(sourceJetRemainderScale cut f g phi psi p damping*laplaceMajorant damping t) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact jetError_bound p F cut f g phi psi frequency damping r t positive small ht.le)
  rw [integral_const_mul,integral_const_mul] at h
  exact h.trans_eq (by unfold laplaceMass;ring)

def jetLaplaceFamily (p : PhysicalMomentum) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping : ℝ) (positive : 0 < damping) (r : ℝ) : Operator Index H where
  component F:=if |r| ≤ observableRadius p cut g psi damping then finiteJetLaplace p F cut f g phi psi frequency damping r else 0
  bounded:=⟨sourceJetTimeScale cut f g phi psi p damping*laplaceMass damping,
    mul_nonneg (sourceJetTimeScale_nonneg cut f g phi psi p damping positive) (laplaceMass_nonneg damping),fun F v=>by
      split_ifs with small
      · exact ((finiteJetLaplace p F cut f g phi psi frequency damping r).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (finiteJetLaplace_bound p F cut f g phi psi frequency damping r positive small) (norm_nonneg v))
      · simp only [zero_apply,norm_zero]
        exact mul_nonneg (mul_nonneg (sourceJetTimeScale_nonneg cut f g phi psi p damping positive) (laplaceMass_nonneg damping)) (norm_nonneg v)⟩

def jetDerivativeFamily (p : PhysicalMomentum) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping : ℝ) (positive : 0 < damping) : Operator Index H where
  component F:=finiteJetDerivative p F cut f g phi psi frequency damping
  bounded:=⟨sourceJetDerivativeScale cut f g phi psi p damping*laplaceMass damping,
    mul_nonneg (sourceJetDerivativeScale_nonneg cut f g phi psi p damping positive) (laplaceMass_nonneg damping),fun F v=>
      ((finiteJetDerivative p F cut f g phi psi frequency damping).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (finiteJetDerivative_bound p F cut f g phi psi frequency damping positive) (norm_nonneg v))⟩

def sourceJetLaplace (p : PhysicalMomentum) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping : ℝ) (positive : 0 < damping) (r : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (jetLaplaceFamily p cut f g phi psi frequency damping positive r)

def sourceJetLaplaceDerivative (p : PhysicalMomentum) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping : ℝ) (positive : 0 < damping) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (jetDerivativeFamily p cut f g phi psi frequency damping positive)

theorem jetLaplaceFamily_actual (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping r : ℝ) (positive : 0 < damping) (small : |r| ≤ observableRadius p cut g psi damping) :
    (jetLaplaceFamily p cut f g phi psi frequency damping positive r).component F=
      ∫ t in Ioi 0,CanonicalGradedFrequency.weight frequency damping t • sourceFirstJet cut F f g phi psi p r t :=
  if_pos small

def jetErrorFamily (p : PhysicalMomentum) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping r : ℝ) (positive : 0 < damping) (small : |r| ≤ observableRadius p cut g psi damping) : Operator Index H where
  component F:=finiteJetLaplace p F cut f g phi psi frequency damping r-finiteJetLaplace p F cut f g phi psi frequency damping 0-
    r • finiteJetDerivative p F cut f g phi psi frequency damping
  bounded:=⟨(sourceJetRemainderScale cut f g phi psi p damping*laplaceMass damping)*‖r‖^2,
    mul_nonneg (mul_nonneg (sourceJetRemainderScale_nonneg cut f g phi psi p damping positive) (laplaceMass_nonneg damping)) (sq_nonneg _),fun F v=>
      ((finiteJetLaplace p F cut f g phi psi frequency damping r-finiteJetLaplace p F cut f g phi psi frequency damping 0-
        r • finiteJetDerivative p F cut f g phi psi frequency damping).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (finiteJetLaplace_remainder p F cut f g phi psi frequency damping r positive small) (norm_nonneg v))⟩

theorem jet_lift_error (p : PhysicalMomentum) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping r : ℝ) (positive : 0 < damping) (small : |r| ≤ observableRadius p cut g psi damping) :
    lift sourceFilter (jetErrorFamily p cut f g phi psi frequency damping r positive small)=
      sourceJetLaplace p cut f g phi psi frequency damping positive r-sourceJetLaplace p cut f g phi psi frequency damping positive 0-
        r • sourceJetLaplaceDerivative p cut f g phi psi frequency damping positive := by
  apply lift_sub_smul
  intro F
  have zeroSmall : |(0:ℝ)| ≤ observableRadius p cut g psi damping := abs_zero.trans_le (observableRadius_pos p cut g psi damping positive).le
  rw [jetLaplaceFamily_actual _ _ _ _ _ _ _ _ _ _ positive small,jetLaplaceFamily_actual _ _ _ _ _ _ _ _ _ _ positive zeroSmall]
  rfl

theorem sourceJetLaplace_remainder (p : PhysicalMomentum) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping r : ℝ) (positive : 0 < damping) (small : |r| ≤ observableRadius p cut g psi damping) :
    ‖sourceJetLaplace p cut f g phi psi frequency damping positive r-sourceJetLaplace p cut f g phi psi frequency damping positive 0-
      r • sourceJetLaplaceDerivative p cut f g phi psi frequency damping positive‖ ≤
        (sourceJetRemainderScale cut f g phi psi p damping*laplaceMass damping)*‖r‖^2 := by
  rw [←jet_lift_error _ _ _ _ _ _ _ _ _ positive small]
  apply lift_bound sourceFilter _ _ (mul_nonneg
    (mul_nonneg (sourceJetRemainderScale_nonneg cut f g phi psi p damping positive) (laplaceMass_nonneg damping)) (sq_nonneg _))
  intro F
  exact finiteJetLaplace_remainder p F cut f g phi psi frequency damping r positive small

theorem sourceJetLaplace_parameter_derivative (p : PhysicalMomentum) (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (frequency damping : ℝ) (positive : 0 < damping) :
    HasDerivAt (sourceJetLaplace p cut f g phi psi frequency damping positive)
      (sourceJetLaplaceDerivative p cut f g phi psi frequency damping positive) 0 := by
  rw [hasDerivAt_iff_tendsto]
  simp only [sub_zero]
  let K:=sourceJetRemainderScale cut f g phi psi p damping*laplaceMass damping
  have convergence : Tendsto (fun r : ℝ=>K*‖r‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using ((continuous_norm:Continuous (fun r:ℝ=>‖r‖)).tendsto 0).const_mul K
  apply squeeze_zero' (Eventually.of_forall (fun r=>mul_nonneg (inv_nonneg.mpr (norm_nonneg r)) (norm_nonneg _))) ?_ convergence
  have small : ∀ᶠ r : ℝ in 𝓝 0,|r| ≤ observableRadius p cut g psi damping := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (observableRadius_pos p cut g psi damping positive)] with r hr
    exact (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hr : |r|<observableRadius p cut g psi damping).le
  filter_upwards [small] with r hr
  have bound:=mul_le_mul_of_nonneg_left (sourceJetLaplace_remainder p cut f g phi psi frequency damping r positive hr) (inv_nonneg.mpr (norm_nonneg r))
  have scalar : ‖r‖⁻¹*(K*‖r‖^2)=K*‖r‖ := by
    by_cases zero : ‖r‖=0
    · simp only [zero,inv_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero]
    · field_simp
  exact bound.trans_eq scalar

open GaussComposite GaussComposite.SourceGraph
open CanonicalPreparationCore.Completed CanonicalPreparationCreation PreparationVacuumNativeClosure
open PreparationChartGuard PreparationScalarCoordinates CanonicalScalarPreparation

theorem original_prepared_affine_laplace (x : zeroLocalizedSpace actualNativeLocalizer)
    (p : PhysicalMomentum) (cut : ℕ) (f g : Field289) (phi psi : Localizer) (frequency damping : ℝ)
    (positive : 0 < damping) (left right : Bool) (lc ls rc rs : Fin 2) :
    (∃ h : prepared (zeroLocalizedProfile actualNativeLocalizer x)∈GaussRadialDomain.closedY.domain,
      ∀ n : ℕ,‖GaussRadialDomain.closedY ⟨prepared (zeroLocalizedProfile actualNativeLocalizer x),h⟩-
        cutoff n (prepared (zeroLocalizedProfile actualNativeLocalizer x))‖ ≤
          (915/916:ℝ)^(n+1)*916*GaussYukawaCoefficient.bound*‖x‖) ∧
    HasDerivAt (fun r : ℝ=>SourceGraph.response (sourceJetLaplace p cut f g phi psi frequency damping positive r) left right lc ls rc rs
      (zeroLocalizedProfile actualNativeLocalizer x) (zeroLocalizedProfile actualNativeLocalizer x))
      (SourceGraph.response (sourceJetLaplaceDerivative p cut f g phi psi frequency damping positive) left right lc ls rc rs
        (zeroLocalizedProfile actualNativeLocalizer x) (zeroLocalizedProfile actualNativeLocalizer x)) 0 := by
  obtain ⟨h,_,bound⟩:=PreparationVacuumLocalizedYukawa.original_prepared_Y_domain x
  refine ⟨⟨h,bound⟩,?_⟩
  exact (preparationRead left right lc ls rc rs (zeroLocalizedProfile actualNativeLocalizer x)
    (zeroLocalizedProfile actualNativeLocalizer x)).hasFDerivAt.comp_hasDerivAt 0
      (sourceJetLaplace_parameter_derivative p cut f g phi psi frequency damping positive)

end LowEnergy.PreparationVacuumDampedFieldPerturbation
