import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationFieldSourceDerivative

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumDampedFieldPerturbation
open SourceFiniteUnitary CanonicalGradedVariation PreparationVacuumFieldPerturbation
open MeasureTheory Set Filter
open scoped Topology Interval

theorem polynomial_term_envelope (y eta t : ℝ) (hy : 0 ≤ y) (he : 0 < eta) (ht : 0 ≤ t) (n : ℕ) :
    (t*y)^n ≤ (n.factorial:ℝ)*(y/eta)^n*Real.exp (eta*t) := by
  have fac : (0:ℝ)<n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have expbound := (div_le_iff₀ fac).mp (Real.pow_div_factorial_le_exp (eta*t) (mul_nonneg he.le ht) n)
  calc
    _ = (y/eta)^n*(eta*t)^n := by
      rw [←mul_pow]
      congr 1
      field_simp
    _ ≤ (y/eta)^n*(Real.exp (eta*t)*n.factorial) :=
      mul_le_mul_of_nonneg_left expbound (pow_nonneg (div_nonneg hy he.le) n)
    _ = _ := by ring

theorem scalar_integral_gronwall (u : ℝ→ℝ) (continuous : Continuous u) (nonnegative : ∀ t,0 ≤ u t)
    (M b T : ℝ) (hM : 0 ≤ M) (hb : 0 ≤ b) (future : 0 ≤ T)
    (comparison : ∀ t∈Icc 0 T,u t ≤ M+b*(∫ s in (0:ℝ)..t,u s)) :
    u T ≤ M*Real.exp (b*T) := by
  let v:=fun t : ℝ=>M+b*(∫ s in (0:ℝ)..t,u s)
  have derivative (t : ℝ) : HasDerivAt v (b*u t) t := by
    have h:=(hasDerivAt_const t M).add ((continuous.integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul b)
    convert! h using 1
    simp only [zero_add]
  have cv : Continuous v := continuous_iff_continuousAt.mpr (fun t=>(derivative t).continuousAt)
  have initial : ‖v 0‖ ≤ M := by
    simp only [v,intervalIntegral.integral_same,mul_zero,add_zero,Real.norm_eq_abs,abs_of_nonneg hM,le_refl]
  have bound (t : ℝ) (ht : t∈Ico 0 T) : ‖b*u t‖ ≤ b*‖v t‖+0 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hb (nonnegative t)),add_zero]
    exact mul_le_mul_of_nonneg_left ((comparison t ⟨ht.1,ht.2.le⟩).trans (le_abs_self (v t))) hb
  have hg:=norm_le_gronwallBound_of_norm_deriv_right_le cv.continuousOn
    (fun t _=>(derivative t).hasDerivWithinAt) initial bound T ⟨future,le_rfl⟩
  have last : ‖v T‖ ≤ M*Real.exp (b*T) := by
    simpa only [sub_zero,gronwallBound_ε0] using hg
  exact (comparison T ⟨future,le_rfl⟩).trans ((le_abs_self (v T)).trans last)

section Volterra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _

def weightedNorm (K B : E →L[ℂ] E) (r eta t : ℝ) : ℝ :=
  Real.exp (-eta*t)*‖time (K+r • B) t‖

theorem weightedNorm_continuous (K B : E →L[ℂ] E) (r eta : ℝ) : Continuous (weightedNorm K B r eta) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (time_continuous (K+r • B)).norm

theorem weightedNorm_nonneg (K B : E →L[ℂ] E) (r eta t : ℝ) : 0 ≤ weightedNorm K B r eta t :=
  mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

theorem weighted_volterra (K B : E →L[ℂ] E) (r eta M t : ℝ) (_hM : 0 ≤ M) (future : 0 ≤ t)
    (base : ∀ s,0 ≤ s → ‖time K s‖ ≤ M*Real.exp (eta*s)) :
    weightedNorm K B r eta t ≤ M+(|r| *M*‖B‖)*(∫ s in (0:ℝ)..t,weightedNorm K B r eta s) := by
  let g:=fun s : ℝ=>‖time (K+r • B) s‖*‖B‖*M*Real.exp (eta*(t-s))
  have cg : Continuous g :=
    ((((time_continuous (K+r • B)).norm.mul continuous_const).mul continuous_const).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))))
  have normB : ‖(-Complex.I) • B‖=‖B‖ := by rw [norm_smul,norm_neg,Complex.norm_I,one_mul]
  have integralBound : ‖variationBetween K B r t‖ ≤ ∫ s in (0:ℝ)..t,g s := by
    apply intervalIntegral.norm_integral_le_of_norm_le future ?_ (cg.intervalIntegrable 0 t)
    apply Eventually.of_forall
    intro s hs
    calc
      _ ≤ (‖time (K+r • B) s‖*‖(-Complex.I) • B‖)*‖time K (t-s)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (‖time (K+r • B) s‖*‖B‖)*(M*Real.exp (eta*(t-s))) := by
        rw [normB]
        exact mul_le_mul_of_nonneg_left (base (t-s) (sub_nonneg.mpr hs.2))
          (mul_nonneg (norm_nonneg _) (norm_nonneg B))
      _ = g s := by dsimp [g];ring
  have decomposition : time (K+r • B) t=time K t+r • variationBetween K B r t := by
    have h:=parameter_difference K B r t
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have preliminary : ‖time (K+r • B) t‖ ≤ M*Real.exp (eta*t)+|r| *(∫ s in (0:ℝ)..t,g s) := by
    rw [decomposition]
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    exact add_le_add (base t future) (mul_le_mul_of_nonneg_left integralBound (abs_nonneg r))
  have exponential (s : ℝ) : Real.exp (-eta*t)*Real.exp (eta*(t-s))=Real.exp (-eta*s) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have normalized : Real.exp (-eta*t)*(∫ s in (0:ℝ)..t,g s)=
      (M*‖B‖)*(∫ s in (0:ℝ)..t,weightedNorm K B r eta s) := by
    rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    calc
      _ = (M*‖B‖)*‖time (K+r • B) s‖*(Real.exp (-eta*t)*Real.exp (eta*(t-s))) := by dsimp [g];ring
      _ = _ := by rw [exponential];unfold weightedNorm;ring
  have unweight : Real.exp (-eta*t)*(M*Real.exp (eta*t))=M := by
    calc
      _ = M*(Real.exp (-eta*t)*Real.exp (eta*t)) := by ring
      _ = M := by rw [←Real.exp_add,show -eta*t+eta*t=0 by ring,Real.exp_zero,mul_one]
  calc
    _ ≤ Real.exp (-eta*t)*(M*Real.exp (eta*t)+|r| *(∫ s in (0:ℝ)..t,g s)) :=
      mul_le_mul_of_nonneg_left preliminary (Real.exp_pos _).le
    _ = _ := by
      rw [mul_add,unweight,←mul_assoc,show Real.exp (-eta*t)*|r|=|r| *Real.exp (-eta*t) by ring,
        mul_assoc,normalized]
      ring

theorem perturbed_time_envelope_positive (K B : E →L[ℂ] E) (r eta M t : ℝ) (hM : 0 ≤ M)
    (future : 0 ≤ t) (base : ∀ s,0 ≤ s → ‖time K s‖ ≤ M*Real.exp (eta*s)) :
    ‖time (K+r • B) t‖ ≤ M*Real.exp ((eta+|r| *M*‖B‖)*t) := by
  have comparison:=scalar_integral_gronwall (weightedNorm K B r eta) (weightedNorm_continuous K B r eta)
    (weightedNorm_nonneg K B r eta) M (|r| *M*‖B‖) t hM
    (mul_nonneg (mul_nonneg (abs_nonneg r) hM) (norm_nonneg B)) future
    (fun s hs=>weighted_volterra K B r eta M s hM hs.1 base)
  have h:=mul_le_mul_of_nonneg_left comparison (Real.exp_pos (eta*t)).le
  calc
    _ = Real.exp (eta*t)*weightedNorm K B r eta t := by
      unfold weightedNorm
      rw [←mul_assoc,←Real.exp_add,show eta*t+-eta*t=0 by ring,Real.exp_zero,one_mul]
    _ ≤ Real.exp (eta*t)*(M*Real.exp (|r| *M*‖B‖*t)) := h
    _ = _ := by
      rw [←mul_assoc,mul_comm (Real.exp (eta*t)) M,mul_assoc,←Real.exp_add]
      congr 2
      ring

theorem perturbed_time_envelope (K B : E →L[ℂ] E) (r eta M t : ℝ) (hM : 0 ≤ M)
    (base : ∀ s,‖time K s‖ ≤ M*Real.exp (eta*|s|)) :
    ‖time (K+r • B) t‖ ≤ M*Real.exp ((eta+|r| *M*‖B‖)*|t|) := by
  by_cases future : 0 ≤ t
  · rw [abs_of_nonneg future]
    exact perturbed_time_envelope_positive K B r eta M t hM future
      (fun s hs=>by simpa only [abs_of_nonneg hs] using base s)
  · have h:=perturbed_time_envelope_positive (-K) (-B) r eta M (-t) hM (by linarith)
      (fun s hs=>by simpa only [time_neg_generator,abs_neg,abs_of_nonneg hs] using base (-s))
    have reflection : -K+r • (-B)=-(K+r • B) := by simp only [smul_neg,neg_add]
    simpa only [reflection,time_neg_generator,neg_neg,norm_neg,abs_of_nonpos (le_of_not_ge future)] using h

end Volterra

open GaussCoreHilbert CanonicalPhysicalSpatial CanonicalGradedSpatialSource CanonicalPhysicalLaplace
open FullYSourceCutoffVolterra GaussUnitaryHistory
open PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily PreparationVacuumCausalFieldResponse

abbrev Op := PreparationVacuumFieldPerturbation.Op

def sourceEnvelope (cut : ℕ) (eta : ℝ) : ℝ :=
  ∑ j∈Finset.range 57,(j.factorial:ℝ)*(‖cutoff cut‖/eta)^j

theorem sourceEnvelope_one_le (cut : ℕ) (eta : ℝ) (positive : 0 < eta) : 1 ≤ sourceEnvelope cut eta := by
  have term (j : ℕ) (_ : j∈Finset.range 57) : 0 ≤ (j.factorial:ℝ)*(‖cutoff cut‖/eta)^j :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg (norm_nonneg _) positive.le) j)
  convert! (Finset.single_le_sum term (show 0∈Finset.range 57 by decide)) using 1
  simp only [Nat.factorial_zero,Nat.cast_one,pow_zero,mul_one]

theorem original_exponential_envelope (p : PhysicalMomentum) (F : Index) (cut : ℕ) (eta : ℝ)
    (positive : 0 < eta) (t : ℝ) :
    ‖time (compression p F+cutoff cut) t‖ ≤ sourceEnvelope cut eta*Real.exp (eta*|t|) := by
  apply (full_time_bound p F cut t).trans
  unfold timeBound sourceEnvelope
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun j _=>polynomial_term_envelope ‖cutoff cut‖ eta |t| (norm_nonneg _) positive (abs_nonneg t) j)

def parameterRadius (cut : ℕ) (eta : ℝ) (B : Op) : ℝ := eta/(sourceEnvelope cut eta*(1+‖B‖))

theorem parameterRadius_pos (cut : ℕ) (eta : ℝ) (B : Op) (positive : 0 < eta) :
    0 < parameterRadius cut eta B :=
  div_pos positive (mul_pos (lt_of_lt_of_le zero_lt_one (sourceEnvelope_one_le cut eta positive))
    (by linarith [norm_nonneg B]))

theorem parameterRadius_controls (cut : ℕ) (eta r : ℝ) (B : Op) (positive : 0 < eta)
    (small : |r| ≤ parameterRadius cut eta B) : |r| *sourceEnvelope cut eta*‖B‖ ≤ eta := by
  have hp : 0 < sourceEnvelope cut eta := lt_of_lt_of_le zero_lt_one (sourceEnvelope_one_le cut eta positive)
  have denom : 0 < sourceEnvelope cut eta*(1+‖B‖) := mul_pos hp (by linarith [norm_nonneg B])
  have h:=(le_div_iff₀ denom).mp small
  calc
    _ ≤ |r| *sourceEnvelope cut eta*(1+‖B‖) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (abs_nonneg r) hp.le)
    _ ≤ eta := by simpa only [mul_assoc] using h

theorem original_perturbed_envelope (p : PhysicalMomentum) (F : Index) (cut : ℕ) (B : Op)
    (eta r t : ℝ) (positive : 0 < eta) (small : |r| ≤ parameterRadius cut eta B) :
    ‖time (compression p F+cutoff cut+r • B) t‖ ≤ sourceEnvelope cut eta*Real.exp (2*eta*|t|) := by
  have hp : 0 ≤ sourceEnvelope cut eta := zero_le_one.trans (sourceEnvelope_one_le cut eta positive)
  have bound:=perturbed_time_envelope (compression p F+cutoff cut) B r eta (sourceEnvelope cut eta) t hp
    (original_exponential_envelope p F cut eta positive)
  apply bound.trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hp
  exact mul_le_mul_of_nonneg_right (by linarith [parameterRadius_controls cut eta r B positive small]) (abs_nonneg t)

def actualParameterRadius (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer) (damping : ℝ) : ℝ :=
  parameterRadius cut (damping/8) (forceGauss f p phi)

theorem actual_parameter_neighborhood (p : PhysicalMomentum) (cut : ℕ) (f : Field289) (phi : Localizer)
    (damping : ℝ) (positive : 0 < damping) : 0 < actualParameterRadius p cut f phi damping :=
  parameterRadius_pos cut (damping/8) (forceGauss f p phi) (by positivity)

theorem actual_damped_time_envelope (p : PhysicalMomentum) (F : Index) (cut : ℕ) (f : Field289) (phi : Localizer)
    (damping r t : ℝ) (positive : 0 < damping) (small : |r| ≤ actualParameterRadius p cut f phi damping) :
    ‖time (compression p F+cutoff cut+r • forceGauss f p phi) t‖ ≤
      sourceEnvelope cut (damping/8)*Real.exp ((damping/4)*|t|) := by
  convert! original_perturbed_envelope p F cut (forceGauss f p phi) (damping/8) r t (by positivity) small using 1
  congr 2
  ring

end LowEnergy.PreparationVacuumDampedFieldPerturbation
