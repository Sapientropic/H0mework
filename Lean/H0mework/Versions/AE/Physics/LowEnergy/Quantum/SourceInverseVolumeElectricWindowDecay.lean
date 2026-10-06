import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeElectricScalarEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceInverseElectricWindowDecay
open GaussHistoryHilbert GaussCoreHilbert GaussCoreDifferential GaussNativeForm GaussYukawaCoefficient
open GaussRadialDomain GaussFockWeights SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open SourceInverseElectricCurrentFactor SourceInverseElectricCurrentForm SourceMixedNativeReturn
open SourceScalarPositiveBulkWard SourceScalarPairedTransport GaussUnitaryHistory GaussDiagonalHistory
open SourceNativeCutoffContact
open scoped ContDiff InnerProductSpace

private theorem geometric_peak (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    s*(1-s)^n ≤ 1/(n+1 : ℝ) := by
  have hterm := Finset.single_le_sum
    (f := fun j => s^j*(1-s)^(n+1-j)*((n+1).choose j : ℝ))
    (fun j _ => by positivity) (show 1 ∈ Finset.range (n+1+1) by simp)
  rw [←add_pow,show s+(1-s)=1 by ring,one_pow] at hterm
  simp only [pow_one,Nat.add_sub_cancel,Nat.choose_one_right,Nat.cast_add,Nat.cast_one] at hterm
  apply (le_div_iff₀ (show 0 < (n+1 : ℝ) by positivity)).mpr
  exact hterm

/-- The original inverse-radius window supplies a cutoff-order bound, uniform in its upper endpoint. -/
theorem original_inverse_window_bound (m ell : ℕ) (hle : m ≤ ell) (z : SourceCoordinateSlice) :
    |reciprocal z*SourceNativeCutoffContact.theta m ell z| ≤ 1/(m+2 : ℝ) := by
  have hs : 0 ≤ reciprocal z := (inv_pos.mpr (radius_pos z)).le
  have hs1 : reciprocal z ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius z)
  have hq : 0 ≤ 1-reciprocal z := sub_nonneg.mpr hs1
  have hq1 : 1-reciprocal z ≤ 1 := by linarith
  have he := pow_le_pow_of_le_one hq hq1 (Nat.add_le_add_right hle 1)
  have ht : 0 ≤ SourceNativeCutoffContact.theta m ell z := sub_nonneg.mpr he
  rw [abs_of_nonneg (mul_nonneg hs ht)]
  have hp := geometric_peak (reciprocal z) hs hs1 (m+1)
  have hmul : reciprocal z*SourceNativeCutoffContact.theta m ell z ≤ reciprocal z*(1-reciprocal z)^(m+1) := by
    unfold SourceNativeCutoffContact.theta
    exact mul_le_mul_of_nonneg_left (sub_le_self _ (pow_nonneg hq _)) hs
  have hd : ((m+1 : ℕ) : ℝ)+1=(m+2 : ℝ) := by push_cast;ring
  rw [hd] at hp
  exact hmul.trans hp

def damping (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  reciprocal z*SourceNativeCutoffContact.theta m ell z
private theorem damping_smooth (m ell : ℕ) : ContDiff ℝ ∞ (damping m ell) :=
  reciprocal_smooth.mul (SourceNativeCutoffContact.theta_smooth m ell)

def dampingAction (m ell : ℕ) : QuantumTest →ₗ[ℂ] QuantumTest :=
  multiply (damping m ell) (fun _ => (damping_smooth m ell).contDiffAt)

def higherEnvelopeAction (sharp : Bool) (v : GaussLiveMomentum.Ambient) : QuantumTest →ₗ[ℂ] QuantumTest :=
  multiply (fun z => envelope sharp v z*radius z)
    (fun z => (envelope_smooth sharp v z).mul radius_smooth.contDiffAt)

/-- The extra radius is carried by the actual input, not placed in a caller-supplied moment bound. -/
theorem actual_scalar_window_factor (sharp : Bool) (m ell : ℕ) (v : GaussLiveMomentum.Ambient) (f : QuantumTest) :
    dampingAction m ell (higherEnvelopeAction sharp v f)=
      envelopeAction sharp v (SourceMixedNativeReturn.thetaAction m ell f) := by
  apply DFunLike.ext
  intro z
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  change ((reciprocal z*SourceNativeCutoffContact.theta m ell z : ℝ) : ℂ) •
    (((envelope sharp v z*radius z : ℝ) : ℂ) • f z)=
    (envelope sharp v z : ℂ) • ((SourceNativeCutoffContact.theta m ell z : ℂ) • f z)
  rw [smul_smul,smul_smul]
  apply congrArg (fun c : ℂ => c • f z)
  have hr : reciprocal z*radius z=1 := inv_mul_cancel₀ (radius_pos z).ne'
  have he : reciprocal z*SourceNativeCutoffContact.theta m ell z*(envelope sharp v z*radius z)=
      envelope sharp v z*SourceNativeCutoffContact.theta m ell z := by
    calc
      _ = (reciprocal z*radius z)*(envelope sharp v z*SourceNativeCutoffContact.theta m ell z) := by ring
      _ = _ := by rw [hr,one_mul]
  exact_mod_cast he

private theorem damping_bound (m ell : ℕ) (hle : m ≤ ell) (f : QuantumTest) :
    ‖embed (dampingAction m ell f)‖ ≤ (1/(m+2 : ℝ))*‖embed f‖ := by
  apply GaussBoundedMultiplier.action_bound
    (fun z => (damping m ell z : ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun z => (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (damping_smooth m ell).contDiffAt).smul contDiffAt_const)
    (fun _ w => (Commute.one_right (weight w)).smul_right _) _ (by positivity) _ f
  intro z x
  change ‖(damping m ell z.val : ℂ) • x‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (original_inverse_window_bound m ell hle z.val) (norm_nonneg x)

theorem actual_scalar_window_energy (sharp : Bool) (m ell : ℕ) (hle : m ≤ ell)
    (v : GaussLiveMomentum.Ambient) (f : QuantumTest) :
    ‖embed (envelopeAction sharp v (SourceMixedNativeReturn.thetaAction m ell f))‖^2 ≤
      (1/(m+2 : ℝ))^2*‖embed (higherEnvelopeAction sharp v f)‖^2 := by
  rw [←actual_scalar_window_factor sharp m ell v f]
  exact (pow_le_pow_left₀ (norm_nonneg _) (damping_bound m ell hle _) 2).trans_eq (mul_pow _ _ 2)

/-- The full current has the generated cutoff decay on each actual retarded input. -/
theorem actual_current_decay (sharp : Bool) (m ell : ℕ) (hle : m ≤ ell)
    (v : GaussLiveMomentum.Ambient) (hv : v.1=0) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    ‖embed (windowCurrent sharp m ell v (state F z hz g))‖^2 ≤
      (1/(m+2 : ℝ))^2*‖embed (higherEnvelopeAction sharp v (state F z hz g))‖^2 :=
  (actual_current_energy sharp m ell v hv _).trans (actual_scalar_window_energy sharp m ell hle v _)

end LowEnergy.SourceInverseElectricWindowDecay
