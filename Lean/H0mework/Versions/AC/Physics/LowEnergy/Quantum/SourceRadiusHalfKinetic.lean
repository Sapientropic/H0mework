import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceRadiusHalfWindow
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeFrequencyBand

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceRadiusHalfKinetic
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussHistoryHilbert
open GaussLiveMomentum GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceRadiusBandGradient SourceRadiusBandContact SourceRadiusHalfWindow
open SourcePhysicalKineticSquare SourceInverseOscillator SourceInverseFrequencyBand SourceScalarInverseNativeEnergy
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def weightedContact (v : Ambient) (m ell : ℕ) : End := inverseRootAction*halfContact v m ell

def contactGram (m ell : ℕ) (p q : QuantumTest) : ℂ :=
  ∑ i : ScalarIndex,sourcePair (weightedContact (scalarDirection i) m ell p)
    (weightedContact (scalarDirection i) m ell q)

private theorem half_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (halfAction m ell g)=sourcePair (halfAction m ell f) g := multiply_pair _ _ _ _

private theorem root_half (m ell : ℕ) : Commute inverseRootAction (halfAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (inverseRootVolume z : ℂ) (halfCoefficient m ell z : ℂ) (f z)

private theorem contact_root (v : Ambient) (m ell : ℕ) : Commute (halfContact v m ell) inverseRootAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((-Complex.I)*(derivative v m ell z : ℂ)) • ((chainFactor m ell z : ℂ) •
    ((inverseRootVolume z : ℂ) • f z))=(inverseRootVolume z : ℂ) •
      (((-Complex.I)*(derivative v m ell z : ℂ)) • ((chainFactor m ell z : ℂ) • f z))
  simp only [smul_smul]
  congr 1
  ring

private theorem contact_half (v : Ambient) (m ell : ℕ) : Commute (weightedContact v m ell) (halfAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (inverseRootVolume z : ℂ) • (((-Complex.I)*(derivative v m ell z : ℂ)) •
    ((chainFactor m ell z : ℂ) • ((halfCoefficient m ell z : ℂ) • f z)))=
    (halfCoefficient m ell z : ℂ) • ((inverseRootVolume z : ℂ) •
      (((-Complex.I)*(derivative v m ell z : ℂ)) • ((chainFactor m ell z : ℂ) • f z)))
  simp only [smul_smul]
  congr 1
  ring

private theorem weighted_native_contact (v : Ambient) (m ell : ℕ) (f : QuantumTest) :
    (inverseRootAction*covariantMomentum v) (halfAction m ell f)=
      halfAction m ell ((inverseRootAction*covariantMomentum v) f)+weightedContact v m ell f := by
  simp only [Module.End.mul_apply,original_half_native_contact,map_add,weightedContact]
  exact congrArg (fun q => q+inverseRootAction (halfContact v m ell f))
    (LinearMap.congr_fun (root_half m ell).eq (covariantMomentum v f))

private theorem weight_pair (p q : QuantumTest) :
    sourcePair p (multiply scalarWeight scalarWeight_smooth q)=
      (-(sourceTime 0 : ℂ))*sourcePair (inverseRootAction p) (inverseRootAction q) := by
  have he : multiply scalarWeight scalarWeight_smooth q=(-(sourceTime 0 : ℂ)) • inverseVolumeAction q := by
    apply DFunLike.ext
    intro z
    change (scalarWeight z : ℂ) • q z=(-(sourceTime 0 : ℂ)) • ((reciprocalVolume z : ℂ) • q z)
    rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
    congr 1
  rw [he,←inverse_root_square]
  have hp : sourcePair p (inverseRootAction (inverseRootAction q))=
    sourcePair (inverseRootAction p) (inverseRootAction q) := multiply_pair _ _ _ _
  simpa only [sourcePair,map_smul,inner_smul_right] using congrArg (fun c : ℂ => -(sourceTime 0 : ℂ)*c) hp

private theorem scalar_pair (p q : QuantumTest) :
    sourcePair p (scalarKinetic q)=(-(sourceTime 0 : ℂ)/2)*∑ i : ScalarIndex,sourcePair
      ((inverseRootAction*covariantMomentum (scalarDirection i)) p)
      ((inverseRootAction*covariantMomentum (scalarDirection i)) q) := by
  have hs (i : ScalarIndex) : sourcePair p
      (sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth q)=
      (-(sourceTime 0 : ℂ))*sourcePair
        ((inverseRootAction*covariantMomentum (scalarDirection i)) p)
        ((inverseRootAction*covariantMomentum (scalarDirection i)) q) := by
    change sourcePair p (GaussMomentumAdjoint.adjoint (scalarDirection i)
      (multiply scalarWeight scalarWeight_smooth (covariantMomentum (scalarDirection i) q)))=_
    rw [adjoint_pair,weight_pair]
    rfl
  have h : sourcePair p (scalarKinetic q)=(1/2 : ℂ)*∑ i : ScalarIndex,sourcePair p
      (sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth q) := by
    simp only [scalarKinetic,LinearMap.smul_apply,LinearMap.sum_apply,sourcePair,map_smul,map_sum,
      inner_smul_right,inner_sum]
  rw [h]
  simp only [hs,←Finset.mul_sum]
  ring

private theorem row_ims (P T C : End)
    (hT : ∀ f g,sourcePair f (T g)=sourcePair (T f) g)
    (hPT : ∀ f,P (T f)=T (P f)+C f) (hCT : Commute C T) (p q : QuantumTest) :
    sourcePair (P (T p)) (P (T q))=
      (1/2 : ℂ)*(sourcePair (P (T (T p))) (P q)+sourcePair (P p) (P (T (T q))))+
        sourcePair (C p) (C q) := by
  have hTT (f : QuantumTest) : P (T (T f))=T (T (P f))+T (C f)+T (C f) := by
    rw [hPT,hPT,map_add,show C (T f)=T (C f) from LinearMap.congr_fun hCT.eq f]
  have hL : sourcePair (P (T (T p))) (P q)=sourcePair (T (P p)) (T (P q))+
      sourcePair (C p) (T (P q))+sourcePair (C p) (T (P q)) := by
    rw [hTT]
    simp only [sourcePair,map_add,inner_add_left]
    change sourcePair (T (T (P p))) (P q)+sourcePair (T (C p)) (P q)+sourcePair (T (C p)) (P q)=_
    rw [←hT (T (P p)) (P q),←hT (C p) (P q)]
    rfl
  have hR : sourcePair (P p) (P (T (T q)))=sourcePair (T (P p)) (T (P q))+
      sourcePair (T (P p)) (C q)+sourcePair (T (P p)) (C q) := by
    rw [hTT]
    simp only [sourcePair,map_add,inner_add_right]
    change sourcePair (P p) (T (T (P q)))+sourcePair (P p) (T (C q))+sourcePair (P p) (T (C q))=_
    rw [hT (P p) (T (P q)),hT (P p) (C q)]
    rfl
  rw [hL,hR,hPT,hPT]
  simp only [sourcePair,map_add,inner_add_left,inner_add_right]
  ring

/-- The literal negative scalar weight and both original covariant legs enter before taking a real part. -/
theorem original_scalar_bilinear_ims (m ell : ℕ) (p q : QuantumTest) :
    sourcePair (halfAction m ell p) (scalarKinetic (halfAction m ell q))=
      (1/2 : ℂ)*(sourcePair (halfAction m ell (halfAction m ell p)) (scalarKinetic q)+
        sourcePair p (scalarKinetic (halfAction m ell (halfAction m ell q))))-
      ((sourceTime 0 : ℂ)/2)*contactGram m ell p q := by
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset ScalarIndex)) rfl (fun i _ =>
    row_ims (inverseRootAction*covariantMomentum (scalarDirection i)) (halfAction m ell)
      (weightedContact (scalarDirection i) m ell) (half_pair m ell)
      (weighted_native_contact (scalarDirection i) m ell) (contact_half (scalarDirection i) m ell) p q)
  simp only [mul_add,Finset.sum_add_distrib,←Finset.mul_sum] at h
  rw [scalar_pair,scalar_pair,scalar_pair]
  unfold contactGram
  linear_combination (-(sourceTime 0 : ℂ)/2)*h

/-- The IMS Gram retains the inverse-volume square root on every one of the native70 rows. -/
theorem original_weighted_contact_energy (m ell : ℕ) (f : QuantumTest) :
    (contactGram m ell f f).re ≤ (3/(4*(m+1 : ℝ)))*‖embed (inverseRootAction f)‖^2 := by
  have h := original_half_transport_error m ell (inverseRootAction f)
  have hc (v : Ambient) : halfContact v m ell (inverseRootAction f)=
      inverseRootAction (halfContact v m ell f) := LinearMap.congr_fun (contact_root v m ell).eq f
  simp_rw [original_half_native_contact,add_sub_cancel_left,hc] at h
  have he : (contactGram m ell f f).re=
      ∑ i : ScalarIndex,‖embed (weightedContact (scalarDirection i) m ell f)‖^2 := by
    unfold contactGram
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    change RCLike.re (inner ℂ (embed (weightedContact (scalarDirection i) m ell f))
      (embed (weightedContact (scalarDirection i) m ell f)))=_
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [he]
  exact h

/-- The existing source oscillator floor pays the weighted IMS error; no bounded-volume premise is installed. -/
theorem original_kinetic_contact_price (m ell : ℕ) (f : QuantumTest) :
    (sourceTime 0/2)*(contactGram m ell f f).re ≤
      (3/(1952*Real.sqrt 2*(m+1 : ℝ)))*inverseForm f := by
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hm : (0 : ℝ) < m+1 := by positivity
  have hc := mul_le_mul_of_nonneg_left (original_weighted_contact_energy m ell f) (by positivity : 0 ≤ sourceTime 0/2)
  have hf := original_inverse_volume_floor f
  rw [original_inverse_mass,Complex.ofReal_re] at hf
  have hb := mul_le_mul_of_nonneg_left hf (by positivity : 0≤3/(1952*Real.sqrt 2*(m+1 : ℝ)))
  apply hc.trans
  convert hb using 1
  field_simp
  ring

private theorem contact_real (m ell : ℕ) (f : QuantumTest) :
    (contactGram m ell f f).re=∑ i : ScalarIndex,‖embed (weightedContact (scalarDirection i) m ell f)‖^2 := by
  unfold contactGram
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  change RCLike.re (inner ℂ (embed (weightedContact (scalarDirection i) m ell f))
    (embed (weightedContact (scalarDirection i) m ell f)))=_
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

private theorem gram_bound {ι : Type*} [Fintype ι] (u v : ι → H) :
    ‖∑ i,inner ℂ (u i) (v i)‖^2 ≤ (∑ i,‖u i‖^2)*(∑ i,‖v i‖^2) := by
  have h := (norm_sum_le (Finset.univ : Finset ι) (fun i => inner ℂ (u i) (v i))).trans
    (Finset.sum_le_sum (fun i _ => norm_inner_le_norm (u i) (v i)))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖u i‖) (fun i => ‖v i‖))

/-- Independent source legs keep the full complex Gram and its exact source oscillator prices. -/
theorem original_kinetic_polarized_price (m ell : ℕ) (p q : QuantumTest) :
    ‖((sourceTime 0 : ℂ)/2)*contactGram m ell p q‖^2 ≤
      (3/(1952*Real.sqrt 2*(m+1 : ℝ)))^2*inverseForm p*inverseForm q := by
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hc : 0 ≤ 3/(1952*Real.sqrt 2*(m+1 : ℝ)) := by positivity
  have hgram : ‖contactGram m ell p q‖^2 ≤ (contactGram m ell p p).re*(contactGram m ell q q).re := by
    rw [contact_real,contact_real]
    exact gram_bound (fun i : ScalarIndex => embed (weightedContact (scalarDirection i) m ell p))
      (fun i : ScalarIndex => embed (weightedContact (scalarDirection i) m ell q))
  have hp := original_kinetic_contact_price m ell p
  have hq := original_kinetic_contact_price m ell q
  have hqp : 0 ≤ (sourceTime 0/2)*(contactGram m ell q q).re := by
    rw [contact_real]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hpp := mul_nonneg hc (original_inverse_nonnegative p)
  have hmul := mul_le_mul hp hq hqp hpp
  calc
    _=(sourceTime 0/2)^2*‖contactGram m ell p q‖^2 := by
      rw [norm_mul,mul_pow,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn]
      norm_num
    _ ≤ (sourceTime 0/2)^2*((contactGram m ell p p).re*(contactGram m ell q q).re) :=
      mul_le_mul_of_nonneg_left hgram (sq_nonneg _)
    _ ≤ _ := by nlinarith only [hmul]

end LowEnergy.SourceRadiusHalfKinetic
