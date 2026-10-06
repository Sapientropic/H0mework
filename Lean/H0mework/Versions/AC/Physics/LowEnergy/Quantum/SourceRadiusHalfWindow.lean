import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceRadiusBandContact
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceActualResolventEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceRadiusHalfWindow
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussHistoryHilbert
open GaussLiveMomentum GaussNativeEnergy GaussYukawaCoefficient GaussRadialDomain
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceRadiusBandGradient SourceRadiusPairedScalarPrice SourceRadiusBandContact
open scoped ContDiff InnerProductSpace

private theorem coefficient_nonneg (m ell : ℕ) (z : SourceCoordinateSlice) : 0≤coefficient m ell z := by
  unfold coefficient SourceRadiusBandPolynomial.band
  exact Finset.sum_nonneg (fun j _ => pow_nonneg
    (sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_radius z))) _)

private theorem root_pos (m ell : ℕ) (z : SourceCoordinateSlice) : 0<Real.sqrt (1+coefficient m ell z) :=
  Real.sqrt_pos.mpr (by have h := coefficient_nonneg m ell z;linarith)
private theorem root_smooth (m ell : ℕ) : ContDiff ℝ ∞ (fun z => Real.sqrt (1+coefficient m ell z)) :=
  (contDiff_const.add (coefficient_smooth m ell)).sqrt (fun z => by
    have h := coefficient_nonneg m ell z;linarith)

/-- A smooth function of the same positive radius band, including its zero fibre. -/
def halfCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ := Real.sqrt (1+coefficient m ell z)-1
private theorem half_smooth (m ell : ℕ) : ContDiff ℝ ∞ (halfCoefficient m ell) :=
  (root_smooth m ell).sub contDiff_const

def halfAction (m ell : ℕ) : QuantumTest →ₗ[ℂ] QuantumTest :=
  multiply (halfCoefficient m ell) (fun _ => (half_smooth m ell).contDiffAt)

/-- This is the chain-rule factor of sqrt(1+A), not an external-leg normalization. -/
def chainFactor (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ := 1/(2*Real.sqrt (1+coefficient m ell z))
private theorem factor_smooth (m ell : ℕ) : ContDiff ℝ ∞ (chainFactor m ell) :=
  contDiff_const.div (contDiff_const.mul (root_smooth m ell))
    (fun z => mul_ne_zero (by norm_num) (root_pos m ell z).ne')
def factorAction (m ell : ℕ) : QuantumTest →ₗ[ℂ] QuantumTest :=
  multiply (chainFactor m ell) (fun _ => (factor_smooth m ell).contDiffAt)
def halfContact (v : Ambient) (m ell : ℕ) : QuantumTest →ₗ[ℂ] QuantumTest :=
  contactAction v m ell*factorAction m ell

private theorem direction_half (v : Ambient) (m ell : ℕ) (z : physicalChart) :
    fderiv ℝ (halfCoefficient m ell) z.val (direction v z.val)=
      derivative v m ell z.val*chainFactor m ell z.val := by
  have hA := ((coefficient_smooth m ell).differentiable (by simp)).differentiableAt (x := z.val) |>.hasFDerivAt
  have hp : 1+coefficient m ell z.val≠0 := by have h := coefficient_nonneg m ell z.val;linarith
  have h := (((hasFDerivAt_const (1 : ℝ) z.val).add hA).sqrt hp).sub_const 1
  change HasFDerivAt (halfCoefficient m ell) _ z.val at h
  rw [h.fderiv]
  simp only [smul_apply,smul_eq_mul,Pi.add_apply,zero_add]
  rw [original_direction_band]
  unfold chainFactor
  ring

private theorem half_action_real (m ell : ℕ) (f : QuantumTest) :
    (halfAction m ell f : SourceCoordinateSlice → FockFiber)=fun z => halfCoefficient m ell z • f z := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem directional_half (v : Ambient) (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    directional v (halfAction m ell f) z=halfCoefficient m ell z • directional v f z+
      (derivative v m ell z*chainFactor m ell z) • f z := by
  rw [directional_apply,half_action_real,
    fderiv_fun_smul ((half_smooth m ell).differentiable (by simp)).differentiableAt
      (f.contDiff.differentiable (by simp)).differentiableAt]
  change halfCoefficient m ell z • directional v f z+fderiv ℝ (halfCoefficient m ell) z (direction v z) • f z=_
  by_cases hz : z∈physicalChart
  · rw [direction_half v m ell ⟨z,hz⟩]
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    rw [hf,smul_zero,smul_zero]

/-- The generated half-radius localization uses the original covariant connection and all native directions. -/
theorem original_half_native_contact (v : Ambient) (m ell : ℕ) (f : QuantumTest) :
    covariantMomentum v (halfAction m ell f)=halfAction m ell (covariantMomentum v f)+halfContact v m ell f := by
  apply DFunLike.ext
  intro z
  change (-Complex.I) • (directional v (halfAction m ell f) z+connection v z (halfAction m ell f z))=
    (halfCoefficient m ell z : ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z)))+
      ((-Complex.I)*(derivative v m ell z : ℂ)) • ((chainFactor m ell z : ℂ) • f z)
  rw [directional_half]
  change (-Complex.I) • (halfCoefficient m ell z • directional v f z+
    (derivative v m ell z*chainFactor m ell z) • f z+
    connection v z ((halfCoefficient m ell z : ℂ) • f z))=_
  rw [map_smul]
  apply PiLp.ext
  intro word
  simp only [PiLp.smul_apply,PiLp.add_apply,Complex.real_smul,Complex.ofReal_mul]
  ring

private theorem factor_identity (m ell : ℕ) (z : SourceCoordinateSlice) :
    chainFactor m ell z*coefficient m ell z*chainFactor m ell z=
      1/4-chainFactor m ell z*chainFactor m ell z := by
  have hs := Real.sq_sqrt (show 0≤1+coefficient m ell z by have h := coefficient_nonneg m ell z;linarith)
  unfold chainFactor
  field_simp [(root_pos m ell z).ne']
  nlinarith only [hs]

private theorem factor_action_identity (m ell : ℕ) (f : QuantumTest) :
    factorAction m ell (bandAction m ell (factorAction m ell f))=
      (1/4 : ℂ) • f-factorAction m ell (factorAction m ell f) := by
  apply DFunLike.ext
  intro z
  change (chainFactor m ell z : ℂ) • ((coefficient m ell z : ℂ) • ((chainFactor m ell z : ℂ) • f z))=
    (1/4 : ℂ) • f z-(chainFactor m ell z : ℂ) • ((chainFactor m ell z : ℂ) • f z)
  have h := congrArg (fun r : ℝ => (r : ℂ) • f z) (factor_identity m ell z)
  push_cast at h
  simpa only [mul_smul,sub_smul] using h

private theorem factor_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (factorAction m ell g)=sourcePair (factorAction m ell f) g := by
  exact multiply_pair (chainFactor m ell) (fun _ => (factor_smooth m ell).contDiffAt) f g

/-- The smooth half-window reconstructs the unaltered original radius band. -/
theorem original_half_square (m ell : ℕ) (f : QuantumTest) :
    halfAction m ell (halfAction m ell f)+(2 : ℂ) • halfAction m ell f=bandAction m ell f := by
  apply DFunLike.ext
  intro z
  change (halfCoefficient m ell z : ℂ) • ((halfCoefficient m ell z : ℂ) • f z)+
    (2 : ℂ) • ((halfCoefficient m ell z : ℂ) • f z)=(coefficient m ell z : ℂ) • f z
  have hs := Real.sq_sqrt (show 0≤1+coefficient m ell z by have h := coefficient_nonneg m ell z;linarith)
  have he : halfCoefficient m ell z^2+2*halfCoefficient m ell z=coefficient m ell z := by
    unfold halfCoefficient
    nlinarith only [hs]
  have h := congrArg (fun r : ℝ => (r : ℂ) • f z) he
  push_cast at h
  simpa only [pow_two,mul_smul,add_smul] using h

/-- The factor's radius energy is paid exactly by the original norm, preserving the subtracted positive square. -/
theorem original_factor_moment (m ell : ℕ) (f : QuantumTest) :
    radiusMoment m ell (embed (factorAction m ell f))=
      (1/4 : ℝ)*‖embed f‖^2-‖embed (factorAction m ell f)‖^2 := by
  unfold radiusMoment
  rw [←original_band_core]
  change (sourcePair (factorAction m ell f) (bandAction m ell (factorAction m ell f))).re=_
  rw [←factor_pair m ell f _,factor_action_identity]
  simp only [sourcePair,map_sub,map_smul,inner_sub_right,inner_smul_right,Complex.sub_re]
  have h := factor_pair m ell f (factorAction m ell f)
  simp only [sourcePair] at h
  rw [h]
  norm_num [inner_self_eq_norm_sq_to_K,Complex.mul_re]
  simp only [←Complex.ofReal_pow,Complex.ofReal_re]

/-- The actual native70 transport error is uniformly small on arbitrary moving source inputs. -/
theorem original_half_transport_error (m ell : ℕ) (f : QuantumTest) :
    (∑ i : ScalarIndex,‖embed (covariantMomentum (scalarDirection i) (halfAction m ell f)-
      halfAction m ell (covariantMomentum (scalarDirection i) f))‖^2) ≤
      (3/(4*(m+1 : ℝ)))*‖embed f‖^2 := by
  simp_rw [original_half_native_contact,add_sub_cancel_left]
  have h := original_contact_energy m ell (factorAction m ell f)
  rw [original_factor_moment] at h
  change (∑ i : ScalarIndex,‖embed (contactAction (scalarDirection i) m ell (factorAction m ell f))‖^2) ≤ _
  have hc : 0≤3/(m+1 : ℝ) := by positivity
  exact h.trans ((mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) hc).trans_eq (by field_simp))

end LowEnergy.SourceRadiusHalfWindow
