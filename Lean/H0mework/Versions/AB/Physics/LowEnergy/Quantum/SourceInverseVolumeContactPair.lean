import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeContactWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseContactPair
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussHistoryHilbert
open GaussNativeEnergy GaussYukawaCoefficient SourceNativeCutoffContact
open SourceQuantumScalarChart SourcePhysicalKineticSquare SourceScalarInverseNativeEnergy
open SourceScalarInverseEnergyExchange SourceInverseContactHardy
open SourceScalarPositiveBulkWard GaussDiagonalHistory GaussUnitaryHistory
open scoped InnerProductSpace BigOperators

private theorem gram_bound {ι : Type*} [Fintype ι] (u v : ι → H) :
    ‖∑ i,inner ℂ (u i) (v i)‖^2  ≤  (∑ i,‖u i‖^2)*(∑ i,‖v i‖^2) := by
  have h := (norm_sum_le (Finset.univ : Finset ι) (fun i => inner ℂ (u i) (v i))).trans
    (Finset.sum_le_sum (fun i _ => norm_inner_le_norm (u i) (v i)))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖u i‖) (fun i => ‖v i‖))

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

/-- Polarization keeps the full native70 Gram, even for distinct source states. -/
theorem original_inverse_contact_gram (m ell : ℕ) (p q : QuantumTest) :
    ‖inverseContact m ell p q‖^2  ≤  (inverseContact m ell p p).re*(inverseContact m ell q q).re := by
  have h := gram_bound
    (fun i : ScalarIndex => embed (inverseVolumeAction (contactAction (scalarDirection i) m ell p)))
    (fun i : ScalarIndex => embed (inverseVolumeAction (contactAction (scalarDirection i) m ell q)))
  have hn : ‖(4*(sourceTime 0 : ℂ))‖=4*sourceTime 0 := by
    rw [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos lapse_pos]
  rw [inverse_contact_real,inverse_contact_real]
  calc
    _=(4*sourceTime 0)^2*‖∑ i : ScalarIndex,sourcePair
      (inverseVolumeAction (contactAction (scalarDirection i) m ell p))
      (inverseVolumeAction (contactAction (scalarDirection i) m ell q))‖^2 := by
        rw [inverseContact,norm_mul,hn,mul_pow]
    _  ≤  (4*sourceTime 0)^2*((∑ i : ScalarIndex,
        ‖embed (inverseVolumeAction (contactAction (scalarDirection i) m ell p))‖^2)*
      (∑ i : ScalarIndex,‖embed (inverseVolumeAction (contactAction (scalarDirection i) m ell q))‖^2)) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _=_ := by ring

/-- The two distinct source legs are each paid by their own two actual cutoff windows. -/
theorem original_polarized_contact_window (m ell : ℕ) (hm : 1 ≤ m) (hell : m ≤ ell)
    (p q : QuantumTest) :
    ‖inverseContact m ell p q‖^2  ≤  (72/3481 : ℝ)^2*
      (inverseForm (thetaAction (m/2) m p)+inverseForm (thetaAction (ell/2) ell p))*
      (inverseForm (thetaAction (m/2) m q)+inverseForm (thetaAction (ell/2) ell q)) := by
  have hp := original_inverse_ims_window m ell hm hell p
  have hq := original_inverse_ims_window m ell hm hell q
  have hnq : 0 ≤ (inverseContact m ell q q).re := by
    rw [inverse_contact_real]
    exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) lapse_pos.le)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hnp : 0 ≤ (72/3481 : ℝ)*
      (inverseForm (thetaAction (m/2) m p)+inverseForm (thetaAction (ell/2) ell p)) :=
    mul_nonneg (by norm_num) (add_nonneg (original_inverse_nonnegative _) (original_inverse_nonnegative _))
  exact (original_inverse_contact_gram m ell p q).trans
    ((mul_le_mul hp hq hnq hnp).trans_eq (by ring))

/-- The original input pair, two independent nonreal frequencies and both branch choices survive the contact budget. -/
theorem actual_two_frequency_contact_window (leftSharp rightSharp : Bool)
    (m ell : ℕ) (hm : 1 ≤ m) (hell : m ≤ ell) (F : Index)
    (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0) (g k : diagonal.domain) :
    ‖inverseContact m ell (state F zl hl k) (state F zr hr g)‖^2  ≤  (72/3481 : ℝ)^2*
      ((signedPair leftSharp (m/2) m (state F zl hl k) (state F zl hl k)).re+
        (signedPair leftSharp (ell/2) ell (state F zl hl k) (state F zl hl k)).re)*
      ((signedPair rightSharp (m/2) m (state F zr hr g) (state F zr hr g)).re+
        (signedPair rightSharp (ell/2) ell (state F zr hr g) (state F zr hr g)).re) := by
  simp_rw [original_diagonal_energy_exchange]
  exact original_polarized_contact_window m ell hm hell (state F zl hl k) (state F zr hr g)

end LowEnergy.SourceInverseContactPair
