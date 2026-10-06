import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeFirstCurrentGaugeJets
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceScalarForceBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.SourceInverseFirstCurrentForceTail
open GaussCoreHilbert GaussCoreDifferential SourceQuantumScalarChart
open GaussDiagonalHistory GaussUnitaryHistory GaussNativeEnergy
open SourceInverseFirstCurrentGaugeJets SourceInverseCompressionCurrent SourceScalarDoubleCurrent
open SourceMixedNativeReturn SourceScalarForceBudget SourceResolventBandLimit SourceGaugeCoframeWard
open SourceJointResidualEnergy SourceFourPoleEnergyClosed FullYSourceResolventGraphSplice
open MeasureTheory
open scoped ENNReal
abbrev Op := H →L[ℂ] H
attribute [local irreducible] sourceRead firstSourceCorrections compressedOscillatorForce
  fullAction cutoffEuler constantAction thetaAction scaleDoubleRemainder doubleProjectionFlux
  balancedForce doubleResponse solverOperator responseJet jointResidual oscillatorMass

/-- The original force remainder keeps all input/inverse/projection jets, the three lower source forces,
    the full double projection flux, and the original Hardy/endpoint subtraction on the same F. -/
def remainingResponse (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : Op :=
  (1/6 : ℂ) • firstSourceCorrections sharp m ell F g z+
    finiteResolvent F z*remainingForces sharp m ell F g*finiteResolvent F z-
    finiteResolvent F z*doubleResponse sharp m ell F g*finiteResolvent F z

private theorem sandwich_force {R : Type*} [Ring R] [Module ℂ R]
    (r b d p q t : R) (h : r*b*r=(1/6 : ℂ) • (p+q)+t) :
    r*(b-d)*r=(1/6 : ℂ) • p+((1/6 : ℂ) • q+t-r*d*r) := by
  rw [mul_sub,sub_mul,h,smul_add]
  abel

/-- The paid current and its untouched remainder reconstruct the original balanced force minus endpoints. -/
theorem actual_force_response (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im ≠ 0) :
    finiteResolvent F z*(balancedForce sharp m ell F g-doubleResponse sharp m ell F g)*finiteResolvent F z=
      (1/6 : ℂ) • gaugeFilter (fun n => responseJet sharp m ell F z n 0)+remainingResponse sharp m ell F g z := by
  have hb := (actual_balanced_ward sharp m ell F g z hz).trans
    (actual_complete_ward_reduction sharp m ell F g z hz)
  exact sandwich_force (finiteResolvent F z) (balancedForce sharp m ell F g)
    (doubleResponse sharp m ell F g) (gaugeFilter (fun n => responseJet sharp m ell F z n 0))
    (firstSourceCorrections sharp m ell F g z)
    (finiteResolvent F z*remainingForces sharp m ell F g*finiteResolvent F z) hb

private theorem filter_pair (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (g k : QuantumTest) :
    inner ℂ (embed k) ((gaugeFilter (fun n => responseJet sharp m ell F z n 0)) (embed g))=
      filteredProfile sharp m ell F z g k := by
  simp only [gaugeFilter,filteredProfile,profile,add_apply,sub_apply,
    smul_apply,inner_add_right,inner_sub_right,inner_smul_right,smul_eq_mul]

/-- The literal original joint residual consumes the newly paid gauge current with the same source legs. -/
theorem actual_joint_response (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g k : diagonal.domain) (w : ℝ) :
    (oscillatorMass : ℂ)*jointResidual sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g k=
      (1/6 : ℂ)*filteredProfile sharp m ell F (line μ w) (coreEquiv.symm g) (coreEquiv.symm k)+
        inner ℂ (k : H) (remainingResponse sharp m ell F g (line μ w) (g : H)) := by
  have he := congrArg (fun B : Op => inner ℂ (k : H) (B (g : H)))
    (actual_force_response sharp m ell F g (line μ w) (by simpa only [line_im] using hμ.ne'))
  have hcore (f : diagonal.domain) : embed (coreEquiv.symm f)=(f : H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply f)
  have hp := filter_pair sharp m ell F (line μ w) (coreEquiv.symm g) (coreEquiv.symm k)
  rw [hcore,hcore] at hp
  simp only [mul_sub,sub_mul,add_apply,sub_apply,
    smul_apply,inner_add_right,inner_sub_right,inner_smul_right,hp] at he
  rw [←actual_force_profile_return sharp m ell F μ hμ g k w]
  exact he

/-- Without assuming a remainder bound, the difference between the original joint residual and that
    explicit remainder has a uniform all-F, whole-frequency tail. -/
theorem actual_joint_corrected_tail (sharp : Bool) (μ : ℝ) (hμ : 0 < μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖(oscillatorMass : ℂ)*jointResidual sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k-
        inner ℂ (k : H) (remainingResponse sharp m ell F g (line μ w) (g : H))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_filtered_profile_tail sharp μ hμ (coreEquiv.symm g) (coreEquiv.symm k) ε hε
  refine ⟨N,fun m hm ell hell F => (lintegral_mono (fun w => ?_)).trans (hN m hm ell hell F)⟩
  apply ENNReal.ofReal_le_ofReal
  rw [actual_joint_response sharp m ell F μ hμ g k w,add_sub_cancel_right,norm_mul,mul_pow]
  have h : ‖(1/6 : ℂ)‖^2 ≤ 1 := by norm_num
  exact (mul_le_mul_of_nonneg_right h (sq_nonneg _)).trans_eq (one_mul _)
end LowEnergy.SourceInverseFirstCurrentForceTail
