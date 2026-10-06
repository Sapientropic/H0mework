import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusAcceleration
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponsePositiveSource
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiRadiusNormalizedFlux
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory GaussNativePotential
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourcePhysicalHamiltonianSquare
open SourceClockReflectedForm SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceScalarDoubleCurrent
open SourceClockPhiRadiusSourceCurrent SourceClockPhiRadiusAcceleration SourceClockPhiRadiusResponsePositiveSource
open SourceClockRadiusAffineCutoff SourceScalarInverseNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
private abbrev U : End := inverseVolumeAction
private abbrev P (a : ScalarIndex) : End := covariantMomentum (scalarDirection a)
private abbrev d (a : ScalarIndex) : End := phiDirectionAction (scalarBasis a)
private abbrev W : End := multiply scalarWeight scalarWeight_smooth
attribute [local irreducible] compressionCore defectAction diagonalAction

private theorem real_commute (c h : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hh : ∀ z : physicalChart,ContDiffAt ℝ ∞ h z.val) :
    Commute (multiply c hc) (multiply h hh) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (h z:ℂ) (f z)
private theorem S_d (a : ScalarIndex) : Commute S (d a) := real_commute _ _ _ _
private theorem S_U : Commute S U := real_commute _ _ _ _
private theorem d_U (a : ScalarIndex) : Commute (d a) U := real_commute _ _ _ _
private theorem S_pair (p q : QuantumTest) : sourcePair p (S q)=sourcePair (S p) q := multiply_pair _ _ _ _
private theorem U_pair (p q : QuantumTest) : sourcePair p (U q)=sourcePair (U p) q := multiply_pair _ _ _ _
private theorem d_pair (a : ScalarIndex) (p q : QuantumTest) : sourcePair p (d a q)=sourcePair (d a p) q := multiply_pair _ _ _ _
private theorem r_pair (p q : QuantumTest) : sourcePair p (r q)=sourcePair (r p) q := multiply_pair _ _ _ _
private theorem inverse_radius : r*S=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiRadius z:ℂ) • ((phiReciprocal z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,mul_inv_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem radius_inverse : S*r=(1:End) := (real_commute _ _ _ _).eq.trans inverse_radius

private theorem native_inverse (a : ScalarIndex) :
    P a*(S)-S*P a=(-Complex.I) • (d a*S^2) := by
  have hp := (original_phi_radius_native_jet (scalarDirection a)).1
  change P a*r-r*P a=Complex.I • d a at hp
  have h1 := congrArg (fun T : End => S*T*S) hp
  have h2 : S*(P a*r-r*P a)*S=S*P a-P a*S := by
    calc _=S*P a*(r*S)-(S*r)*P a*S := by noncomm_ring
         _=_ := by rw [inverse_radius,radius_inverse,mul_one,one_mul]
  rw [h2,mul_smul_comm,smul_mul_assoc] at h1
  have hd := (S_d a).eq
  have he : S*d a*S=d a*S^2 := by rw [hd,pow_two,mul_assoc]
  rw [he] at h1
  linear_combination (norm:=module) -h1

private theorem weight_inverse : W=(-(sourceTime 0:ℂ)) • U := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (scalarWeight z:ℂ) • f z=(-(sourceTime 0:ℂ)) • ((reciprocalVolume z:ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1

private theorem radius_current_pair (p q : QuantumTest) :
    sourcePair p (phiRadiusCurrent q)=(-Complex.I*(sourceTime 0:ℂ)/2)*
      (∑ a : ScalarIndex,(sourcePair (P a (U p)) (d a q)+sourcePair (d a (U p)) (P a q))) := by
  have hP (a : ScalarIndex) : U (P a p)=P a (U p) :=
    (LinearMap.congr_fun (original_native_inverse_commute (scalarDirection a)).eq p).symm
  have hd (a : ScalarIndex) : U (d a p)=d a (U p) :=
    (LinearMap.congr_fun (d_U a).eq p).symm
  have row (a : ScalarIndex) :
      sourcePair p (GaussMomentumAdjoint.adjoint (scalarDirection a) (W (d a q)))+
        sourcePair p (d a (W (P a q)))=
      (-(sourceTime 0:ℂ))*(sourcePair (P a (U p)) (d a q)+sourcePair (d a (U p)) (P a q)) := by
    rw [adjoint_pair,d_pair a p (W (P a q)),weight_inverse]
    simp only [LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right]
    change (-(sourceTime 0:ℂ))*sourcePair (P a p) (U (d a q))+
      (-(sourceTime 0:ℂ))*sourcePair (d a p) (U (P a q))=_
    rw [U_pair,U_pair,hP,hd]
    unfold sourcePair
    ring
  rw [phiRadiusCurrent]
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.add_apply,Module.End.mul_apply]
  change sourcePair p ((Complex.I/2:ℂ) •
    ∑ a : ScalarIndex,(GaussMomentumAdjoint.adjoint (scalarDirection a) (W (d a q))+d a (W (P a q))))=_
  simp only [sourcePair,map_smul,map_sum,map_add,inner_smul_right,inner_sum,inner_add_right] at row ⊢
  simp_rw [row]
  rw [←Finset.mul_sum]
  ring

private theorem current_anti (p q : QuantumTest) :
    sourcePair p (phiRadiusCurrent q)= -sourcePair (phiRadiusCurrent p) q := by
  rw [←original_phi_radius_hamiltonian_current]
  change sourcePair p (diagonalAction (r q)-r (diagonalAction q))=
    -sourcePair (diagonalAction (r p)-r (diagonalAction p)) q
  simp only [sourcePair,map_sub,inner_sub_right,inner_sub_left]
  have h1 := diagonalAction_pair p (r q)
  have h2 := r_pair p (diagonalAction q)
  have h3 := r_pair (diagonalAction p) q
  have h4 := diagonalAction_pair (r p) q
  unfold sourcePair at h1 h2 h3 h4
  linear_combination (norm:=ring) h1-h2+h3-h4

private theorem contact_im_zero (a : ScalarIndex) (f : QuantumTest) :
    (sourcePair (d a (U f)) (d a ((S^2) f))).im=0 := by
  have hd (q : QuantumTest) : d a (S q)=S (d a q) :=
    (LinearMap.congr_fun (S_d a).eq q).symm
  have hu (q : QuantumTest) : S (U q)=U (S q) := LinearMap.congr_fun S_U.eq q
  have hc (q : QuantumTest) : d a (U q)=U (d a q) := LinearMap.congr_fun (d_U a).eq q
  rw [pow_two]
  change (sourcePair (d a (U f)) (d a (S (S f)))).im=0
  rw [hd,S_pair,hc,hu,←hd]
  have h := congrArg Complex.im (pair_conjugate (U (d a (S f))) (d a (S f)))
  rw [U_pair] at h
  simp only [Complex.conj_im] at h
  linarith

private def columnPair (f : QuantumTest) : ℂ :=
  ∑ a : ScalarIndex,sourcePair (P a (U f)) (d a (S f))

private theorem current_normalized_im (f : QuantumTest) :
    (sourcePair f (phiRadiusCurrent (S f))).im= -sourceTime 0*(columnPair f).re := by
  have row (a : ScalarIndex) :
      (sourcePair (P a (U f)) (d a (S f))+sourcePair (d a (U f)) (P a (S f))).re=
        2*(sourcePair (P a (U f)) (d a (S f))).re := by
    have hp := LinearMap.congr_fun (native_inverse a) f
    change P a (S f)-S (P a f)=(-Complex.I) • d a ((S^2) f) at hp
    have hp' := sub_eq_iff_eq_add.mp hp
    rw [hp']
    have hM : sourcePair (d a (U f)) (S (P a f))=
        star (sourcePair (P a (U f)) (d a (S f))) := by
      rw [S_pair]
      have hleft : S (d a (U f))=U (d a (S f)) := by
        have h1 := LinearMap.congr_fun (S_d a).eq (U f)
        have h2 := LinearMap.congr_fun (d_U a).eq (S f)
        have h3 := LinearMap.congr_fun S_U.eq f
        change S (d a (U f))=d a (S (U f)) at h1
        change d a (U (S f))=U (d a (S f)) at h2
        change S (U f)=U (S f) at h3
        rw [h1,h3,h2]
      rw [hleft,←U_pair]
      have hc := LinearMap.congr_fun (original_native_inverse_commute (scalarDirection a)).eq f
      change P a (U f)=U (P a f) at hc
      rw [hc]
      exact (pair_conjugate _ _).symm
    simp only [sourcePair,map_add,map_smul,inner_add_right,inner_smul_right] at hM ⊢
    rw [hM]
    have he := contact_im_zero a f
    unfold sourcePair at he
    simp only [Complex.add_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,
      Complex.I_im,neg_zero,zero_mul,Complex.star_def,Complex.conj_re,he]
    ring
  rw [radius_current_pair]
  have hc (x : ℂ) : ((-Complex.I*(sourceTime 0:ℂ)/2)*x).im= -(sourceTime 0/2)*x.re := by
    simp [Complex.mul_im]
    ring
  rw [hc,Complex.re_sum]
  simp_rw [row]
  simp only [←Finset.mul_sum,columnPair,Complex.re_sum]
  ring

/-- The compression and its full defect are consumed together before taking a norm. -/
def jointFlux (F : Index) (f : QuantumTest) : ℂ :=
  sourcePair (S f) ((bracket (compressionCore F) phiSquare+bracket (defectAction F) phiSquare) (S f))

private theorem joint_flux_source (F : Index) (f : QuantumTest) :
    jointFlux F f=(-2*Complex.I*(sourceTime 0:ℂ))*((columnPair f).re:ℂ) := by
  have hc : bracket (compressionCore F) phiSquare+bracket (defectAction F) phiSquare=
      bracket diagonalAction phiSquare := by
    unfold bracket
    have h : compressionCore F+defectAction F=diagonalAction := by
      simp only [defectAction];abel
    linear_combination (norm:=noncomm_ring) h*phiSquare-phiSquare*h
  have he : bracket diagonalAction phiSquare=phiRadiusCurrent*r+r*phiRadiusCurrent := by
    rw [←original_phi_radius_hamiltonian_current]
    unfold phiSquare bracket
    noncomm_ring
  unfold jointFlux
  rw [hc,he]
  change sourcePair (S f) (phiRadiusCurrent (r (S f))+r (phiRadiusCurrent (S f)))=_
  have hr : r (S f)=f := LinearMap.congr_fun inverse_radius f
  simp only [sourcePair,map_add,inner_add_right]
  change sourcePair (S f) (phiRadiusCurrent (r (S f)))+sourcePair (S f) (r (phiRadiusCurrent (S f)))=_
  rw [hr,r_pair,hr,current_anti]
  rw [←pair_conjugate f (phiRadiusCurrent (S f))]
  have him := current_normalized_im f
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp only [Complex.add_im,Complex.neg_im,Complex.conj_im,Complex.mul_im,
      Complex.neg_re,Complex.re_ofNat,Complex.im_ofNat,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,neg_zero,mul_zero,zero_add,add_zero,him]
    ring

private theorem gram_bound {ι : Type*} [Fintype ι] (p q : ι → QuantumTest) :
    ‖∑ a,sourcePair (p a) (q a)‖^2 ≤ (∑ a,‖embed (p a)‖^2)*(∑ a,‖embed (q a)‖^2) := by
  have h := (norm_sum_le (Finset.univ : Finset ι) (fun a => sourcePair (p a) (q a))).trans
    (Finset.sum_le_sum (fun a _ => norm_inner_le_norm (𝕜 := ℂ) (embed (p a)) (embed (q a))))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => ‖embed (p a)‖) (fun a => ‖embed (q a)‖))

private theorem young_square (a p e η : ℝ) (hp : 0 ≤ p) (he : 0 ≤ e) (hη : 0 < η)
    (hs : a^2 ≤ p*e) : a ≤ η*p+e/(4*η) := by
  have hi : 4*(η*p)*(e/(4*η))=p*e := by field_simp [hη.ne']
  have hr : 0 ≤ η*p+e/(4*η) := add_nonneg (mul_nonneg hη.le hp) (div_nonneg he (by positivity))
  nlinarith only [hs,hi,hr,sq_nonneg (η*p-e/(4*η))]

private theorem joint_flux_square (F : Index) (f : QuantumTest) :
    ‖jointFlux F f‖^2 ≤ (sourceTime 0)^2*scalarForm (U f)*‖embed (S f)‖^2 := by
  have hC := gram_bound (fun a : ScalarIndex => P a (U f)) (fun a => d a (S f))
  have hD := original_phi_gradient_energy (embed (S f))
  simp only [original_phi_direction_core] at hD
  have he : (∑ a : ScalarIndex,‖embed (d a (S f))‖^2) ≤ ‖embed (S f)‖^2/4 := by
    nlinarith only [hD,sq_nonneg ‖phiInverseBounded (embed (S f))‖]
  have hP : 0 ≤ scalarForm (U f) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change ‖columnPair f‖^2 ≤ scalarForm (U f)*(∑ a : ScalarIndex,‖embed (d a (S f))‖^2) at hC
  have hB := hC.trans (mul_le_mul_of_nonneg_left he hP)
  have hR := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm (columnPair f)) 2
  have hnorm : ‖jointFlux F f‖^2=4*(sourceTime 0)^2*((columnPair f).re)^2 := by
    rw [joint_flux_source]
    have htwo : ‖(2:ℂ)‖=2 := by norm_num
    simp only [norm_mul,mul_pow,norm_neg,Complex.norm_I,htwo,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    ring
  rw [hnorm]
  rw [sq_abs] at hR
  have hn := mul_le_mul_of_nonneg_left (hR.trans hB) (by positivity : 0 ≤ 4*(sourceTime 0)^2)
  exact hn.trans_eq (by ring)

/-- The full compression-plus-defect current has no unpriced derivative of the normalized response. -/
theorem original_joint_normalized_flux_price (F : Index) (f : QuantumTest) (η : ℝ) (hη : 0<η) :
    ‖jointFlux F f‖ ≤ η*((sourceTime 0)^2*scalarForm (U f))+‖embed (S f)‖^2/(4*η) := by
  have hp : 0 ≤ (sourceTime 0)^2*scalarForm (U f) :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _=>sq_nonneg _))
  exact young_square _ _ _ η hp (sq_nonneg _) hη (joint_flux_square F f)

/-- The literal response spends the actual positive scalar slot; its remaining vector is bounded. -/
theorem actual_phi_normalized_flux_price (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    ‖jointFlux F (phiResponseCore m ell F z hz g)‖ ≤
      η*phiPositivePrice m ell F z hz g+
      ‖embed (phiInverseAction (phiResponseCore m ell F z hz g))‖^2/(2*η) := by
  let v := phiResponseCore m ell F z hz g
  have h := original_joint_normalized_flux_price F v (η/2) (by positivity)
  have hp := actual_phi_positive_slots m ell F z hz g
  have hc := original_coframe_gram_nonnegative (U v)
  have hs : (sourceTime 0)^2/2*scalarForm (U v) ≤ phiPositivePrice m ell F z hz g := by
    change (sourceTime 0)^2/4*coframeGram (U v)+(sourceTime 0)^2/2*scalarForm (U v)+
      6*(sourceTime 0)^2*‖embed v‖^2 ≤ _ at hp
    nlinarith only [hp,mul_nonneg (by positivity : 0 ≤ (sourceTime 0)^2/4) hc,
      mul_nonneg (by positivity : 0 ≤ 6*(sourceTime 0)^2) (sq_nonneg ‖embed v‖)]
  calc
    _ ≤ (η/2)*((sourceTime 0)^2*scalarForm (U v))+‖embed (S v)‖^2/(4*(η/2)) := h
    _ = η*((sourceTime 0)^2/2*scalarForm (U v))+‖embed (S v)‖^2/(2*η) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hs hη.le) (le_refl _)

end LowEnergy.SourceClockPhiRadiusNormalizedFlux
