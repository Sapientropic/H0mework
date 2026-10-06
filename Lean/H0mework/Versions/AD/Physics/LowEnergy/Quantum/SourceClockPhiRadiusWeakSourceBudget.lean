import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponseHessian
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponsePositiveSource
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponseNativeBudget
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockSourceTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiRadiusWeakSourceBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceClockPhiRadiusResponseHessian SourceClockPhiRadiusResponsePositiveSource SourceClockPhiRadiusResponseNativeBudget
open SourceClockRadiusAffineCutoff SourceClockPhiRadiusSourceCurrent SourceClockYukawaCubicCurrent
open SourceClockSourceTail SourcePhysicalKineticSquare SourceClockReflectedForm
open SourceRadiusHalfSourceBudget SourceLocalizedInverseFormPayment
open SourceClockYukawaQ8RadiusBudget SourceClockYukawaRadialGammaNativeBudget SourceFourPoleEnergyClosed
open SourceActualResolventEnergy FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] resolventCore finiteResolvent thetaHessian bandHessian zeroVector diagonalAction

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore SourceScalarPositiveBulkWard.state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem zero_embed (m ell : ℕ) (hml : m ≤ ell) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (zeroVector m ell F z hz g)=bandBounded m ell hml (finiteResolvent F z (g:H))-
      thetaBounded m ell hml (finiteResolvent F z (phiRadiusSource g:H)) := by
  unfold zeroVector
  simp only [map_sub,←(original_phi_hessian_bounded_core m ell hml _).1,
    ←(original_phi_hessian_bounded_core m ell hml _).2,resolvent_embed]
  have hg : embed (coreEquiv.symm g)=(g:H) := congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hr : embed (SourceClockPhiRadiusSourceCurrent.phiRadiusAction (coreEquiv.symm g))=(phiRadiusSource g:H) := rfl
  rw [hg,hr]

private theorem zero_state_bound (m ell : ℕ) (hml : m ≤ ell) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    ‖embed (zeroVector m ell F z hz g)‖^2 ≤ (12800/(m+2:ℝ)^2)*
      (‖finiteResolvent F z (g:H)‖^2+‖finiteResolvent F z (phiRadiusSource g:H)‖^2) := by
  have hN := original_phi_hessian_norm m ell hml
  have hb := ((bandBounded m ell hml).le_opNorm (finiteResolvent F z (g:H))).trans
    (mul_le_mul_of_nonneg_right hN.1 (norm_nonneg _))
  have ht := ((thetaBounded m ell hml).le_opNorm (finiteResolvent F z (phiRadiusSource g:H))).trans
    (mul_le_mul_of_nonneg_right (hN.2.trans (div_le_div_of_nonneg_right
      (by norm_num : (64:ℝ) ≤ 80) (by positivity))) (norm_nonneg _))
  have hs := norm_sub_le (bandBounded m ell hml (finiteResolvent F z (g:H)))
    (thetaBounded m ell hml (finiteResolvent F z (phiRadiusSource g:H)))
  have h := pow_le_pow_left₀ (norm_nonneg _) (hs.trans (add_le_add hb ht)) 2
  rw [zero_embed m ell hml]
  have he : (12800/(m+2:ℝ)^2)*
      (‖finiteResolvent F z (g:H)‖^2+‖finiteResolvent F z (phiRadiusSource g:H)‖^2)=
      2*(80/(m+2:ℝ))^2*(‖finiteResolvent F z (g:H)‖^2+‖finiteResolvent F z (phiRadiusSource g:H)‖^2) := by
    simp only [div_pow]
    ring
  rw [he]
  nlinarith only [h,sq_nonneg (‖finiteResolvent F z (g:H)‖-‖finiteResolvent F z (phiRadiusSource g:H)‖)]

def zeroEnergy (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  ‖embed (zeroVector m ell F z hz g)‖^2

private theorem finite_star (F : Index) (z : ℂ) : finiteResolvent F (star z)=(finiteResolvent F z).adjoint := by
  unfold finiteResolvent
  change Ring.inverse (GaussGradedCompression.compression F-star z • 1)=
    (Ring.inverse (GaussGradedCompression.compression F-z • 1)).adjoint
  rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
  congr 1
  simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]

private theorem causal_continuous (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (F : Index) :
    Continuous (fun w : ℝ => finiteResolvent F (causalPoint advanced μ w)) := by
  cases advanced
  · exact SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  · have he : (fun w : ℝ => finiteResolvent F (causalPoint true μ w))=
        (fun w : ℝ => (finiteResolvent F (line μ w)).adjoint) := by funext w;exact finite_star F _
    exact he ▸ (ContinuousLinearMap.adjoint.continuous.comp (SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F))

private theorem phi_zero_energy_measurable (m ell : ℕ) (hml : m ≤ ell) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) (advanced : Bool) :
    Measurable (fun w : ℝ => ENNReal.ofReal (zeroEnergy m ell F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g)) := by
  unfold zeroEnergy
  simp_rw [zero_embed m ell hml]
  have hR := causal_continuous advanced μ hμ F
  exact ((((bandBounded m ell hml).continuous.comp (hR.clm_apply continuous_const)).sub
    ((thetaBounded m ell hml).continuous.comp (hR.clm_apply continuous_const))).norm.pow 2).measurable.ennreal_ofReal

private theorem causal_square (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (F : Index) (g : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (causalPoint advanced μ w) g‖^2))=
      ENNReal.ofReal (Real.pi/μ*‖g‖^2) := by
  have hn (w : ℝ) : ‖finiteResolvent F (causalPoint advanced μ w) g‖=‖finiteResolvent F (line μ w) g‖ := by
    cases advanced
    · rfl
    · exact SourceInverseSourceLeg.actual_conjugate_leg_norm F (line μ w)
        (by simpa only [line_im] using hμ.ne') g
  simp_rw [hn]
  simpa only [line,mul_comm (μ:ℂ) Complex.I] using SourceActualResolventEnergy.actual_square_lintegral F μ hμ g

private theorem phi_zero_energy_common_tail (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,∀ advanced : Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (zeroEnergy m ell F (causalPoint advanced μ w)
        (causal_nonreal advanced μ w hμ) g)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := 12800*(Real.pi/μ*(‖(g:H)‖^2+‖(phiRadiusSource g:H)‖^2))
  have hC : 0 ≤ C := by dsimp [C];positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (C/ε)
  refine ⟨N,fun m hm ell hml F advanced => ?_⟩
  have hden : 0 < (m+2:ℝ) := by positivity
  have hN' : C/ε < (m:ℝ)+2 := by
    have hm' : (N:ℝ) ≤ m := by exact_mod_cast hm
    linarith only [hN,hm']
  have htail : C/(m+2:ℝ)^2 ≤ ε := by
    have hlin : C < ε*((m:ℝ)+2) := by simpa only [mul_comm] using (div_lt_iff₀ hε).mp hN'
    have hd2 : (m+2:ℝ) ≤ (m+2:ℝ)^2 := by
      have hm0 : (0:ℝ) ≤ m := by positivity
      nlinarith only [hm0]
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    nlinarith only [hlin,mul_le_mul_of_nonneg_left hd2 hε.le]
  have hmeas : Measurable (fun w : ℝ => ENNReal.ofReal
      (‖finiteResolvent F (causalPoint advanced μ w) (phiRadiusSource g:H)‖^2)) :=
    (((causal_continuous advanced μ hμ F).clm_apply continuous_const).norm.pow 2).measurable.ennreal_ofReal
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (12800/(m+2:ℝ)^2)*
        (ENNReal.ofReal (‖finiteResolvent F (causalPoint advanced μ w) (g:H)‖^2)+
          ENNReal.ofReal (‖finiteResolvent F (causalPoint advanced μ w) (phiRadiusSource g:H)‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ←ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 12800/(m+2:ℝ)^2)]
      exact ENNReal.ofReal_le_ofReal (zero_state_bound m ell hml F _ _ g)
    _=ENNReal.ofReal (12800/(m+2:ℝ)^2)*
        (ENNReal.ofReal (Real.pi/μ*‖(g:H)‖^2)+ENNReal.ofReal (Real.pi/μ*‖(phiRadiusSource g:H)‖^2)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_right _ hmeas,
        causal_square advanced μ hμ F (g:H),causal_square advanced μ hμ F (phiRadiusSource g:H)]
    _=ENNReal.ofReal (C/(m+2:ℝ)^2) := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 12800/(m+2:ℝ)^2)]
      congr 1
      dsimp [C]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal htail

private theorem young (a b η : ℝ) (hη : 0 < η) : a*b ≤ η*a^2+b^2/(4*η) := by
  have he : (4*η)*(b^2/(4*η))=b^2 := by field_simp
  nlinarith only [sq_nonneg (2*η*a-b),he,hη]

private def zeroForcing (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  (-(sourceTime 0:ℂ)/2) • inverseVolumeAction (zeroVector m ell F z hz g)

private theorem zero_pair_price (p : QuantumTest) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    ‖sourcePair p (zeroForcing m ell F z hz g)‖ ≤
      η*(sourceTime 0)^2*coframeGram (inverseVolumeAction p)+zeroEnergy m ell F z hz g/(400*η) := by
  let v := zeroVector m ell F z hz g
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hp : sourcePair p (inverseVolumeAction v)=sourcePair (inverseVolumeAction p) v := multiply_pair _ _ _ _
  change ‖sourcePair p ((-(sourceTime 0:ℂ)/2) • inverseVolumeAction v)‖ ≤ _
  rw [show sourcePair p ((-(sourceTime 0:ℂ)/2) • inverseVolumeAction v)=
    (-(sourceTime 0:ℂ)/2)*sourcePair p (inverseVolumeAction v) by simp only [sourcePair,map_smul,inner_smul_right]]
  rw [hp,norm_mul,norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn]
  norm_num only [Complex.norm_ofNat]
  have hi := mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℂ) (embed (inverseVolumeAction p)) (embed v))
    (by positivity : 0 ≤ sourceTime 0/2)
  change (sourceTime 0/2)*‖sourcePair (inverseVolumeAction p) v‖ ≤
    (sourceTime 0/2)*(‖embed (inverseVolumeAction p)‖*‖embed v‖) at hi
  have hf := original_inverse_coframe_floor (inverseVolumeAction p)
  have hy := young (5*sourceTime 0*‖embed (inverseVolumeAction p)‖) ((1/10)*‖embed v‖) η hη
  have he : ((1/10)*‖embed v‖)^2/(4*η)=‖embed v‖^2/(400*η) := by field_simp;ring
  rw [he] at hy
  have hv : ‖embed v‖^2=zeroEnergy m ell F z hz g := rfl
  rw [hv] at hy
  have hb := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ η*(sourceTime 0)^2)
  change (sourceTime 0/2)*‖sourcePair (inverseVolumeAction p) v‖ ≤ _
  nlinarith only [hi,hy,hb]

def remainingPrice (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) (α : ℝ) : ℝ :=
  α*phiPositivePrice m ell F z hz g-
    (sourcePair (phiResponseCore m ell F z hz g) (phiCoherentDefect m ell F z hz g)).im

def remainingBudget (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (α : ℝ) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (remainingPrice m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g α)

private theorem response_mu_ward (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    z.im*‖embed (phiResponseCore m ell F z hz g)‖^2=
      -(sourcePair (phiResponseCore m ell F z hz g) (phiResponseSource m ell F z hz g)).im := by
  let v := phiResponseCore m ell F z hz g
  have h0 : (sourcePair v (diagonalAction v)).im=0 := by
    have hp := congrArg Complex.im (GaussNativeForm.pair_conjugate v (diagonalAction v))
    rw [←diagonalAction_pair] at hp
    simp only [Complex.conj_im] at hp
    linarith only [hp]
  let f := phiResponseSource m ell F z hz g
  have he : diagonalAction v=f+z • v := actual_phi_response_source m ell F z hz g
  have hp : sourcePair v (diagonalAction v)=sourcePair v f+z*sourcePair v v := by
    rw [he]
    simp only [sourcePair,map_add,map_smul,inner_add_right,inner_smul_right]
  have h := congrArg Complex.im hp
  rw [h0] at h
  have hn : sourcePair v v=((‖embed v‖^2:ℝ):ℂ) := by
    simpa only [sourcePair,Complex.ofReal_pow] using! inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (embed v)
  rw [hn] at h
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add] at h
  change z.im*‖embed v‖^2=-(sourcePair v f).im
  linarith only [h]

/-- Native and Hessian errors are paid inside a single complete source price. -/
theorem actual_phi_weak_source_price (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (α : ℝ) (hα : 0<α) :
    z.im*‖embed (phiResponseCore m ell F z hz g)‖^2 ≤ remainingPrice m ell F z hz g α+
      phiNativeEnergy m ell F z hz g/(2*α)+zeroEnergy m ell F z hz g/(100*α) := by
  let v := phiResponseCore m ell F z hz g
  have he : phiResponseSource m ell F z hz g=
      phiNativeDivergence m ell F z hz g+zeroForcing m ell F z hz g+phiCoherentDefect m ell F z hz g := by
    rw [actual_phi_response_forcing]
    unfold zeroForcing
    module
  have h := response_mu_ward m ell F z hz g
  rw [he] at h
  have hn := actual_phi_native_pair_price v m ell F z hz g (α/2) (by positivity)
  have hZ := zero_pair_price v m ell F z hz g (α/4) (by positivity)
  have nN := (neg_le_abs (sourcePair v (phiNativeDivergence m ell F z hz g)).im).trans (Complex.abs_im_le_norm _)
  have zN := (neg_le_abs (sourcePair v (zeroForcing m ell F z hz g)).im).trans (Complex.abs_im_le_norm _)
  have hp := actual_phi_positive_slots m ell F z hz g
  have hb : (α/2)*((sourceTime 0)^2*scalarForm (inverseVolumeAction v))+
      (α/4)*(sourceTime 0)^2*coframeGram (inverseVolumeAction v) ≤ α*phiPositivePrice m ell F z hz g := by
    have ht := mul_le_mul_of_nonneg_left hp hα.le
    have hr : 0 ≤ α*(6*(sourceTime 0)^2*‖embed v‖^2) := by positivity
    nlinarith only [ht,hr]
  unfold remainingPrice
  simp only [sourcePair,map_add,inner_add_right,Complex.add_im] at h
  change z.im*‖embed v‖^2 ≤ _
  have hdn : 4*(α/2)=2*α := by ring
  have hdz : 400*(α/4)=100*α := by ring
  rw [hdn] at hn
  rw [hdz] at hZ
  dsimp only [v] at hn hZ nN zN hb ⊢
  unfold sourcePair at hn hZ nN zN ⊢
  linarith only [h,hn,hZ,nN,zN,hb]

private theorem line_nonreal (μ : ℝ) (hμ : 0<μ) (w : ℝ) : (line μ w).im≠0 := by
  simpa only [line_im] using hμ.ne'

private theorem weak_integral (m ell : ℕ) (hml : m ≤ ell) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (α : ℝ) (hα : 0<α) :
    phiResponseBudget m ell F μ hμ g ≤ remainingBudget m ell F μ hμ g α+
      ENNReal.ofReal (1/(2*α))*(∫⁻ w : ℝ,ENNReal.ofReal (phiNativeEnergy m ell F (line μ w) (line_nonreal μ hμ w) g))+
      ENNReal.ofReal (1/(100*α))*(∫⁻ w : ℝ,ENNReal.ofReal (zeroEnergy m ell F (line μ w) (line_nonreal μ hμ w) g)) := by
  have hG := actual_phi_native_energy_measurable m ell F μ hμ g false
  have hZ := phi_zero_energy_measurable m ell hml F μ hμ g false
  change Measurable (fun w : ℝ => ENNReal.ofReal (phiNativeEnergy m ell F (line μ w) _ g)) at hG
  change Measurable (fun w : ℝ => ENNReal.ofReal (zeroEnergy m ell F (line μ w) _ g)) at hZ
  unfold phiResponseBudget remainingBudget
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (remainingPrice m ell F (line μ w) (line_nonreal μ hμ w) g α)+
        ENNReal.ofReal (1/(2*α))*ENNReal.ofReal (phiNativeEnergy m ell F (line μ w) (line_nonreal μ hμ w) g)+
        ENNReal.ofReal (1/(100*α))*ENNReal.ofReal (zeroEnergy m ell F (line μ w) (line_nonreal μ hμ w) g) := by
      apply lintegral_mono
      intro w
      have hp := actual_phi_weak_source_price m ell F (line μ w) (line_nonreal μ hμ w) g α hα
      simp only [line_im] at hp
      have hq : ∀x:ℝ,x/(2*α)=(1/(2*α))*x := by intro x;ring
      have hz : ∀x:ℝ,x/(100*α)=(1/(100*α))*x := by intro x;ring
      rw [hq,hz] at hp
      exact (ENNReal.ofReal_le_ofReal hp).trans
        (ENNReal.ofReal_add_le.trans (add_le_add
          (ENNReal.ofReal_add_le.trans (add_le_add le_rfl
            (le_of_eq (ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(2*α))))))
          (le_of_eq (ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(100*α))))))
    _ = _ := by
      rw [lintegral_add_right _ (hZ.const_mul _),lintegral_add_right _ (hG.const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The actual native and zero vectors pay internally; only one clipped full coherent-defect price remains. -/
theorem actual_phi_weak_source_payment (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (α : ℝ) (hα : 0<α) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),
      phiResponseBudget m ell F μ hμ g ≤ ENNReal.ofReal ε+remainingBudget m ell F μ hμ g α := by
  intro ε hε
  obtain ⟨NG,hG⟩ := actual_phi_native_energy_common_tail μ hμ g (α*ε) (by positivity)
  obtain ⟨NZ,hZ⟩ := phi_zero_energy_common_tail μ hμ g (50*α*ε) (by positivity)
  refine ⟨max NG NZ,fun m hm ell hml => ?_⟩
  filter_upwards [hG m (by omega) ell hml] with F hGF
  have hg := hGF false
  have hz := hZ m (by omega) ell hml F false
  have hb := weak_integral m ell hml F μ hμ g α hα
  have cg : ENNReal.ofReal (1/(2*α))*ENNReal.ofReal (α*ε)=ENNReal.ofReal (ε/2) := by
    rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(2*α))]
    congr 1
    field_simp [hα.ne']
  have cz : ENNReal.ofReal (1/(100*α))*ENNReal.ofReal (50*α*ε)=ENNReal.ofReal (ε/2) := by
    rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(100*α))]
    congr 1
    field_simp [hα.ne']
    ring
  have ht := hb.trans (add_le_add (add_le_add le_rfl
    (mul_le_mul le_rfl hg zero_le zero_le)) (mul_le_mul le_rfl hz zero_le zero_le))
  rw [cg,cz] at ht
  have he : remainingBudget m ell F μ hμ g α+ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2)=
      ENNReal.ofReal ε+remainingBudget m ell F μ hμ g α := by
    rw [add_assoc,←ENNReal.ofReal_add (by positivity) (by positivity)]
    have hr : ε/2+ε/2=ε := by ring
    rw [hr,add_comm]
  exact ht.trans_eq he

/-- Original Gamma consumes the same homogeneous response and the internally paid full source errors. -/
theorem actual_original_phi_weak_Gamma_budget (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (α : ℝ) (hα : 0<α) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),
      ∀ sharp : Bool,ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
        ENNReal.ofReal ε+ENNReal.ofReal (24*sourceMuFactor μ k*radiusPrice)*remainingBudget m ell F μ hμ g α := by
  intro ε hε
  let C := 6*sourceMuFactor μ k*radiusPrice
  have hC : 0 ≤ C := by dsimp [C];unfold sourceMuFactor radiusPrice;positivity
  let δ := ε/(10*(C+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨N1,h1⟩ := actual_original_Q8_radius_response_budget μ hμ g k (ε/2) (by positivity)
  obtain ⟨N2,h2⟩ := actual_original_radius_homogeneous_budget μ hμ g δ hδ
  obtain ⟨N3,h3⟩ := actual_phi_weak_source_payment μ hμ g α hα δ hδ
  refine ⟨max N1 (max N2 N3),fun m hm ell hml => ?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml,h3 m (by omega) ell hml] with F hg hr hp
  intro sharp
  have hx := hr.trans (add_le_add le_rfl (mul_le_mul le_rfl hp zero_le zero_le))
  have heδ : ENNReal.ofReal δ+4*ENNReal.ofReal δ=ENNReal.ofReal (5*δ) := by
    rw [show (4:ENNReal)=ENNReal.ofReal (4:ℝ) by norm_num,←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),
      ←ENNReal.ofReal_add hδ.le (by positivity)]
    congr 1
    ring
  rw [mul_add,←add_assoc,heδ] at hx
  have hb := (hg sharp).trans (add_le_add le_rfl (mul_le_mul le_rfl hx zero_le zero_le))
  have halloc : ε/2+C*(5*δ) ≤ ε := by
    have hs : C*(5*δ) ≤ ε/2 := by
      dsimp only [δ]
      rw [←mul_div_assoc,←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < 10*(C+1))).mpr
      nlinarith only [hε]
    linarith only [hs]
  have hcoef : ENNReal.ofReal C*4=ENNReal.ofReal (24*sourceMuFactor μ k*radiusPrice) := by
    rw [show (4:ENNReal)=ENNReal.ofReal (4:ℝ) by norm_num,←ENNReal.ofReal_mul hC]
    congr 1
    dsimp [C]
    ring
  change _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal C*(ENNReal.ofReal (5*δ)+4*remainingBudget m ell F μ hμ g α) at hb
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal C*(ENNReal.ofReal (5*δ)+4*remainingBudget m ell F μ hμ g α) := hb
    _ = ENNReal.ofReal (ε/2+C*(5*δ))+
        ENNReal.ofReal (24*sourceMuFactor μ k*radiusPrice)*remainingBudget m ell F μ hμ g α := by
      rw [mul_add,←mul_assoc,hcoef,←ENNReal.ofReal_mul hC,←add_assoc,
        ←ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := add_le_add (ENNReal.ofReal_le_ofReal halloc) le_rfl

end LowEnergy.SourceClockPhiRadiusWeakSourceBudget
