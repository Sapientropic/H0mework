import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiNativeWeightedHardy
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiNativeJointPayment
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeSourceJetEnergy
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceResolventLorentzian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiNativeSignedCurrent
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussFockWeights GaussDensityCore SourceRelativePowerTail
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockPhiRadiusResponseHessian
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourcePhysicalKineticSquare SourceScalarPairedTransport
open SourceClockYukawaCubicCurrent SourceClockPhiRadiusResponsePositiveSource SourceClockPhiRadiusClockSturm
open SourceInverseJetEnergy FullYSourceResolventGraphSplice SourceLocalizedInverseFormPayment SourceResolventBandLimit
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev E : End := phiEulerAction
private abbrev Phi : End := SourceScalarAffineScaleTransport.generator
private abbrev U : End := inverseVolumeAction
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
private abbrev T (m ell : ℕ) : End := phiThetaAction m ell
private abbrev M (m ell : ℕ) : End := U*(T m ell)^2
private abbrev n : ℝ := sourceTime 0
attribute [local irreducible] resolventCore compressionCore defectAction diagonalAction
  SourceScalarPositiveBulkWard.state GaussAdjointHistory.coreStep

/-- The original affine generator is symmetrized with the actual phi cutoff and U, on the core. -/
def weightedGenerator (m ell : ℕ) : End := (1/2:ℂ) • (M m ell*Phi+Phi*M m ell)
private def phiBulk : End := (-2:ℂ) • scalarKinetic+(2:ℂ) • centeredAction-
  (2:ℂ) • vacuumLinearAction+(2:ℂ) • scalarSpatialAction
private def windowCurrent (m ell : ℕ) : End :=
  (-3*Complex.I*(n:ℂ)/4) • (U*SourceCoframeVolumeCurrent.dilation*U*(T m ell)^2)+
    U*bracket ((T m ell)^2) scalarKinetic
/-- Coframe, scalar and local source fields remain in the same anticommutator. -/
def fieldCurrent (m ell : ℕ) : End := (1/2:ℂ) •
  (M m ell*phiBulk+phiBulk*M m ell+windowCurrent m ell*Phi+Phi*windowCurrent m ell)

private theorem pair_add_l (f g h:QuantumTest) : sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_r (f g h:QuantumTest) : sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_l (f g h:QuantumTest) : sourcePair (f-g) h=sourcePair f h-sourcePair g h := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r (f g h:QuantumTest) : sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l (c:ℂ) (f g:QuantumTest) : sourcePair (c • f) g=(starRingEnd ℂ c)*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_left]
private theorem pair_smul_r (c:ℂ) (f g:QuantumTest) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem phi_pair (f g:QuantumTest) : sourcePair f (Phi g)= -sourcePair (Phi f) g := by
  have h:=SourceClockPhiRadiusClockSturm.phi_profile_paired_derivative (1:End) f g
  have hz:bracket E (1:End)=0 := by simp [bracket]
  rw [hz] at h
  simp only [Module.End.one_apply,zero_add,LinearMap.smul_apply] at h
  change sourcePair f (E g)= -sourcePair (E f) g-sourcePair f ((61:ℂ) • g) at h
  simp only [Phi,SourceScalarAffineScaleTransport.generator,LinearMap.add_apply,
    LinearMap.smul_apply,Module.End.one_apply,pair_add_l,pair_add_r,pair_smul_l,pair_smul_r] at h ⊢
  norm_num only [map_div₀,map_ofNat,map_one]
  linear_combination (norm:=ring) h
private theorem real_commute (a b:SourceCoordinateSlice → ℝ)
    (ha:∀z:physicalChart,ContDiffAt ℝ ∞ a z.val) (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val) :
    Commute (multiply a ha) (multiply b hb) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (a z:ℂ) (b z:ℂ) (f z)
private theorem inverse_radius : S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem radius_inverse : r*S=(1:End) := (real_commute _ _ _ _).eq.symm.trans inverse_radius
private theorem commute_inverse {A:End} (ha:Commute A r) : Commute A S := by
  change A*S=S*A
  have h:=congrArg (fun B:End=>S*B*S) ha.eq
  simp only [mul_assoc,radius_inverse,mul_one] at h
  simpa only [←mul_assoc,inverse_radius,one_mul] using h.symm
private theorem theta_commute {A:End} (ha:Commute A S) (m ell:ℕ) : Commute A (T m ell) :=
  (((Commute.one_right A).sub_right ha).pow_right (m+1)).sub_right
    (((Commute.one_right A).sub_right ha).pow_right (ell+1))
private theorem pair_product {A B:End} (ha:GaussCoframeForm.Paired A A)
    (hb:GaussCoframeForm.Paired B B) (hc:Commute A B) : GaussCoframeForm.Paired (A*B) (A*B) := by
  intro f g
  change sourcePair f (A (B g))=sourcePair (A (B f)) g
  rw [ha,hb]
  exact congrArg (fun p=>sourcePair p g) (LinearMap.congr_fun hc.eq f).symm
private theorem pair_power {A:End} (ha:GaussCoframeForm.Paired A A) (k:ℕ) : GaussCoframeForm.Paired (A^k) (A^k) := by
  induction k with
  | zero => intro f g;rfl
  | succ k ih => rw [pow_succ];exact pair_product ih ha ((Commute.refl A).pow_left k)
private theorem pair_sub {A B:End} (ha:GaussCoframeForm.Paired A A)
    (hb:GaussCoframeForm.Paired B B) : GaussCoframeForm.Paired (A-B) (A-B) := by
  intro f g
  simp only [LinearMap.sub_apply,pair_sub_l,pair_sub_r]
  rw [ha f g,hb f g]
private theorem theta_pair (m ell:ℕ) : GaussCoframeForm.Paired (T m ell) (T m ell) := by
  have h1:GaussCoframeForm.Paired (1:End) 1 := by intro f g;rfl
  exact pair_sub (pair_power (pair_sub h1 (multiply_pair _ _)) (m+1))
    (pair_power (pair_sub h1 (multiply_pair _ _)) (ell+1))
private theorem weight_pair (m ell:ℕ) : GaussCoframeForm.Paired (M m ell) (M m ell) :=
  pair_product (multiply_pair _ _) (pair_power (theta_pair m ell) 2)
    ((theta_commute (real_commute _ _ _ _) m ell).pow_right 2)
private theorem generator_pair (m ell:ℕ) (f g:QuantumTest) :
    sourcePair f (weightedGenerator m ell g)= -sourcePair (weightedGenerator m ell f) g := by
  have h1:sourcePair f (M m ell (Phi g))= -sourcePair (Phi (M m ell f)) g := by
    rw [weight_pair,phi_pair]
  have h2:sourcePair f (Phi (M m ell g))= -sourcePair (M m ell (Phi f)) g := by
    rw [phi_pair,weight_pair]
  unfold weightedGenerator
  simp only [LinearMap.smul_apply,LinearMap.add_apply,pair_smul_l,pair_smul_r,pair_add_l,pair_add_r]
  change (1/2:ℂ)*(sourcePair f (M m ell (Phi g))+sourcePair f (Phi (M m ell g)))=
    -(starRingEnd ℂ (1/2:ℂ)*(sourcePair (M m ell (Phi f)) g+sourcePair (Phi (M m ell f)) g))
  rw [h1,h2]
  norm_num only [map_div₀,map_one,map_ofNat]
  ring
private theorem full_radial_current (m ell:ℕ) : bracket ((T m ell)^2) diagonalAction=
    bracket ((T m ell)^2) scalarKinetic := by
  have hc:=((theta_commute (commute_inverse original_phi_radius_non_scalar_commute.2.2.2) m ell).pow_right 2).eq
  unfold bracket
  linear_combination (norm:=noncomm_ring) -hc
private theorem phi_bulk_source : bracket Phi diagonalAction=phiBulk := by
  have h:=SourceScalarVirialBulk.original_scalar_gauge_current
  rw [SourceInverseHamiltonianForceReduction.original_hamiltonian_gauge_source] at h
  have he:=SourceScalarAffineScaleTransport.generator_commutator diagonalAction
  change Phi*diagonalAction-diagonalAction*Phi=E*diagonalAction-diagonalAction*E at he
  change bracket Phi diagonalAction=phiBulk
  unfold phiBulk bracket
  change (E*diagonalAction-diagonalAction*E)-_=_ at h
  linear_combination (norm:=module) h+he
private theorem window_current_source (m ell:ℕ) : bracket (M m ell) diagonalAction=windowCurrent m ell := by
  have hu:=SourceScalarInverseRetardedBudget.original_inverse_current
  change diagonalAction*U-U*diagonalAction=(3*Complex.I*(n:ℂ)/4) •
    (U*SourceCoframeVolumeCurrent.dilation*U) at hu
  have ht:=full_radial_current m ell
  unfold bracket at ht
  unfold windowCurrent M bracket
  simp only [neg_mul,neg_div,neg_smul]
  linear_combination (norm:=noncomm_ring) -hu*(T m ell)^2+U*ht

/-- Both complete source currents use the original phi/coframe fields, before the full compression defect is inserted. -/
theorem original_weighted_phi_field_source (m ell:ℕ) :
    bracket (weightedGenerator m ell) diagonalAction=fieldCurrent m ell := by
  have hp (A B H:End):bracket (A*B) H=A*bracket B H+bracket A H*B := by
    unfold bracket;noncomm_ring
  have ha (A B H:End):bracket (A+B) H=bracket A H+bracket B H := by
    unfold bracket;noncomm_ring
  have hc (c:ℂ) (A H:End):bracket (c • A) H=c • bracket A H := by
    simp only [bracket,smul_mul_assoc,mul_smul_comm,smul_sub]
  rw [weightedGenerator,hc,ha,hp (M m ell) Phi diagonalAction,
    hp Phi (M m ell) diagonalAction,phi_bulk_source,window_current_source]
  unfold fieldCurrent
  module

private theorem compression_pair (F:Index) : GaussCoframeForm.Paired (compressionCore F) (compressionCore F) := by
  intro f g
  have he (u:QuantumTest):embed (compressionCore F u)=GaussGradedCompression.compression F (embed u) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  simp only [sourcePair,he]
  exact (GaussGradedCompression.compression_pair F _ _).symm
private theorem resolvent_source (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    compressionCore F (resolventCore F z hz (coreEquiv.symm g))=
      coreEquiv.symm g+z • resolventCore F z hz (coreEquiv.symm g) := by
  have he (u:QuantumTest):embed (compressionCore F u)=GaussGradedCompression.compression F (embed u) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hr (u:QuantumTest):embed (resolventCore F z hz u)=finiteResolvent F z (embed u) := by
    unfold resolventCore SourceScalarPositiveBulkWard.state
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have h:=congrArg (fun A:H →L[ℂ] H=>A (g:H))
    (resolvent_right (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
  apply embed_injective
  simp only [he,hr,map_add,map_smul]
  have hg:embed (coreEquiv.symm g)=(g:H) := congrArg Subtype.val (coreEquiv.apply_symm_apply g)
  rw [hg]
  change (GaussGradedCompression.compression F-z • 1) (finiteResolvent F z (g:H))=(g:H) at h
  simp only [sub_apply,smul_apply,one_apply_eq_self] at h
  linear_combination (norm:=module) h

private theorem paired_resolvent_current (A C:End)
    (hA:∀f g:QuantumTest,sourcePair f (A g)= -sourcePair (A f) g)
    (hC:GaussCoframeForm.Paired C C) (q f:QuantumTest) (z:ℂ)
    (hq:C q=f+z • q) :
    (sourcePair q (bracket A C q)).re=
      -2*(sourcePair (A q) f).re+2*z.im*(sourcePair (A q) q).im := by
  change (sourcePair q (A (C q)-C (A q))).re=_
  rw [pair_sub_r,hA q (C q),hC q (A q),hq,pair_add_r,pair_smul_r,pair_add_l,pair_smul_l]
  rw [hA q q,←pair_conjugate (A q) f]
  simp only [Complex.sub_re,Complex.neg_re,Complex.add_re,Complex.mul_re,Complex.conj_re,
    Complex.conj_im,Complex.neg_im]
  ring
private theorem generator_source_pair (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    let q:=resolventCore F z hz (coreEquiv.symm g)
    (sourcePair q (bracket (weightedGenerator m ell) (compressionCore F) q)).re=
      -2*(sourcePair (weightedGenerator m ell q) (coreEquiv.symm g)).re+
        2*z.im*(sourcePair (weightedGenerator m ell q) q).im :=
  paired_resolvent_current _ _ (generator_pair m ell) (compression_pair F) _ _ z
    (resolvent_source F z hz g)

private abbrev W (m ell:ℕ) : End := U*S*T m ell
private theorem W_pair (m ell:ℕ) : GaussCoframeForm.Paired (W m ell) (W m ell) := by
  have hUS:Commute U S:=real_commute _ _ _ _
  have hU:Commute U (T m ell):=theta_commute hUS m ell
  have hS:Commute S (T m ell):=theta_commute (Commute.refl S) m ell
  exact pair_product (pair_product (multiply_pair _ _) (multiply_pair _ _) hUS)
    (theta_pair m ell) (hU.mul_left hS)
private theorem W_radius (m ell:ℕ) : W m ell*r*T m ell=M m ell := by
  have hS:Commute S r:=inverse_radius.trans radius_inverse.symm
  have hT:=theta_commute hS.symm m ell
  change U*S*T m ell*r*T m ell=U*(T m ell)^2
  calc _=U*(S*(T m ell*r))*T m ell := by simp only [mul_assoc]
       _=U*(S*(r*T m ell))*T m ell := by rw [←hT.eq]
       _=U*(S*r)*((T m ell)^2) := by simp only [mul_assoc,pow_two]
       _=_ := by rw [inverse_radius,mul_one]
private theorem generator_phase (m ell:ℕ) (q h:QuantumTest) :
    (sourcePair (weightedGenerator m ell q) q).im=
      (sourcePair (W m ell (Phi q)) (T m ell (r q-h))).im+
      (sourcePair (W m ell (Phi q)) (T m ell h)).im := by
  let c:=sourcePair (Phi q) (M m ell q)
  have hm:sourcePair (M m ell (Phi q)) q=c := (weight_pair m ell (Phi q) q).symm
  have hp:sourcePair (Phi (M m ell q)) q= -(starRingEnd ℂ c) := by
    calc _= -sourcePair (M m ell q) (Phi q) := by
           linear_combination (norm:=ring) phi_pair (M m ell q) q
         _=_ := congrArg Neg.neg (pair_conjugate (Phi q) (M m ell q)).symm
  have he:sourcePair (weightedGenerator m ell q) q=(1/2:ℂ)*(c-starRingEnd ℂ c) := by
    unfold weightedGenerator
    simp only [LinearMap.smul_apply,LinearMap.add_apply,Module.End.mul_apply,pair_smul_l,pair_add_l]
    change (starRingEnd ℂ (1/2:ℂ))*(sourcePair (M m ell (Phi q)) q+sourcePair (Phi (M m ell q)) q)=_
    rw [hm,hp]
    norm_num only [map_div₀,map_one,map_ofNat]
    ring
  have hi:(sourcePair (weightedGenerator m ell q) q).im=c.im := by
    rw [he]
    simp only [Complex.mul_im,Complex.sub_im,Complex.conj_im,Complex.one_re,Complex.one_im,
      Complex.div_re,Complex.div_im,Complex.re_ofNat,Complex.im_ofNat,Complex.normSq_ofNat]
    ring
  have hc:c=sourcePair (W m ell (Phi q)) (r (T m ell q)) := by
    rw [←W_pair]
    exact congrArg (sourcePair (Phi q)) (LinearMap.congr_fun (W_radius m ell) q).symm
  rw [hi,hc]
  have hT:Commute r (T m ell):=theta_commute (real_commute _ _ _ _) m ell
  have ht:=LinearMap.congr_fun hT.eq q
  change r (T m ell q)=T m ell (r q) at ht
  rw [ht]
  simp only [map_sub,pair_sub_r,Complex.sub_im]
  ring

/-- The original field and the complete same-F defect share one signed phi-current. -/
def signedCurrent (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) : ℝ :=
  let q:=resolventCore F z hz (coreEquiv.symm g)
  (sourcePair q ((fieldCurrent m ell-bracket (weightedGenerator m ell) (defectAction F)) q)).re-
    2*z.im*(sourcePair (W m ell (Phi q)) (phiResponseCore m ell F z hz g)).im
private theorem signed_current_return (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    let q:=resolventCore F z hz (coreEquiv.symm g)
    let h:=resolventCore F z hz (r (coreEquiv.symm g))
    signedCurrent m ell F z hz g=
      -2*(sourcePair (weightedGenerator m ell q) (coreEquiv.symm g)).re+
        2*z.im*(sourcePair (W m ell (Phi q)) (T m ell h)).im := by
  let q:=resolventCore F z hz (coreEquiv.symm g)
  let h:=resolventCore F z hz (r (coreEquiv.symm g))
  have hC:fieldCurrent m ell-bracket (weightedGenerator m ell) (defectAction F)=
      bracket (weightedGenerator m ell) (compressionCore F) := by
    rw [←original_weighted_phi_field_source]
    unfold bracket defectAction
    noncomm_ring
  have hsource:=generator_source_pair m ell F z hz g
  have hphase:=generator_phase m ell q h
  have hv:T m ell (r q-h)=phiResponseCore m ell F z hz g := by
    unfold phiResponseCore bracket
    rfl
  unfold signedCurrent
  rw [hC]
  dsimp only at hsource ⊢
  rw [hv] at hphase
  dsimp only [q,h] at hphase
  linear_combination (norm:=ring) hsource+(2*z.im)*hphase

private abbrev Op := H →L[ℂ] H
private abbrev Q : End := 1-S
private abbrev B (m ell:ℕ) : End := phiFirstPeak m ell
private abbrev delta : End := S^3-S
private theorem phi_inverse_core (f:QuantumTest) : phiInverseBounded (embed f)=embed (phiInverseAction f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
private theorem phi_inverse_norm : ‖phiInverseBounded‖    ≤    1 := GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem phi_inverse_pair (x y:H) : inner ℂ (phiInverseBounded x) y=inner ℂ x (phiInverseBounded y) := by
  refine GaussBoundedMultiplier.core_dense.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
  intro a b
  obtain ⟨f,rfl⟩:=coreEquiv.surjective a
  obtain ⟨g,rfl⟩:=coreEquiv.surjective b
  change inner ℂ (phiInverseBounded (embed f)) (embed g)=inner ℂ (embed f) (phiInverseBounded (embed g))
  rw [phi_inverse_core,phi_inverse_core]
  exact (multiply_pair _ _ _ _).symm
private theorem phi_inverse_positive : 0    ≤    phiInverseBounded := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  refine ⟨phi_inverse_pair,?_⟩
  intro x
  change 0    ≤    (inner ℂ (phiInverseBounded x) x).re
  rw [phi_inverse_pair]
  refine GaussBoundedMultiplier.core_dense.induction_on x (isClosed_le continuous_const (by fun_prop)) ?_
  intro a
  obtain ⟨f,rfl⟩:=coreEquiv.surjective a
  change 0    ≤    (inner ℂ (embed f) (phiInverseBounded (embed f))).re
  rw [phi_inverse_core]
  change 0    ≤    (sourcePair f (phiInverseAction f)).re
  rw [sourcePair_integral]
  have hr:(∫z,densityPair f (phiInverseAction f) z ∂GaussHistoryHilbert.configurationMeasure).re=
      ∫z,(densityPair f (phiInverseAction f) z).re ∂GaussHistoryHilbert.configurationMeasure := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re (densityPair_integrable f (phiInverseAction f))).symm
  rw [hr]
  apply integral_nonneg
  intro z
  change 0    ≤    (densityPair f (phiInverseAction f) z).re
  by_cases hz:z∈physicalChart
  · have hp:0    ≤    (densityPair f f z).re := by
      change 0    ≤    RCLike.re (inner ℂ (weight (fun N=>(density N z:ℂ)) (f z)) (f z))
      rw [GaussBoundedMultiplier.weighted_square _ (fun N=>(density_pos N ⟨z,hz⟩).le)]
      exact sq_nonneg _
    have he:densityPair f (phiInverseAction f) z=(phiReciprocal z:ℂ)*densityPair f f z :=
      inner_smul_right _ _ _
    rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hp
  · have hf:f z=0 := image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]
private def phiComplement : Op := 1-phiInverseBounded
private theorem phi_complement_positive : 0    ≤    phiComplement :=
  sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg _ phi_inverse_positive).mp phi_inverse_norm)
private theorem phi_complement_le_one : phiComplement    ≤    1 := sub_le_self _ phi_inverse_positive
/-- The same actual affine radial powers, on the full weighted Hilbert space. -/
private def phiTail (m ell:ℕ) : Op := phiComplement^(m+1)-phiComplement^(ell+1)
private theorem phi_power_core (n:ℕ) (f:QuantumTest) :
    (phiComplement^n) (embed f)=embed (((1-phiInverseAction)^n) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change phiComplement ((phiComplement^n) (embed f))=embed ((1-phiInverseAction) (((1-phiInverseAction)^n) f))
    rw [ih]
    change embed (((1-phiInverseAction)^n) f)-phiInverseBounded (embed (((1-phiInverseAction)^n) f))=_
    rw [phi_inverse_core,←map_sub]
    rfl
private theorem phi_tail_core (m ell:ℕ) (f:QuantumTest) :
    phiTail m ell (embed f)=embed (phiThetaAction m ell f) := by
  simp only [phiTail,sub_apply,phi_power_core,phiThetaAction,LinearMap.sub_apply,map_sub]

private def boundary (n:ℕ) : Op := PositiveContractionRitt.gradient phiComplement n
private def peak (m ell:ℕ) : Op := boundary ell-boundary m
private theorem boundary_norm (n:ℕ) : ‖boundary n‖    ≤    1 :=
  PositiveContractionRitt.gradient_norm phiComplement phi_complement_positive phi_complement_le_one n
private theorem peak_norm (m ell:ℕ) : ‖peak m ell‖    ≤    2 := by
  exact (norm_sub_le _ _).trans ((add_le_add (boundary_norm ell) (boundary_norm m)).trans_eq (by norm_num))
private theorem theta_norm (m ell:ℕ) : ‖phiTail m ell‖    ≤    2 := by
  have hQ:‖phiComplement‖    ≤    1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ phi_complement_positive).mpr phi_complement_le_one
  have hpow (k:ℕ):‖phiComplement^k‖    ≤    1 := by
    induction k with
    | zero =>
      rw [pow_zero]
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      change ‖x‖    ≤    1*‖x‖
      rw [one_mul]
    | succ k ih =>
      rw [pow_succ]
      exact (norm_mul_le _ _).trans ((mul_le_mul ih hQ (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  unfold phiTail
  exact (norm_sub_le _ _).trans ((add_le_add (hpow _) (hpow _)).trans_eq (by norm_num))
private def CoreReturn (A:Op) (a:End) : Prop := ∀f:QuantumTest,A (embed f)=embed (a f)
private theorem core_mul {A B:Op} {a b:End} (ha:CoreReturn A a) (hb:CoreReturn B b) :
    CoreReturn (A*B) (a*b) := by intro f;change A (B (embed f))=embed (a (b f));rw [hb,ha]
private theorem core_add {A B:Op} {a b:End} (ha:CoreReturn A a) (hb:CoreReturn B b) :
    CoreReturn (A+B) (a+b) := by intro f;change A (embed f)+B (embed f)=embed (a f+b f);rw [ha,hb,map_add]
private theorem core_sub {A B:Op} {a b:End} (ha:CoreReturn A a) (hb:CoreReturn B b) :
    CoreReturn (A-B) (a-b) := by intro f;change A (embed f)-B (embed f)=embed (a f-b f);rw [ha,hb,map_sub]
private theorem core_smul {A:Op} {a:End} (ha:CoreReturn A a) (c:ℂ) :
    CoreReturn (c • A) (c • a) := by intro f;change c • A (embed f)=embed (c • a f);rw [ha,map_smul]
private theorem gradient_complex {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Q:E →L[ℂ] E) (n:ℕ) :
    PositiveContractionRitt.gradient Q n=(n+1:ℂ) • (Q^n*(1-Q)) := by
  unfold PositiveContractionRitt.gradient
  have hr:=RCLike.real_smul_eq_coe_smul (K:=ℂ) (n+1:ℝ) (Q^n*(1-Q))
  simpa only [RCLike.ofReal_add,RCLike.ofReal_natCast,RCLike.ofReal_one] using hr
private theorem boundary_core (j:ℕ) : CoreReturn (boundary j) ((j+1:ℂ) • (Q^j*S)) := by
  unfold boundary
  rw [gradient_complex]
  have hS:(1:Op)-phiComplement=phiInverseBounded:=by unfold phiComplement;abel
  rw [hS]
  exact core_smul (core_mul (phi_power_core j) phi_inverse_core) _
private theorem peak_core (m ell:ℕ) : CoreReturn (peak m ell) (B m ell*S) := by
  have h:=core_sub (boundary_core ell) (boundary_core m)
  simpa only [peak,B,SourceClockPhiRadiusResponseHessian.phiFirstPeak,sub_mul,smul_mul_assoc] using h

private theorem bracket_product (A B C:End):bracket A (B*C)=bracket A B*C+B*bracket A C := by
  unfold bracket;noncomm_ring
private theorem bracket_sub (A B C:End):bracket A (B-C)=bracket A B-bracket A C := by
  unfold bracket;noncomm_ring
private theorem euler_inverse : bracket E S=delta := by
  have hr : bracket E r=r-S := original_phi_euler_radius
  have h1 : S*E*r*S=S*E := by
    calc _=S*E*(r*S) := by noncomm_ring
         _=_ := by rw [radius_inverse,mul_one]
  have h2 : S*r*E*S=E*S := by rw [inverse_radius,one_mul]
  have hi : bracket E S= -(S*bracket E r*S) := by
    unfold bracket
    calc _= -(S*E*r*S-S*r*E*S) := by rw [h1,h2];abel
         _=_ := by noncomm_ring
  rw [hi,hr]
  change -(S*(r-S)*S)=S^3-S
  calc _= -((S*r)*S)+S^3 := by noncomm_ring
       _=_ := by rw [inverse_radius,one_mul];abel
private theorem q_delta : Commute Q delta :=
  (((Commute.one_left S).sub_left (Commute.refl S)).pow_right 3).sub_right
    ((Commute.one_left S).sub_left (Commute.refl S))
private theorem euler_q : bracket E Q= -delta := by
  rw [Q,bracket_sub,euler_inverse]
  simp only [bracket,mul_one,one_mul,sub_self,zero_sub]
private theorem euler_geometric_succ (n : ℕ) :
    bracket E (Q^(n+1))=(-(n+1:ℂ)) • (Q^n*delta) := by
  induction n with
  | zero => simpa only [zero_add,Nat.cast_zero,pow_one,pow_zero,one_mul,one_smul,neg_smul] using euler_q
  | succ n ih =>
    have hm : (Q^n*delta)*Q=Q^(n+1)*delta := by rw [mul_assoc,←q_delta.eq,←mul_assoc,←pow_succ]
    rw [show n+1+1=(n+1)+1 from rfl,pow_succ,bracket_product,ih,euler_q]
    simp only [smul_mul_assoc,mul_neg]
    rw [hm]
    push_cast
    simp only [pow_succ]
    module
private theorem euler_geometric (n : ℕ) : bracket E (Q^n)=(-(n:ℂ)) • (Q^(n-1)*delta) := by
  cases n with
  | zero => simp [bracket]
  | succ n => simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using euler_geometric_succ n
private theorem euler_theta (m ell : ℕ) : bracket E (T m ell)=B m ell*delta := by
  change bracket E (Q^(m+1)-Q^(ell+1))=B m ell*delta
  rw [bracket_sub,euler_geometric_succ,euler_geometric_succ]
  change _=((ell+1:ℂ) • Q^ell-(m+1:ℂ) • Q^m)*delta
  simp only [sub_mul,smul_mul_assoc]
  module


private theorem beta_commute {A:End} (h:Commute A S) (m ell:ℕ) : Commute A (B m ell) :=
  ((((Commute.one_right A).sub_right h).pow_right ell).smul_right _).sub_right
    ((((Commute.one_right A).sub_right h).pow_right m).smul_right _)
private theorem euler_U : Commute E U := sub_eq_zero.mp SourceScalarInverseBulk.inverse_phi
private theorem generator_normal (m ell:ℕ) : weightedGenerator m ell=
    (T m ell)^2*U*Phi+(B m ell*S)*(S^2-1)*T m ell*U := by
  have hS:Commute (T m ell) S:=(theta_commute (Commute.refl S) m ell).symm
  have hB:Commute (T m ell) (B m ell):=beta_commute hS m ell
  have hD:Commute (T m ell) delta:=(hS.pow_right 3).sub_right hS
  have hU:Commute U (T m ell):=theta_commute (real_commute _ _ _ _) m ell
  have hUS:Commute U S:=real_commute _ _ _ _
  have hUB:Commute U (B m ell):=beta_commute hUS m ell
  have hsq:bracket E ((T m ell)^2)=(2:ℂ) • (T m ell*B m ell*delta) := by
    rw [pow_two,bracket_product,euler_theta]
    have he:(B m ell*delta)*T m ell=T m ell*B m ell*delta := by
      rw [mul_assoc,←hD.eq,←mul_assoc,←hB.eq]
    rw [he]
    module
  have hg:=SourceScalarAffineScaleTransport.generator_commutator (M m ell)
  change bracket Phi (M m ell)=bracket E (M m ell) at hg
  have he:bracket E (M m ell)=U*bracket E ((T m ell)^2) := by
    unfold M bracket
    linear_combination (norm:=noncomm_ring) euler_U.eq*(T m ell)^2
  rw [he,hsq,mul_smul_comm] at hg
  have hn:weightedGenerator m ell=M m ell*Phi+U*T m ell*B m ell*delta := by
    unfold bracket at hg
    unfold weightedGenerator
    linear_combination (norm:=module) (1/2:ℂ) • hg
  have ht:Commute (T m ell) (B m ell*S*(S^2-1)) :=
    (hB.mul_right hS).mul_right ((hS.pow_right 2).sub_right (Commute.one_right _))
  have hu:Commute U (B m ell*S*(S^2-1)) :=
    (hUB.mul_right hUS).mul_right ((hUS.pow_right 2).sub_right (Commute.one_right _))
  have hfirst:M m ell*Phi=(T m ell)^2*U*Phi := by
    change U*(T m ell)^2*Phi=_
    rw [(hU.pow_right 2).eq]
  have hsecond:U*T m ell*B m ell*delta=(B m ell*S)*(S^2-1)*T m ell*U := by
    calc _=(U*T m ell)*(B m ell*S*(S^2-1)) := by unfold delta;noncomm_ring
         _=(B m ell*S*(S^2-1))*(U*T m ell) := (hu.mul_left ht).eq
         _=_ := by rw [hU.eq];simp only [mul_assoc]
  rw [hn,hfirst,hsecond]

private theorem inverse_square_core (f:QuantumTest) :
    ((phiInverseBounded^2-1:Op)) (embed f)=embed ((S^2-1:End) f) := by
  change phiInverseBounded (phiInverseBounded (embed f))-embed f=_
  rw [phi_inverse_core,phi_inverse_core,←map_sub]
  rfl
private theorem generator_fixed_read (m ell:ℕ) (f:QuantumTest) :
    embed (weightedGenerator m ell f)=
      phiTail m ell (phiTail m ell (embed (U (Phi f))))+
      peak m ell (((phiInverseBounded^2-1:Op)) (phiTail m ell (embed (U f)))) := by
  rw [generator_normal]
  change embed (T m ell (T m ell (U (Phi f))))+
    embed ((B m ell*S) ((S^2-1:End) (T m ell (U f))))=_
  rw [phi_tail_core,phi_tail_core,phi_tail_core,inverse_square_core,peak_core]

private theorem inverse_square_difference_norm : ‖phiInverseBounded^2-1‖   ≤   2 := by
  have h:‖phiInverseBounded^2‖   ≤   1 := by
    rw [pow_two]
    exact (norm_mul_le _ _).trans ((mul_le_mul phi_inverse_norm phi_inverse_norm (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have h1:‖(1:Op)‖   ≤   1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖x‖   ≤   1*‖x‖
    rw [one_mul]
  exact (norm_sub_le _ _).trans ((add_le_add h h1).trans_eq (by norm_num))
private theorem generator_fixed_bound (m ell:ℕ) (f:QuantumTest) :
    ‖embed (weightedGenerator m ell f)‖   ≤   2*‖embed (T m ell (U (Phi f)))‖+
      4*‖embed (T m ell (U f))‖ := by
  rw [generator_fixed_read,←phi_tail_core,←phi_tail_core]
  have h1:=((phiTail m ell).le_opNorm (phiTail m ell (embed (U (Phi f))))).trans
    (mul_le_mul_of_nonneg_right (theta_norm m ell) (norm_nonneg _))
  have h2:=((peak m ell).le_opNorm (((phiInverseBounded^2-1:Op)) (phiTail m ell (embed (U f))))).trans
    (mul_le_mul_of_nonneg_right (peak_norm m ell) (norm_nonneg _))
  have h3:=((phiInverseBounded^2-1).le_opNorm (phiTail m ell (embed (U f)))).trans
    (mul_le_mul_of_nonneg_right inverse_square_difference_norm (norm_nonneg _))
  have h4:=norm_add_le (phiTail m ell (phiTail m ell (embed (U (Phi f)))))
    (peak m ell (((phiInverseBounded^2-1:Op)) (phiTail m ell (embed (U f)))))
  linarith only [h1,h2,h3,h4]
private theorem fixed_theta_tail (f:QuantumTest) :
    ∀ ε : ℝ, 0 < ε → ∃N:ℕ,∀m,N   ≤   m → ∀ell,m   ≤   ell → ‖embed (T m ell f)‖<ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=SourceRelativePowerTail.decreasing_distance_tail
    (fun k:ℕ=>(phiComplement^k) (embed f))
    (fun m ell h=>SourceRelativePowerTail.positive_power_distance phiComplement phi_complement_positive
      phi_complement_le_one (embed f) h) ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  rw [←phi_tail_core]
  exact hN m hm ell hml
private theorem generator_fixed_tail (f:QuantumTest) :
    ∀ ε : ℝ, 0 < ε → ∃N:ℕ,∀m,N   ≤   m → ∀ell,m   ≤   ell → ‖embed (weightedGenerator m ell f)‖   ≤   ε := by
  intro ε hε
  obtain ⟨N1,h1⟩:=fixed_theta_tail (U (Phi f)) (ε/6) (by positivity)
  obtain ⟨N2,h2⟩:=fixed_theta_tail (U f) (ε/6) (by positivity)
  refine ⟨max N1 N2,fun m hm ell hml=>?_⟩
  have ha:=h1 m (by omega) ell hml
  have hb:=h2 m (by omega) ell hml
  have hc:=generator_fixed_bound m ell f
  linarith only [ha,hb,hc]

private theorem complex_two_step (z x y a b c:ℂ)
    (h0:(starRingEnd ℂ z)*x=y-a) (h1:(starRingEnd ℂ z)*y=c-b) (ha:a.re=0) :
    ‖z‖^2*|x.re|  ≤  ‖c‖+‖b‖+|z.im| *‖a‖ := by
  have hz:z*(starRingEnd ℂ z)=((‖z‖^2:ℝ):ℂ) := by
    simp only [Complex.mul_conj,Complex.normSq_eq_norm_sq]
  have hreal:‖z‖^2*x.re=(z*y).re+z.im*a.im := by
    have h:=congrArg (fun d:ℂ=>(z*d).re) h0
    rw [←mul_assoc,hz] at h
    simp only [mul_sub,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,ha,mul_zero] at h
    simp only [Complex.mul_re]
    linarith only [h]
  have hn:‖z‖*‖y‖  ≤  ‖c‖+‖b‖ := by
    have he:=congrArg (fun d:ℂ=>‖d‖) h1
    simp only [norm_mul] at he
    change ‖star z‖*‖y‖=‖c-b‖ at he
    rw [norm_star] at he
    exact he.trans_le (norm_sub_le _ _)
  calc
    _=|‖z‖^2*x.re| := by rw [abs_mul,abs_of_nonneg (sq_nonneg ‖z‖)]
    _  ≤  |(z*y).re|+|z.im| *|a.im| := by rw [hreal];simpa only [abs_mul] using abs_add_le (z*y).re (z.im*a.im)
    _  ≤  ‖z‖*‖y‖+|z.im| *‖a‖ := add_le_add
      ((Complex.abs_re_le_norm _).trans_eq (norm_mul z y))
      (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm a) (abs_nonneg _))
    _  ≤  _ := add_le_add hn le_rfl
private theorem norm_pair (f g:QuantumTest):‖sourcePair f g‖  ≤  ‖embed f‖*‖embed g‖ := norm_inner_le_norm _ _
private theorem source_pair_re_zero (m ell:ℕ) (f:QuantumTest) :
    (sourcePair f (weightedGenerator m ell f)).re=0 := by
  have h:=congrArg Complex.re (generator_pair m ell f f)
  have hc:=congrArg Complex.re (pair_conjugate f (weightedGenerator m ell f))
  simp only [Complex.neg_re,Complex.conj_re] at h hc
  linarith only [h,hc]
private theorem source_state (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    resolventCore F z hz (coreEquiv.symm g)=SourceScalarPositiveBulkWard.state F z hz g := by
  simp only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply]
private theorem state_embed (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    embed (SourceScalarPositiveBulkWard.state F z hz g)=finiteResolvent F z (g:H) := by
  unfold SourceScalarPositiveBulkWard.state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem embed_core (g:diagonal.domain):embed (coreEquiv.symm g)=(g:H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)
private theorem state_norm (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    ‖embed (SourceScalarPositiveBulkWard.state F z hz g)‖  ≤  |z.im|⁻¹*‖(g:H)‖ := by
  rw [state_embed]
  have hr:‖finiteResolvent F z‖  ≤  |z.im|⁻¹ := by
    simpa only [finiteResolvent,one_div] using
      (resolvent_norm (GaussGradedCompression.compression F)
        (GaussGradedCompression.compression_selfAdjoint F) z hz)
  exact ((finiteResolvent F z).le_opNorm (g:H)).trans
    (mul_le_mul_of_nonneg_right hr (norm_nonneg _))

private def fixedCoefficient (μ:ℝ) (g:diagonal.domain):ℝ :=
  2*(μ*‖(g:H)‖+‖(GaussAdjointHistory.coreStep g:H)‖+
    μ⁻¹*‖(GaussAdjointHistory.coreStep (GaussAdjointHistory.coreStep g):H)‖)
private def fixedTerm (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain):ℝ :=
  -2*(sourcePair (weightedGenerator m ell (resolventCore F z hz (coreEquiv.symm g))) (coreEquiv.symm g)).re
private theorem fixed_point_source (g:diagonal.domain) :
    ∀ᶠ F in (sourceFilter:Filter Index),∀m ell:ℕ,∀z:ℂ,∀hz:z.im≠0,
      |fixedTerm m ell F z hz g|  ≤  fixedCoefficient |z.im| g*
        ‖embed (weightedGenerator m ell (coreEquiv.symm g))‖/(‖z‖^2) := by
  filter_upwards [SourceInverseJetEnergy.actual_source_step g,
    SourceInverseJetEnergy.actual_source_step (GaussAdjointHistory.coreStep g)] with F h0 h1
  intro m ell z hz
  let k:=weightedGenerator m ell (coreEquiv.symm g)
  let q0:=SourceScalarPositiveBulkWard.state F z hz g
  let q1:=SourceScalarPositiveBulkWard.state F z hz (GaussAdjointHistory.coreStep g)
  let q2:=SourceScalarPositiveBulkWard.state F z hz (GaussAdjointHistory.coreStep (GaussAdjointHistory.coreStep g))
  have hs0:=congrArg (fun f:QuantumTest=>sourcePair f k) (h0 z hz)
  have hs1:=congrArg (fun f:QuantumTest=>sourcePair f k) (h1 z hz)
  simp only [pair_smul_l,pair_sub_l] at hs0 hs1
  have hb:=complex_two_step z (sourcePair q0 k) (sourcePair q1 k)
    (sourcePair (coreEquiv.symm g) k) (sourcePair (coreEquiv.symm (GaussAdjointHistory.coreStep g)) k)
    (sourcePair q2 k) hs0 hs1 (source_pair_re_zero m ell (coreEquiv.symm g))
  have hR:=state_norm F z hz (GaussAdjointHistory.coreStep (GaussAdjointHistory.coreStep g))
  have h2:=norm_pair q2 k
  have h1p:=norm_pair (coreEquiv.symm (GaussAdjointHistory.coreStep g)) k
  have h0p:=norm_pair (coreEquiv.symm g) k
  rw [embed_core] at h1p h0p
  have hR':‖sourcePair q2 k‖  ≤  (|z.im|⁻¹*‖(GaussAdjointHistory.coreStep (GaussAdjointHistory.coreStep g):H)‖)*‖embed k‖ :=
    h2.trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  have h0':|z.im| *‖sourcePair (coreEquiv.symm g) k‖  ≤  |z.im| *(‖(g:H)‖*‖embed k‖) :=
    mul_le_mul_of_nonneg_left h0p (abs_nonneg _)
  have hn:0<‖z‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (by intro h;exact hz (by rw [h];rfl)))
  have he:|fixedTerm m ell F z hz g|=2*|(sourcePair q0 k).re| := by
    have hp:=congrArg Complex.re (generator_pair m ell
      (resolventCore F z hz (coreEquiv.symm g)) (coreEquiv.symm g))
    rw [source_state] at hp
    change (sourcePair q0 k).re= -(sourcePair (weightedGenerator m ell q0) (coreEquiv.symm g)).re at hp
    unfold fixedTerm
    rw [source_state]
    change |-2*(sourcePair (weightedGenerator m ell q0) (coreEquiv.symm g)).re|=_
    have hinner:(sourcePair (weightedGenerator m ell q0) (coreEquiv.symm g)).re= -(sourcePair q0 k).re := by linarith only [hp]
    rw [hinner,abs_mul,abs_neg]
    norm_num

  rw [he]
  apply (le_div_iff₀ hn).mpr
  dsimp only [fixedCoefficient,k]
  change _  ≤  2*(|z.im| *‖(g:H)‖+‖(GaussAdjointHistory.coreStep g:H)‖+
    |z.im|⁻¹*‖(GaussAdjointHistory.coreStep (GaussAdjointHistory.coreStep g):H)‖)*‖embed k‖
  nlinarith only [hb,hR',h1p,h0']

private theorem frequency_nonreal (advanced:Bool) (μ:ℝ) (hμ:0<μ) (t:ℝ) :
    (actualFrequency advanced μ t).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
private theorem frequency_abs (advanced:Bool) (μ:ℝ) (hμ:0<μ) (t:ℝ) :
    |(actualFrequency advanced μ t).im|=μ := by
  cases advanced <;> simp only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,abs_neg,abs_of_pos hμ]
private theorem frequency_kernel (advanced:Bool) (μ t:ℝ) :
    (‖actualFrequency advanced μ t‖^2)⁻¹=SourceResolventLorentzian.kernel μ 0 t := by
  have hb:(‖line μ t‖^2)⁻¹=SourceResolventLorentzian.kernel μ 0 t := by
    simpa only [Complex.ofReal_zero,zero_sub,norm_inv,norm_neg,inv_pow,line,mul_comm Complex.I (μ:ℂ)]
      using SourceResolventLorentzian.inverse_norm_square μ 0 t
  cases advanced
  · exact hb
  · change (‖star (line μ t)‖^2)⁻¹=_
    rw [norm_star]
    exact hb
private theorem kernel_integral (μ:ℝ) (hμ:0<μ) :
    (∫⁻t:ℝ,ENNReal.ofReal (SourceResolventLorentzian.kernel μ 0 t))=ENNReal.ofReal (Real.pi/μ) := by
  rw [←ofReal_integral_eq_lintegral_ofReal (SourceResolventLorentzian.kernel_integrable μ 0 hμ)
    (Eventually.of_forall (fun t=>by unfold SourceResolventLorentzian.kernel;positivity)),
    SourceResolventLorentzian.kernel_integral μ 0 hμ]
private theorem fixed_common_tail (μ:ℝ) (hμ:0<μ) (g:diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻t:ℝ,ENNReal.ofReal (|fixedTerm m ell F (actualFrequency advanced μ t)
        (frequency_nonreal advanced μ hμ t) g|)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let c:=fixedCoefficient μ g
  have hc:0 ≤ c := by dsimp only [c,fixedCoefficient];positivity
  let L:=c*(Real.pi/μ)
  have hL:0 ≤ L:=mul_nonneg hc (by positivity)
  obtain ⟨N,hN⟩:=generator_fixed_tail (coreEquiv.symm g) (ε/(L+1)) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [fixed_point_source g] with F hF
  intro advanced
  let a:=‖embed (weightedGenerator m ell (coreEquiv.symm g))‖
  have ha:a ≤ ε/(L+1):=hN m hm ell hml
  have hb:L*a ≤ ε := by
    have h:=mul_le_mul_of_nonneg_left ha hL
    have hdiv:L*(ε/(L+1)) ≤ ε := by
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0<L+1)).mpr
      nlinarith only [hε]
    exact h.trans hdiv
  calc
    _ ≤ ∫⁻t:ℝ,ENNReal.ofReal (c*a)*ENNReal.ofReal (SourceResolventLorentzian.kernel μ 0 t) := by
      apply lintegral_mono
      intro t
      dsimp only
      have ha0:0 ≤ a:=norm_nonneg _
      rw [←ENNReal.ofReal_mul (mul_nonneg hc ha0)]
      apply ENNReal.ofReal_le_ofReal
      simpa only [frequency_abs advanced μ hμ t,div_eq_mul_inv,frequency_kernel] using
        hF m ell (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t)
    _=ENNReal.ofReal (c*a)*ENNReal.ofReal (Real.pi/μ) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,kernel_integral μ hμ]
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul (mul_nonneg hc (norm_nonneg _))]
      apply ENNReal.ofReal_le_ofReal
      convert hb using 1
      dsimp only [L]
      ring
private theorem finite_star (F:Index) (z:ℂ):finiteResolvent F (star z)=(finiteResolvent F z).adjoint := by
  unfold finiteResolvent
  change Ring.inverse (GaussGradedCompression.compression F-star z • 1)=
    (Ring.inverse (GaussGradedCompression.compression F-z • 1)).adjoint
  rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
  congr 1
  simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]
private theorem frequency_continuous (advanced:Bool) (μ:ℝ) (hμ:0<μ) (F:Index):
    Continuous (fun t:ℝ=>finiteResolvent F (actualFrequency advanced μ t)) := by
  cases advanced
  · exact SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  · have h:(fun t:ℝ=>finiteResolvent F (actualFrequency true μ t))=
        fun t:ℝ=>(finiteResolvent F (line μ t)).adjoint := funext (fun t=>finite_star F (line μ t))
    exact h ▸ ContinuousLinearMap.adjoint.continuous.comp (SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F)
private theorem fixed_measurable (m ell:ℕ) (F:Index) (μ:ℝ) (hμ:0<μ) (advanced:Bool) (g:diagonal.domain):
    Measurable (fun t:ℝ=>ENNReal.ofReal |fixedTerm m ell F (actualFrequency advanced μ t)
      (frequency_nonreal advanced μ hμ t) g|) := by
  have hr (z:ℂ) (hz:z.im≠0):fixedTerm m ell F z hz g=
      2*(inner ℂ (finiteResolvent F z (g:H)) (embed (weightedGenerator m ell (coreEquiv.symm g)))).re := by
    have h:=congrArg Complex.re (generator_pair m ell
      (resolventCore F z hz (coreEquiv.symm g)) (coreEquiv.symm g))
    rw [source_state] at h
    simp only [sourcePair,state_embed,Complex.neg_re] at h
    unfold fixedTerm
    rw [source_state]
    change -2*(inner ℂ (embed (weightedGenerator m ell (SourceScalarPositiveBulkWard.state F z hz g)))
      (embed (coreEquiv.symm g))).re=_
    rw [h]
    ring
  simp_rw [hr]
  have hi:Continuous (fun t:ℝ=>inner ℂ (finiteResolvent F (actualFrequency advanced μ t) (g:H))
      (embed (weightedGenerator m ell (coreEquiv.symm g)))) :=
    ((frequency_continuous advanced μ hμ F).clm_apply continuous_const).inner continuous_const
  exact ((continuous_const.mul (Complex.continuous_re.comp hi)).abs).measurable.ennreal_ofReal

private theorem weighted_phi_bound (m ell:ℕ) (hml:m ≤ ell) (f:QuantumTest):
    ‖embed (W m ell (Phi f))‖ ≤ 3*‖embed (W m ell (E f))‖ := by
  have hh:=SourceClockPhiNativeWeightedHardy.original_phi_weighted_hardy m ell hml f
  change (57/2:ℝ)*‖embed (W m ell f)‖ ≤ ‖embed (W m ell (E f))‖ at hh
  have he:W m ell (Phi f)=W m ell (E f)+(61/2:ℂ) • W m ell f := by
    simp only [Phi,SourceScalarAffineScaleTransport.generator,LinearMap.add_apply,
      LinearMap.smul_apply,Module.End.one_apply,map_add,map_smul]
  rw [he,map_add]
  have hb:=norm_add_le (embed (W m ell (E f))) (embed ((61/2:ℂ) • W m ell f))
  simp only [map_smul,norm_smul,norm_div,Complex.norm_ofNat] at hb
  simp only [map_smul]
  nlinarith only [hb,hh,norm_nonneg (embed (W m ell (E f)))]
private theorem radius_state (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain):
    resolventCore F z hz (r (coreEquiv.symm g))=SourceScalarPositiveBulkWard.state F z hz (phiRadiusSource g) := by
  have h:r (coreEquiv.symm g)=coreEquiv.symm (phiRadiusSource g) := by unfold phiRadiusSource;rw [coreEquiv.symm_apply_apply]
  rw [h,source_state]
private theorem current_point (m ell:ℕ) (hml:m ≤ ell) (F:Index) (z:ℂ) (hz:z.im≠0)
    (g:diagonal.domain) (η:ℝ) (hη:0<η):
    |signedCurrent m ell F z hz g|-η*‖embed (W m ell (E (resolventCore F z hz (coreEquiv.symm g))))‖^2 ≤
      |fixedTerm m ell F z hz g|+(9*z.im^2/η)*
        ‖embed (T m ell (SourceScalarPositiveBulkWard.state F z hz (phiRadiusSource g)))‖^2 := by
  let q:=resolventCore F z hz (coreEquiv.symm g)
  let h:=T m ell (resolventCore F z hz (r (coreEquiv.symm g)))
  have hpair:|(sourcePair (W m ell (Phi q)) h).im| ≤ 3*‖embed (W m ell (E q))‖*‖embed h‖ :=
    ((Complex.abs_im_le_norm _).trans (norm_pair _ _)).trans
      (mul_le_mul_of_nonneg_right (weighted_phi_bound m ell hml q) (norm_nonneg _))
  have hy:2*|z.im| *(3*‖embed (W m ell (E q))‖*‖embed h‖) ≤
      η*‖embed (W m ell (E q))‖^2+(9*z.im^2/η)*‖embed h‖^2 := by
    have hs:=sq_nonneg (η*‖embed (W m ell (E q))‖-3*|z.im| *‖embed h‖)
    apply (mul_le_mul_iff_of_pos_left hη).mp
    field_simp [hη.ne']
    nlinarith only [hs,sq_abs z.im]
  rw [signed_current_return]
  change |fixedTerm m ell F z hz g+2*z.im*(sourcePair (W m ell (Phi q)) h).im|-_ ≤ _
  have hsum:=abs_add_le (fixedTerm m ell F z hz g) (2*z.im*(sourcePair (W m ell (Phi q)) h).im)
  rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hsum
  have hh:=mul_le_mul_of_nonneg_left hpair (show 0 ≤ 2*|z.im| by positivity)
  have hr:‖embed h‖^2=‖embed (T m ell (SourceScalarPositiveBulkWard.state F z hz (phiRadiusSource g)))‖^2 := by
    dsimp only [h];rw [radius_state]
  rw [←hr]
  linarith only [hsum,hh,hy]

/-- The complete source-field/full-defect current, less the actual response flux, is paid by a freely small radial first-jet price and genuine fixed-source tails. -/
theorem actual_weighted_phi_current_common_payment (μ:ℝ) (hμ:0<μ) (g:diagonal.domain) (η:ℝ) (hη:0<η):
    ∀ ε : ℝ, 0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻t:ℝ,ENNReal.ofReal (|signedCurrent m ell F (actualFrequency advanced μ t)
        (frequency_nonreal advanced μ hμ t) g|-η*‖embed (W m ell (E (resolventCore F
          (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) (coreEquiv.symm g))))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let c:ℝ:=9*μ^2/η
  have hc:0<c:=by dsimp only [c];positivity
  obtain ⟨N0,h0⟩:=fixed_common_tail μ hμ g (ε/2) (by positivity)
  obtain ⟨N1,h1⟩:=SourceClockPhiRadiusResponseNativeBudget.actual_phi_theta_common_tail μ hμ
    (phiRadiusSource g) (ε/(2*c)) (by positivity)
  refine ⟨max N0 N1,fun m hm ell hml=>?_⟩
  filter_upwards [h0 m (by omega) ell hml,h1 m (by omega) ell hml] with F hF hT
  intro advanced
  let f:ℝ→ENNReal:=fun t=>ENNReal.ofReal |fixedTerm m ell F (actualFrequency advanced μ t)
    (frequency_nonreal advanced μ hμ t) g|
  let e:ℝ→ENNReal:=fun t=>ENNReal.ofReal (‖embed (T m ell (SourceScalarPositiveBulkWard.state F
    (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) (phiRadiusSource g)))‖^2)
  have mf:Measurable f:=fixed_measurable m ell F μ hμ advanced g
  have hp(t:ℝ):ENNReal.ofReal (|signedCurrent m ell F (actualFrequency advanced μ t)
      (frequency_nonreal advanced μ hμ t) g|-η*‖embed (W m ell (E (resolventCore F
        (actualFrequency advanced μ t) (frequency_nonreal advanced μ hμ t) (coreEquiv.symm g))))‖^2) ≤
      f t+ENNReal.ofReal c*e t := by
    dsimp only [f,e]
    rw [←ENNReal.ofReal_mul hc.le,←ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg hc.le (sq_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    have hs:(actualFrequency advanced μ t).im^2=μ^2 := by
      cases advanced <;> simp only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
        Complex.star_def,Complex.conj_im,line_im,neg_sq]
    simpa only [hs] using current_point m ell hml F (actualFrequency advanced μ t)
      (frequency_nonreal advanced μ hμ t) g η hη
  calc
    _ ≤ ∫⁻t:ℝ,(f t+ENNReal.ofReal c*e t) := lintegral_mono hp
    _=(∫⁻t:ℝ,f t)+ENNReal.ofReal c*(∫⁻t:ℝ,e t) := by
      rw [lintegral_add_left mf,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal c*ENNReal.ofReal (ε/(2*c)) :=
      add_le_add (hF advanced) (mul_le_mul_of_nonneg_left (hT advanced) (by exact bot_le))
    _=ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hc.le,←ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      field_simp [hc.ne']
      norm_num

end LowEnergy.SourceClockPhiNativeSignedCurrent
