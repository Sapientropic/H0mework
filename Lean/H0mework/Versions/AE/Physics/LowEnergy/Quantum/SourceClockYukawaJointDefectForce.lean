import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaJointRadialZero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaJointDefectForce
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussQuantumMultiplier
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceClockYukawaSpinJointForce SourceClockYukawaSpinNativeBudget SourceClockYukawaJointRadialZero
open SourceClockYukawaRadialCoefficient SourceClockYukawaCubicCurrent SourceInverseNeutralSpinCurrent
open SourceClockYukawaSpinClosure FullYSourceResolventGraphSplice SourceResolventBandLimit
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] fullAction resolventCore compressionCore defectAction diagonalAction
  finiteResolvent SourceClockYukawaSpinJointForce.currentCore SourceClockYukawaSpinJointForce.cutoffCore

private theorem inverse_spin (j : Fin 4) : Commute inverseAction (activeSpin j) := by
  unfold activeSpin
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (reciprocal z:ℂ) • quantized (GaussCoframeSpin.full (activeIndex j)) (f z)=
    quantized (GaussCoframeSpin.full (activeIndex j)) ((reciprocal z:ℂ) • f z)
  exact (map_smul _ _ _).symm

private theorem inverse_coefficient (sharp : Bool) (mu : Fin 8) :
    Commute inverseAction (spinClosureCoefficient sharp mu) := by
  have hY : Commute inverseAction (fullAction sharp) := by
    unfold fullAction
    cases sharp
    · exact GaussRadialHamiltonian.original_commutes.symm
    · exact GaussRadialHamiltonian.adjoint_commutes.symm
  have hb (A B : End) (hA : Commute inverseAction A) (hB : Commute inverseAction B) :
      Commute inverseAction (bracket A B) := (hA.mul_right hB).sub_right (hB.mul_right hA)
  unfold spinClosureCoefficient SourceClockYukawaSpinRelativeForm.spinCoefficient
  split
  · exact hY
  · split
    · exact hb _ _ (inverse_spin _) hY
    · exact hb _ _ (inverse_spin _) (hb _ _ (inverse_spin 3) hY)

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_embed (F : Index) (q : QuantumTest) :
    embed (compressionCore F q)=GaussGradedCompression.compression F (embed q) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore
  exact state_embed F z hz (coreEquiv f)

private theorem core_inverses (F : Index) (z : ℂ) (hz : z.im≠0) :
    (compressionCore F-z • (1:End))*resolventCore F z hz=1 ∧
      resolventCore F z hz*(compressionCore F-z • (1:End))=1 := by
  constructor
  · apply LinearMap.ext
    intro f
    apply embed_injective
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
      map_sub,map_smul,compression_embed,resolvent_embed]
    have h := congrArg (fun A : H →L[ℂ] H => A (embed f))
      (resolvent_right (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
    simpa only [finiteResolvent,mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self] using h
  · apply LinearMap.ext
    intro f
    apply embed_injective
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
      resolvent_embed,map_sub,map_smul,compression_embed]
    have h := congrArg (fun A : H →L[ℂ] H => A (embed f))
      (resolvent_left (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
    simpa only [finiteResolvent,mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self,map_sub,map_smul] using h

private theorem response_difference (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    cutoffResponseCore sharp mu m ell F z hz g=
      spinClosureCoefficient sharp mu (SourceMixedNativeReturn.thetaAction m ell (resolventCore F z hz (coreEquiv.symm g)))-
        resolventCore F z hz (SourceMixedNativeReturn.thetaAction m ell (spinClosureCoefficient sharp mu (coreEquiv.symm g))) := by
  let L : End := compressionCore F-z • 1
  let R : End := resolventCore F z hz
  let A : End := SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu
  have hi := core_inverses F z hz
  have hm (L R A : End) (hL : L*R=1) (hR : R*L=1) : R*bracket L A*R=A*R-R*A := by
    unfold bracket
    rw [mul_sub,sub_mul,←mul_assoc,←mul_assoc,hR,one_mul,mul_assoc,mul_assoc,hL,mul_one]
  have hJ : bracket L A=SourceClockYukawaSpinJointForce.currentCore sharp m ell F mu := by
    unfold SourceClockYukawaSpinJointForce.currentCore defectAction
    dsimp only [L,A]
    simp only [bracket,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
    module
  have h := LinearMap.congr_fun (hm L R A hi.1 hi.2) (coreEquiv.symm g)
  rw [hJ] at h
  have ht : Commute (SourceMixedNativeReturn.thetaAction m ell) (spinClosureCoefficient sharp mu) := by
    exact ((((Commute.one_left _).sub_left (inverse_coefficient sharp mu)).pow_left _).sub_left
      (((Commute.one_left _).sub_left (inverse_coefficient sharp mu)).pow_left _))
  have ht' := LinearMap.congr_fun ht.eq (coreEquiv.symm g)
  simp only [Module.End.mul_apply] at ht'
  simpa only [cutoffResponseCore,Module.End.mul_apply,LinearMap.sub_apply,A,SourceClockYukawaSpinJointForce.cutoffCore,ht',R]
    using h

private theorem radial_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (radialCore F z hz g)=SourceRadiusResponseDecay.response F z (g:H) := by
  rw [radialCore,state_embed]
  change finiteResolvent F z (embed (SourceRadiusResponseDecay.radialCurrent F (SourceScalarPositiveBulkWard.state F z hz g)))=_
  rw [SourceRadiusResponseDecay.original_radial_current]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,compression_embed,←GaussRadialDomain.inverse_core,state_embed]
  simp only [SourceRadiusResponseDecay.response,mul_apply_eq_comp,sub_apply,map_sub]

private theorem radial_map_return (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    radialMap F z hz (inputCore g)=radialCore F z hz (SourceClockYukawaRadialMixedBudget.radiusSource g) := by
  have hg : embed (inputCore g)=(SourceClockYukawaRadialMixedBudget.radiusSource g:H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  apply embed_injective
  rw [radial_embed,SourceRadiusResponseDecay.actual_response_difference F z hz]
  simp only [radialMap,Module.End.mul_apply,LinearMap.sub_apply,map_sub,←GaussRadialDomain.inverse_core,resolvent_embed,hg]

/-- The whole compression defect enters through this one actual radial response operator. -/
def defectRadialMap (F : Index) (z : ℂ) (hz : z.im≠0) : End :=
  inverseAction*defectAction F*resolventCore F z hz-defectAction F*resolventCore F z hz*inverseAction

def defectWord (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : Column := fun mu =>
  let h := SourceClockYukawaRadialMixedBudget.radiusSource g
  let rS := radialCore F z hz h
  let rA := cutoffResponseCore sharp mu m ell F z hz h
  let q := state F z hz h;
  -(bracket (defectAction F) (cutoffCore sharp m ell mu) rS)-
    bracket (defectAction F) inverseAction rA+
    bracket (bracket (defectAction F) inverseAction) (cutoffCore sharp m ell mu) q

def coherentDefectWord (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : Column := fun mu =>
  bracket (cutoffCore sharp m ell mu) (defectRadialMap F z hz) (inputCore g)

private theorem defect_kernel (D S A R : End) :
    -(bracket D A*(S*R-R*S))-bracket D S*(A*R-R*A)+bracket (bracket D S) A*R+
      D*bracket A (S*R-R*S)=bracket A (S*D*R-D*R*S) := by
  unfold bracket
  noncomm_ring

private theorem theta_coefficient (sharp : Bool) (mu : Fin 8) (m ell : ℕ) :
    Commute (thetaAction m ell) (spinClosureCoefficient sharp mu) :=
  (((Commute.one_left _).sub_left (inverse_coefficient sharp mu)).pow_left _).sub_left
    (((Commute.one_left _).sub_left (inverse_coefficient sharp mu)).pow_left _)

private theorem joint_commutator (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (mu : Fin 8) :
    jointState sharp m ell F z hz g mu=
      bracket (cutoffCore sharp m ell mu) (radialMap F z hz) (inputCore g) := by
  have ht := LinearMap.congr_fun (theta_coefficient sharp mu m ell).eq (inputCore g)
  change thetaAction m ell (spinClosureCoefficient sharp mu (inputCore g))=
    spinClosureCoefficient sharp mu (thetaAction m ell (inputCore g)) at ht
  simp only [jointState,coherentColumn,windowState,errorColumn,bracket,LinearMap.sub_apply,Module.End.mul_apply,
    SourceClockYukawaSpinJointForce.cutoffCore,ht]

/-- All three original defects collapse into the same coherent commutator plus the actual selfadjoint diagonal defect. -/
theorem actual_joint_defect_source (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (mu : Fin 8) :
    defectWord sharp m ell F z hz g mu+defectAction F (jointState sharp m ell F z hz g mu)=
      coherentDefectWord sharp m ell F z hz g mu := by
  let h := SourceClockYukawaRadialMixedBudget.radiusSource g
  let A : End := cutoffCore sharp m ell mu
  let R : End := resolventCore F z hz
  have hS : radialCore F z hz h=radialMap F z hz (inputCore g) := (radial_map_return F z hz g).symm
  have hA : cutoffResponseCore sharp mu m ell F z hz h=bracket A R (inputCore g) := by
    rw [response_difference]
    have ht := LinearMap.congr_fun (theta_coefficient sharp mu m ell).eq (inputCore g)
    change thetaAction m ell (spinClosureCoefficient sharp mu (inputCore g))=
      spinClosureCoefficient sharp mu (thetaAction m ell (inputCore g)) at ht
    change spinClosureCoefficient sharp mu (thetaAction m ell (R (inputCore g)))-
      R (thetaAction m ell (spinClosureCoefficient sharp mu (inputCore g)))=_
    rw [ht]
    simp only [A,SourceClockYukawaSpinJointForce.cutoffCore,bracket,LinearMap.sub_apply,Module.End.mul_apply]
  have hq : state F z hz h=R (inputCore g) := by
    have hg : embed (inputCore g)=(h:H) := congrArg Subtype.val (coreEquiv.apply_symm_apply h)
    apply embed_injective
    exact (state_embed F z hz h).trans ((congrArg (finiteResolvent F z) hg.symm).trans
      (resolvent_embed F z hz (inputCore g)).symm)
  have he := LinearMap.congr_fun (defect_kernel (defectAction F) inverseAction A R) (inputCore g)
  unfold defectWord coherentDefectWord
  dsimp only
  rw [hS,hA,hq,joint_commutator]
  simpa only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,Module.End.mul_apply,
    radialMap,defectRadialMap,A,R,bracket] using he

private theorem defect_pair (F : Index) (p q : QuantumTest) :
    sourcePair p (defectAction F q)=sourcePair (defectAction F p) q := by
  have hc : sourcePair p (compressionCore F q)=sourcePair (compressionCore F p) q := by
    simp only [sourcePair,compression_embed]
    exact (GaussGradedCompression.compression_pair F _ _).symm
  unfold defectAction
  simp only [LinearMap.sub_apply,sourcePair,map_sub,inner_sub_right,inner_sub_left] at *
  exact congrArg₂ (·-·) (diagonalAction_pair p q) hc

private theorem defect_imaginary_zero (F : Index) (q : QuantumTest) :
    (sourcePair q (defectAction F q)).im=0 := by
  have h := congrArg Complex.im (pair_conjugate q (defectAction F q))
  rw [←defect_pair] at h
  simp only [Complex.conj_im] at h
  linarith only [h]

/-- The selfadjoint defect cancels inside the actual joint imaginary word, before any norm estimate. -/
theorem actual_joint_defect_pair_source (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    (∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu) (defectWord sharp m ell F z hz g mu)).im=
      (∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu) (coherentDefectWord sharp m ell F z hz g mu)).im := by
  have h (mu : Fin 8) := congrArg (fun f => (sourcePair (jointState sharp m ell F z hz g mu) f).im)
    (actual_joint_defect_source sharp m ell F z hz g mu)
  simp only [sourcePair,map_add,inner_add_right,Complex.add_im] at h
  change ∀ mu,(sourcePair (jointState sharp m ell F z hz g mu) (defectWord sharp m ell F z hz g mu)).im+
    (sourcePair (jointState sharp m ell F z hz g mu) (defectAction F (jointState sharp m ell F z hz g mu))).im=
      (sourcePair (jointState sharp m ell F z hz g mu) (coherentDefectWord sharp m ell F z hz g mu)).im at h
  simp only [defect_imaginary_zero,add_zero] at h
  simp only [Complex.im_sum]
  exact Finset.sum_congr rfl (fun mu _ => h mu)

/-- The original signed field word consumes the cancellation without separating gamma, matter or the retained defect response. -/
theorem actual_joint_field_defect_source (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    (∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu) (fieldRemainingWord sharp m ell F z hz g mu)).im=
      (∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
        (gammaWord sharp m ell F z hz g mu+SourceClockYukawaJointCoframeForce.matterWord sharp m ell F z hz g mu+
          coherentDefectWord sharp m ell F z hz g mu)).im := by
  have hf (mu : Fin 8) : fieldRemainingWord sharp m ell F z hz g mu=
      gammaWord sharp m ell F z hz g mu+SourceClockYukawaJointCoframeForce.matterWord sharp m ell F z hz g mu+
        defectWord sharp m ell F z hz g mu := by
    unfold fieldRemainingWord defectWord
    dsimp only
    abel
  simp only [hf,sourcePair,map_add,inner_add_right,Finset.sum_add_distrib,Complex.add_im]
  have h := actual_joint_defect_pair_source sharp m ell F z hz g
  simp only [sourcePair] at h
  rw [h]

end LowEnergy.SourceClockYukawaJointDefectForce
