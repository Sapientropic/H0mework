import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNumberRange

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalNumberOneRead
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace
attribute [local irreducible] actualC actualA physicalTime sourcePoleRead sourceProjection

open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential PreparationVacuumFieldConstraintResponse
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open MeasureTheory

set_option backward.isDefEq.respectTransparency false in
private theorem uncutOperator_N1G0_range (f : Field289) (phi : Localizer) (r : ℝ) :
    sourceExcitedProjection*uncutOperator f phi r*sourceProjection=uncutOperator f phi r*sourceProjection := by
  apply GaussYukawaGrade.core_ext
  intro test
  simp only [mul_apply_eq_comp]
  rw [show sourceProjection (embed test)=embed (GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel test) from
    by simpa only [sourceProjection] using (GaussCoreLabel.embed_project CanonicalGradedCurrent.sourceLabel test).symm]
  rw [uncutOperator_core]
  rw [show sourceExcitedProjection (embed _)=embed (GaussCoreLabel.project sourceExcitedLabel _) from
    by simpa only [sourceExcitedProjection] using (GaussCoreLabel.embed_project sourceExcitedLabel _).symm]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  change fiberPiece sourceExcitedLabel ((_:ℂ) • sourceMap (scalarField (fieldCoordinateCurve f r z))
    (fiberPiece CanonicalGradedCurrent.sourceLabel (test z)))=_
  rw [map_smul,sourceMap_N1G0_range]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem uncutOperator_N1G1_zero (f : Field289) (phi : Localizer) (r : ℝ) :
    uncutOperator f phi r*sourceExcitedProjection=0 := by
  apply GaussYukawaGrade.core_ext
  intro test
  simp only [mul_apply_eq_comp,zero_apply]
  rw [show sourceExcitedProjection (embed test)=embed (GaussCoreLabel.project sourceExcitedLabel test) from
    by simpa only [sourceExcitedProjection] using (GaussCoreLabel.embed_project sourceExcitedLabel test).symm]
  rw [uncutOperator_core]
  rw [←map_zero embed]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  change (_:ℂ) • sourceMap (scalarField (fieldCoordinateCurve f r z))
    (fiberPiece sourceExcitedLabel (test z))=0
  rw [sourceMap_N1G1_zero,smul_zero]


set_option backward.isDefEq.respectTransparency false in
theorem actualA_N1G0_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceExcitedProjection*actualA p F*sourceProjection=actualA p F*sourceProjection :=
  by simpa only [actualA] using uncutOperator_N1G0_range 0 (PreparationVacuumYukawaTransport.finiteRetainer p F) 0

set_option backward.isDefEq.respectTransparency false in
theorem actualA_N1G1_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    actualA p F*sourceExcitedProjection=0 :=
  by simpa only [actualA] using uncutOperator_N1G1_zero 0 (PreparationVacuumYukawaTransport.finiteRetainer p F) 0

theorem actualC_excitedProjection (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    Commute sourceExcitedProjection (actualC p F):=by
  simpa only [sourceExcitedProjection,actualC] using
    CanonicalPhysicalSpatial.compression_blocks p F sourceExcitedLabel

private theorem interaction_range {R : Type*} [Ring R] [Algebra ℂ R]
    (P Q U V A : R) (QU : Commute Q U) (PV : Commute P V) (range : Q*A*P=A*P) :
    Q*(U*((-Complex.I) • A)*V)*P=U*((-Complex.I) • A)*V*P := by
  have h : Q*(U*A*V)*P=U*A*V*P := by
    calc
      _=(Q*U)*A*(V*P):=by noncomm_ring
      _=(U*Q)*A*(P*V):=by rw [QU.eq,PV.symm.eq]
      _=U*(Q*A*P)*V:=by noncomm_ring
      _=U*A*P*V:=by rw [range]; noncomm_ring
      _=U*A*V*P:=by noncomm_ring [PV.eq]
  simpa only [mul_smul_comm,smul_mul_assoc] using congrArg (fun B : R=>(-Complex.I) • B) h

private theorem interaction_zero {R : Type*} [Ring R] [Algebra ℂ R]
    (Q U V A : R) (QV : Commute Q V) (zero : A*Q=0) :
    (U*((-Complex.I) • A)*V)*Q=0 := by
  have h : (U*A*V)*Q=0:=by
    calc
      _=U*(A*Q)*V:=by noncomm_ring [QV.symm.eq]
      _=0:=by rw [zero,mul_zero,zero_mul]
  simpa only [mul_smul_comm,smul_mul_assoc,smul_zero] using congrArg (fun B : R=>(-Complex.I) • B) h

theorem actualInteraction_N1G0_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    sourceExcitedProjection*interaction (actualC p F) (actualA p F) t*sourceProjection=
      interaction (actualC p F) (actualA p F) t*sourceProjection :=
  interaction_range _ _ _ _ _
    (SourceFiniteUnitary.time_commutes _ _ (actualC_excitedProjection p F) t)
    (SourceFiniteUnitary.time_commutes _ _ (actualC_sourceProjection p F) (-t))
    (actualA_N1G0_range p F)

theorem actualInteraction_N1G1_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    interaction (actualC p F) (actualA p F) t*sourceExcitedProjection=0 :=
  interaction_zero _ _ _ _
    (SourceFiniteUnitary.time_commutes _ _ (actualC_excitedProjection p F) (-t)) (actualA_N1G1_zero p F)

private theorem zeroIntegralRight {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (f : ℝ→E→L[ℂ] E) (hf : Continuous f) (P : E→L[ℂ] E) (t : ℝ)
    (zero : ∀s,f s*P=0) : (∫s in (0:ℝ)..t,f s)*P=0 := by
  let r : (E→L[ℂ] E)→L[ℂ] (E→L[ℂ] E):=(ContinuousLinearMap.mul ℂ (E→L[ℂ] E)).flip P
  have h := r.intervalIntegral_comp_comm (hf.intervalIntegrable (μ:=volume) 0 t)
  change (∫s in (0:ℝ)..t,f s*P)=(∫s in (0:ℝ)..t,f s)*P at h
  simp_rw [zero] at h
  simpa only [intervalIntegral.integral_zero] using h.symm

theorem actualOrdered_N1G1_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (t : ℝ) (positive : 0<n) :
    orderedIntegral (actualC p F) (actualA p F) n t*sourceExcitedProjection=0 := by
  cases n with
  | zero => omega
  | succ n =>
    apply zeroIntegralRight _ ((orderedIntegral_continuous _ _ n).mul (interaction_continuous _ _))
    intro s
    change (orderedIntegral (actualC p F) (actualA p F) n s*interaction (actualC p F) (actualA p F) s)*sourceExcitedProjection=0
    rw [mul_assoc,actualInteraction_N1G1_zero,mul_zero]

theorem actualOrdered_N1G0_high_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (t : ℝ) (high : 1<n) :
    orderedIntegral (actualC p F) (actualA p F) n t*sourceProjection=0 := by
  cases n with
  | zero => omega
  | succ n =>
    apply zeroIntegralRight _ ((orderedIntegral_continuous _ _ n).mul (interaction_continuous _ _))
    intro s
    change (orderedIntegral (actualC p F) (actualA p F) n s*interaction (actualC p F) (actualA p F) s)*sourceProjection=0
    have range := actualInteraction_N1G0_range p F s
    rw [mul_assoc,←range,←mul_assoc,←mul_assoc,actualOrdered_N1G1_zero p F n s (by omega),zero_mul,zero_mul]

theorem actualPrefix_N1G0_high_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (t : ℝ) (high : 1<n) :
    finitePrefix (actualC p F) (actualA p F) n t*sourceProjection=0 := by
  unfold finitePrefix
  have h := SourceFiniteUnitary.time_commutes _ _ (actualC_sourceProjection p F) t
  calc
    _=orderedIntegral (actualC p F) (actualA p F) n t*sourceProjection*SourceFiniteUnitary.time (actualC p F) t:=by
      rw [mul_assoc,←h.eq,←mul_assoc]
    _=0:=by rw [actualOrdered_N1G0_high_zero p F n t high,zero_mul]



private theorem firstReturnInverse {R : Type*} [Ring R] (P Q D A U V : R)
    (PU : Commute P U) (QU : Commute Q U) (range : Q*A*P=A*P) (zero : A*Q=0)
    (free : D*U=1) (full : V*(D+A)=1) : V*P=(U-U*A*U)*P := by
  have nilpotent : A*U*A*U*P=0 := by
    calc
      _=A*U*(A*P)*U:=by noncomm_ring [PU.symm.eq]
      _=A*U*(Q*A*P)*U:=by rw [range]
      _=A*(U*Q)*A*P*U:=by noncomm_ring
      _=A*(Q*U)*A*P*U:=by rw [QU.symm.eq]
      _=(A*Q)*U*A*P*U:=by noncomm_ring
      _=0:=by rw [zero,zero_mul,zero_mul,zero_mul,zero_mul]
  have generated : (D+A)*(U-U*A*U)*P=P := by
    calc
      _=(D*U)*P+A*U*P-((D*U)*A*U*P+A*U*A*U*P):=by noncomm_ring
      _=P:=by rw [free,nilpotent,one_mul,one_mul,add_zero];abel
  calc
    V*P=V*((D+A)*(U-U*A*U)*P):=by rw [generated]
    _=(V*(D+A))*((U-U*A*U)*P):=by noncomm_ring
    _=(U-U*A*U)*P:=by rw [full,one_mul]

set_option backward.isDefEq.respectTransparency false in
theorem actual_resolvent_N1G0_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) :
    jointResolvent p F z 0*sourceProjection=
      (CanonicalPhysicalResolvent.finiteResolvent p F z-
        CanonicalPhysicalResolvent.finiteResolvent p F z*actualA p F*CanonicalPhysicalResolvent.finiteResolvent p F z)*sourceProjection := by
  have free := FullYSourceResolventGraphSplice.resolvent_right (actualC p F) (actualC_symmetric p F) z nonreal
  simp only [actualC] at free
  have full := sourceMaterialInverse_left p F z nonreal
  rw [actualGenerator_source] at full
  simp only [actualC] at full
  have full' : jointResolvent p F z 0*((CanonicalPhysicalSpatial.compression p F-z • 1)+actualA p F)=1:=by
    simpa only [sub_add_eq_add_sub] using full
  have commute (P : GaussCoreHilbert.H→L[ℂ] GaussCoreHilbert.H) (h : Commute P (actualC p F)) :
      Commute P (CanonicalPhysicalResolvent.finiteResolvent p F z) := by
    unfold CanonicalPhysicalResolvent.finiteResolvent FullYSourceResolventGraphSplice.resolvent
    exact PreparationVacuumYukawaTransport.inverse_commuting _ _
      (FullYSourceResolventGraphSplice.resolvent_isUnit _ (CanonicalPhysicalSpatial.compression_selfAdjoint p F) z nonreal)
      ((show Commute P (CanonicalPhysicalSpatial.compression p F) from by simpa only [actualC] using h).sub_right
        ((Commute.one_right _).smul_right z))
  simpa only [CanonicalPhysicalResolvent.finiteResolvent] using
    firstReturnInverse sourceProjection sourceExcitedProjection (CanonicalPhysicalSpatial.compression p F-z • 1) (actualA p F)
      (FullYSourceResolventGraphSplice.resolvent (CanonicalPhysicalSpatial.compression p F) z) (jointResolvent p F z 0)
      (commute _ (actualC_sourceProjection p F)) (commute _ (actualC_excitedProjection p F))
      (actualA_N1G0_range p F) (actualA_N1G1_zero p F) free full'

end LowEnergy.PreparationVacuumPhysicalNumberOneRead
