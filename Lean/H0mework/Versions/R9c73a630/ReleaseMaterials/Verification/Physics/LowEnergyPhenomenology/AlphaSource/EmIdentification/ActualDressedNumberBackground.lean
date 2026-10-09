import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberTimeRange

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberZero
open GaussCoreHilbert GaussComposite.SourceGraph
open CanonicalGradedCurrent CanonicalGradedSpatialSource
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalPoleAmputation
open PreparationVacuumPhysicalNumberOneRead PreparationVacuumPhysicalN1WardCollapse
open PreparationVacuumPhysicalGradeZeroRead
open FullYSourceCutoffVolterra
open scoped Topology
attribute [local irreducible] sourceProjection sourceExcitedProjection sourceN1Projection
  actualC actualA physicalTime jointResolvent

/-- The unchanged graph profile has the original seed's N1/G0 identity. -/
theorem actual_background_N1G0 (profile : Profile) : sourceProjection (prepared profile)=prepared profile := by
  refine core_dense.induction_on profile (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [prepared_core]
  have original:=congrArg embed (ActualRadial.seedSection_project f)
  simpa only [GaussCoreLabel.embed_project,sourceProjection] using original

theorem actual_background_number_one (profile : Profile) : sourceN1Projection (prepared profile)=prepared profile := by
  have original:=sourceN1Projection_source (prepared profile)
  simpa only [actual_background_N1G0] using original

/-- The actual background time uses its original two prefixes, at every time and momentum. -/
theorem actual_time_background (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) (profile : Profile) :
    physicalTime p F t 0 (prepared profile)=partialEvolution (actualC p F) (actualA p F) 1 t (prepared profile) := by
  have truncated (n : ℕ) : partialEvolution (actualC p F) (actualA p F) (n+1) t*sourceProjection=
      partialEvolution (actualC p F) (actualA p F) 1 t*sourceProjection := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [partialEvolution,add_mul,ih,actualPrefix_N1G0_high_zero p F (n+2) t (by omega),add_zero]
  have original:=congrArg (fun A : Op=>A (prepared profile)) (truncated 55)
  rw [actual_time_finitePrefix]
  simpa only [mul_apply_eq_comp,actual_background_N1G0] using original

private theorem inverse_preserves_one (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (P : Op) (blocks : Commute P (actualC p F)) :
    Commute P (CanonicalPhysicalResolvent.finiteResolvent p F z) := by
  unfold CanonicalPhysicalResolvent.finiteResolvent FullYSourceResolventGraphSplice.resolvent
  exact PreparationVacuumYukawaTransport.inverse_commuting _ _
    (FullYSourceResolventGraphSplice.resolvent_isUnit _ (CanonicalPhysicalSpatial.compression_selfAdjoint p F) z nonreal)
    ((show Commute P (CanonicalPhysicalSpatial.compression p F) from
      by simpa only [actualC] using blocks).sub_right ((Commute.one_right _).smul_right z))

private theorem inverse_one_range {R : Type*} [Ring R] (P Q A U : R)
    (PU : Commute P U) (range : Q*A*P=A*P) : Q*(A*U)*P=(A*U)*P := by
  calc
    _=(Q*A)*(U*P) := by noncomm_ring
    _=(Q*A)*(P*U) := by rw [PU.symm.eq]
    _=(Q*A*P)*U := by noncomm_ring
    _=(A*P)*U := by rw [range]
    _=A*(P*U) := by rw [mul_assoc]
    _=A*(U*P) := by rw [PU.eq]
    _=_ := by rw [mul_assoc]

private theorem inverse_one_terminal {R : Type*} [Ring R] (P A U : R)
    (PU : Commute P U) (terminal : A*P=0) : (A*U)*P=0 := by
  rw [mul_assoc,PU.symm.eq,←mul_assoc,terminal,zero_mul]

private theorem inverse_two_return {R : Type*} [Ring R] (P D A U V : R)
    (free : D*U=1) (full : V*(D+A)=1) (terminal : A*U*A*U*P=0) : V*P=(U-U*A*U)*P := by
  have generated : (D+A)*(U-U*A*U)*P=P := by
    calc
      _=(D*U)*P+A*U*P-((D*U)*A*U*P+A*U*A*U*P) := by noncomm_ring
      _=P := by rw [free,terminal]; noncomm_ring
  calc
    _=V*((D+A)*(U-U*A*U)*P) := by rw [generated]
    _=(V*(D+A))*((U-U*A*U)*P) := by noncomm_ring
    _=_ := by rw [full,one_mul]

/-- The complete original N1 sector returns two C-Green/Yukawa words, including the evolved background. -/
theorem actual_resolvent_number_one_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) : jointResolvent p F z 0*sourceN1Projection=
      (CanonicalPhysicalResolvent.finiteResolvent p F z-
        CanonicalPhysicalResolvent.finiteResolvent p F z*actualA p F*CanonicalPhysicalResolvent.finiteResolvent p F z)*sourceN1Projection := by
  let U:=CanonicalPhysicalResolvent.finiteResolvent p F z
  let B:=actualA p F*U
  have range : sourceExcitedProjection*B*sourceProjection=B*sourceProjection :=
    inverse_one_range _ _ _ _ (inverse_preserves_one p F z nonreal _ (actualC_sourceProjection p F))
      (actualA_N1G0_range p F)
  have terminal : B*sourceExcitedProjection=0 :=
    inverse_one_terminal _ _ _ (inverse_preserves_one p F z nonreal _ (actualC_excitedProjection p F))
      (actualA_N1G1_zero p F)
  have base_zero : B*B*sourceProjection=0 := by
    calc
      _=B*(B*sourceProjection) := by rw [mul_assoc]
      _=B*(sourceExcitedProjection*B*sourceProjection) := by rw [range]
      _=(B*sourceExcitedProjection)*B*sourceProjection := by noncomm_ring
      _=0 := by rw [terminal,zero_mul,zero_mul]
  have generated : actualA p F*U*actualA p F*U*sourceN1Projection=0 := by
    have original : B*B*(sourceProjection+sourceExcitedProjection)=0 := by
      rw [mul_add,base_zero,mul_assoc B B sourceExcitedProjection,terminal,mul_zero,add_zero]
    simpa only [B,sourceN1Projection,mul_assoc] using original
  have free:=FullYSourceResolventGraphSplice.resolvent_right (actualC p F) (actualC_symmetric p F) z nonreal
  have free' : (actualC p F-z • 1)*U=1 := by
    simpa only [U,actualC,CanonicalPhysicalResolvent.finiteResolvent] using free
  have full:=sourceMaterialInverse_left p F z nonreal
  rw [actualGenerator_source] at full
  have full' : jointResolvent p F z 0*((actualC p F-z • 1)+actualA p F)=1 := by
    simpa only [sub_add_eq_add_sub] using full
  exact inverse_two_return sourceN1Projection (actualC p F-z • 1) (actualA p F) U (jointResolvent p F z 0) free' full' generated

theorem actual_background_resolvent_time_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (t : ℝ) (profile : Profile) :
    jointResolvent p F z 0 (physicalTime p F t 0 (prepared profile))=
      (CanonicalPhysicalResolvent.finiteResolvent p F z-
        CanonicalPhysicalResolvent.finiteResolvent p F z*actualA p F*CanonicalPhysicalResolvent.finiteResolvent p F z)
        (partialEvolution (actualC p F) (actualA p F) 1 t (prepared profile)) := by
  have time_range:=congrArg (fun A : Op=>A (prepared profile)) (actualTime_sourceN1_range p F t)
  simp only [mul_apply_eq_comp,actual_background_number_one] at time_range
  have returned:=congrArg (fun A : Op=>A (physicalTime p F t 0 (prepared profile)))
    (actual_resolvent_number_one_return p F z nonreal)
  simp only [mul_apply_eq_comp] at returned
  rw [time_range] at returned
  simpa only [actual_time_background] using returned

end LowEnergy.GaussComposite.ActualDressedNumberZero
