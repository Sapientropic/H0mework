import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedGradeZero

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalLockedCurrentFirstResidue
open GaussCoreHilbert GaussCoreDifferential GaussCoreLabel NativeHistoryGrade
open PreparationVacuumPhysicalElectromagneticDirection PreparationVacuumFullFieldRiesz
open PreparationVacuumSourceFieldFamily PreparationVacuumSourceActionJets PreparationVacuumRawJointFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumPhysicalNumberOneRead
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumElectromagneticIdentity PreparationVacuumJointFieldResponse
open PreparationVacuumPropagationPencil PreparationVacuumGaugeSlowFrequency
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumFixedMomentumActionReturn CanonicalGradedSpatialSource CanonicalGradedCurrent
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates PreparationVacuumGaugeSourceInjection
open SourceFiniteUnitary MeasureTheory Set Filter
open scoped BigOperators InnerProductSpace Topology
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
attribute [local irreducible] frameVector frameTest finiteRiesz sourceLockedReader sourceLockedForm
  actualC actualA sourceProjection physicalTime jointResolvent rawHalf rawReader sourcePoleRead
  sourceMatterActionOperator

private theorem sample_project (g : Label) (z : SourceCoordinateSlice) (u v : FockFiber) :
    pairSample z (fiberPiece g u) v=pairSample z u (fiberPiece g v) := by
  unfold pairSample
  apply Finset.sum_congr rfl
  intro word _
  simp only [fiberPiece_apply]
  by_cases same : NativeHistoryGrade.sourceLabel word=g <;> simp [same]

private theorem locked_weak_project (mu : Fin 4) (i : Fin 3) (g : Label) (a b : QuantumTest) :
    sourceLockedForm mu i (project g a) b=sourceLockedForm mu i a (project g b) := by
  unfold sourceLockedForm
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  simp only [project_apply]
  rw [sample_project]
  have generated:=congrArg (fun A : FockFiber→L[ℂ] FockFiber=>A (b z))
    (sourceLockedFiber_blocks mu i z g).eq
  simpa only [mul_apply_eq_comp] using congrArg (fun v=>pairSample z (a z) v) generated

private theorem frame_project (F : GaussUnitaryHistory.Index) (i : FrameIndex F) (g : Label) :
    project g (frameTest F i)=if g=i.1 then frameTest F i else 0 := by
  by_cases same : g=i.1
  · rw [if_pos same]
    apply embed_injective
    rw [embed_project,frameTest_embed]
    unfold frameVector
    rw [←mul_apply_eq_comp,projection_product,if_pos same,same]
  · rw [if_neg same]
    apply embed_injective
    rw [embed_project,frameTest_embed,map_zero]
    unfold frameVector
    rw [←mul_apply_eq_comp,projection_product,if_neg same]
    exact zero_apply _

private theorem locked_frame_off (mu : Fin 4) (i : Fin 3) (F : GaussUnitaryHistory.Index)
    (a b : FrameIndex F) (different : a.1≠b.1) :
    sourceLockedForm mu i (frameTest F a) (frameTest F b)=0 := by
  have generated:=locked_weak_project mu i a.1 (frameTest F a) (frameTest F b)
  rw [frame_project,if_pos rfl,frame_project,if_neg different] at generated
  refine generated.trans ?_
  unfold sourceLockedForm
  simp [pairSample]

private theorem frame_projection (F : GaussUnitaryHistory.Index) (i : FrameIndex F) (g : Label) :
    projection g (frameVector F i)=if g=i.1 then frameVector F i else 0:=by
  unfold frameVector
  rw [←mul_apply_eq_comp,projection_product]
  by_cases same : g=i.1 <;> simp [same]

private theorem frame_rank_left (F : GaussUnitaryHistory.Index) (i j : FrameIndex F) (g : Label) :
    projection g*InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j)=
      if g=i.1 then InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j) else 0:=by
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp,InnerProductSpace.rankOne_apply,map_smul,frame_projection]
  by_cases same : g=i.1 <;> simp [same]

private theorem rank_right_of_projection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : E→L[ℂ] E) (symmetric : P.toLinearMap.IsSymmetric) (x y : E)
    (keep : Prop) [Decidable keep] (paid : P y=if keep then y else 0) :
    InnerProductSpace.rankOne ℂ x y*P=if keep then InnerProductSpace.rankOne ℂ x y else 0:=by
  apply ContinuousLinearMap.ext
  intro z
  simp only [mul_apply_eq_comp,InnerProductSpace.rankOne_apply]
  have read : inner ℂ y (P z)=inner ℂ (P y) z:=by exact (symmetric y z).symm
  rw [read,paid]
  by_cases same : keep
  · simp only [if_pos same,InnerProductSpace.rankOne_apply]
  · simp only [if_neg same,inner_zero_left,zero_smul,zero_apply]

private theorem frame_rank_right (F : GaussUnitaryHistory.Index) (i j : FrameIndex F) (g : Label) :
    InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j)*projection g=
      if g=j.1 then InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j) else 0:=
  rank_right_of_projection (projection g) (projection_symmetric g)
    (frameVector F i) (frameVector F j) (g=j.1) (frame_projection F j g)

private theorem zeroScalar_smul_same {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (e : ℂ) (x y : M) (h : e=0) : e • x=e • y:=by
  subst e
  simp only [zero_smul]


/-- The original finite Riesz reader preserves every source occupation/grade block. -/
theorem sourceLockedReader_blocks (mu : Fin 4) (i : Fin 3) (F : GaussUnitaryHistory.Index)
    (g : Label) : Commute (projection g) (sourceLockedReader mu i F) := by
  change projection g*sourceLockedReader mu i F=sourceLockedReader mu i F*projection g
  unfold sourceLockedReader finiteRiesz
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,frame_rank_left,frame_rank_right]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases same : a.1=b.1
  · have predicates : (g=a.1)↔(g=b.1):=by rw [same]
    simp only [predicates]
  · exact zeroScalar_smul_same (M:=H→L[ℂ] H)
      (sourceLockedForm mu i (frameTest F a) (frameTest F b))
      (if g=a.1 then InnerProductSpace.rankOne ℂ (frameVector F a) (frameVector F b) else 0)
      (if g=b.1 then InnerProductSpace.rankOne ℂ (frameVector F a) (frameVector F b) else 0)
      (locked_frame_off mu i F a b same)

/-- Coordinates are generated by the same original action derivative, rather than a separate field source. -/
theorem sourceLockedReader_coordinates (mu : Fin 4) (i : Fin 3) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) :
    sourceLockedReader mu i F=∑j : Fin 289,sourceLockedField mu i j • rawReader (fieldUnit j) p F 0 := by
  have basis : sourceLockedField mu i=∑j : Fin 289,sourceLockedField mu i j • fieldUnit j := by
    funext k
    simp [fieldUnit,Finset.sum_apply,Pi.single_apply]
  have generated:=congrArg (fderiv ℝ (sourceMatterActionOperator p F) 0) basis
  simp only [map_sum,map_smul,sourceMatterActionOperator_gradient,sourceLockedReader_generated] at generated
  exact generated

private theorem projected_word {R : Type*} [Ring R]
    (P A B J D E a b d e : R)
    (hA : P*A=a*P) (hB : P*B=b*P) (hJ : P*J=J*P)
    (hD : P*D=d*P) (hE : P*E=e*P) :
    P*(A*B*J*D*E)=(a*b*J*d*e)*P:=by
  calc
    _=(P*A)*B*J*D*E:=by noncomm_ring
    _=a*(P*B)*J*D*E:=by rw [hA];noncomm_ring
    _=a*b*(P*J)*D*E:=by rw [hB];noncomm_ring
    _=a*b*J*(P*D)*E:=by rw [hJ];noncomm_ring
    _=a*b*J*d*(P*E):=by rw [hD];noncomm_ring
    _=_:=by rw [hE];noncomm_ring

private theorem bareTime_blocks (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    Commute sourceProjection (time (actualC p F) t):=
  time_commutes _ _ (actualC_sourceProjection p F) t

private theorem bareResolvent_blocks (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) : Commute sourceProjection (CanonicalPhysicalResolvent.finiteResolvent p F z):=by
  unfold CanonicalPhysicalResolvent.finiteResolvent FullYSourceResolventGraphSplice.resolvent
  exact PreparationVacuumYukawaTransport.inverse_commuting _ _
    (FullYSourceResolventGraphSplice.resolvent_isUnit _ (CanonicalPhysicalSpatial.compression_selfAdjoint p F) z nonreal)
    ((show Commute sourceProjection (CanonicalPhysicalSpatial.compression p F) from
      by simpa only [actualC] using actualC_sourceProjection p F).sub_right
      ((Commute.one_right _).smul_right z))


def sourceLockedZeroHistoryKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (i : Fin 3) (t : ℝ) : H→L[ℂ] H :=
  time (actualC pL q.F) (-t)*CanonicalPhysicalResolvent.finiteResolvent pL q.F q.z*
    sourceLockedReader mu i q.F*CanonicalPhysicalResolvent.finiteResolvent pR q.F q.w*
      time (actualC pR q.F) t

/-- Every positive time-history term is removed by the actual grade-zero reader, on the original fulljoint word. -/
theorem sourceLockedKernel_projected (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (i : Fin 3) (t : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceProjection*sourceLockedKernel q pL pR mu i t=
      sourceLockedZeroHistoryKernel q pL pR mu i t*sourceProjection := by
  unfold sourceLockedKernel sourceLockedZeroHistoryKernel
  exact projected_word _ _ _ _ _ _ _ _ _ _
    ((actual_time_sourceProjection pL q.F (-t)).trans (bareTime_blocks pL q.F (-t)).eq)
    ((actual_resolvent_sourceProjection pL q.F q.z nonrealL).trans (bareResolvent_blocks pL q.F q.z nonrealL).eq)
    (by simpa only [sourceProjection] using (sourceLockedReader_blocks mu i q.F sourceLabel).eq)
    ((actual_resolvent_sourceProjection pR q.F q.w nonrealR).trans (bareResolvent_blocks pR q.F q.w nonrealR).eq)
    ((actual_time_sourceProjection pR q.F t).trans (bareTime_blocks pR q.F t).eq)

end LowEnergy.PreparationVacuumPhysicalLockedCurrentFirstResidue
