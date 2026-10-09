import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationPhiGrade
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceProjectionReturn
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationGaugeFields

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalGradeZeroRead
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineDiracDualYukawaSpinJurisdiction SU7MotherLieAlgebra
open PreparationVacuumGaugeSourceInjection PreparationVacuumSourceFieldFamily
open PreparationVacuumActualFieldQuantization PreparationVacuumActionFieldLift
open PreparationVacuumMixedFieldReturn PreparationVacuumLowerClassical
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates CanonicalGradedSpatialSource
open GaussFockLabel GaussNativeMatter GaussYukawaGrade GaussHistoryHilbert
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open GaussCoreHilbert GaussCoreDifferential GaussCoreLabel NativeHistoryGrade
open PreparationVacuumSourceActionJets PreparationVacuumRawJointFeedback PreparationVacuumFullFieldRiesz
open PreparationVacuumPhysicalZeroRead PreparationVacuumPhysicalHalfAxis
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumElectromagneticIdentity
open CanonicalGradedCurrent PreparationVacuumPhysicalFeedback SourceFiniteUnitary
open MeasureTheory Set
open scoped Matrix BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local irreducible] frameVector PreparationVacuumFullFieldRiesz.sourceBasis
  frameTest rawForm rawReader finiteRiesz fiberPiece NativeHistoryGrade.projection

private def primalPreserves (A : SourceMatrix) : Prop:=∀i j,
  ((if isSix i then (1:ℂ) else 0)-(if isSix j then (1:ℂ) else 0))*A i j=0

private theorem primal_smul (A : SourceMatrix) (hA : primalPreserves A) (c : ℂ) :
    primalPreserves (c • A):=by
  intro i j
  change _*(c*A i j)=0
  rw [mul_left_comm,hA i j,mul_zero]

private theorem primal_mul (A B : SourceMatrix) (hA : primalPreserves A) (hB : primalPreserves B) :
    primalPreserves (A*B):=by
  intro i j
  rw [Matrix.mul_apply,Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro k _
  calc
    _=(((if isSix i then (1:ℂ) else 0)-(if isSix k then (1:ℂ) else 0))*A i k)*B k j+
      A i k*(((if isSix k then (1:ℂ) else 0)-(if isSix j then (1:ℂ) else 0))*B k j):=by ring
    _=0:=by rw [hA i k,hB k j,zero_mul,mul_zero,add_zero]

private theorem primal_mother (A : Module.End ℂ DiracExteriorMatterCarrier)
    (paid : Commute MixedSymbol.degreeSix A) : primalPreserves (Quantum.operatorMatrix A):=by
  intro i j
  simpa only [Nat.cast_zero,sub_zero] using matrix_grade A 0
    (by simpa only [Nat.cast_zero,zero_smul,add_zero] using paid.eq) i j

private theorem primal_coefficient (mu : Fin 4) (e : LorentzianCoframe) :
    primalPreserves (coefficientMatrix mu e):=by
  unfold coefficientMatrix
  apply primal_smul
  exact primal_mother _ (MixedSymbol.degreeSix_spin _)

private theorem primal_densityAction : primalPreserves densityActionMatrix:=by
  unfold densityActionMatrix
  apply primal_smul
  apply primal_mother
  show MixedSymbol.degreeSix*YangMills.FullPairing.flipMatter=
    YangMills.FullPairing.flipMatter*MixedSymbol.degreeSix
  apply LinearMap.ext
  intro v
  funext spin
  rfl

private theorem primal_native (a : Fin 12) : primalPreserves (nativePrimal (originalUnit a)):=
  primal_mother _ (MixedSymbol.degreeSix_gauge _)

private theorem full_branches (A : SourceMatrix) (paid : primalPreserves A) :
    Preserves (SourceRealScalarFock.branches A):=by
  intro i j
  simpa only [charge,Nat.cast_zero,sub_zero] using branches_grade A 0
    (by intro u v; simpa only [Nat.cast_zero,sub_zero] using paid u v) i j

private theorem opposite_preserves : Preserves oppositeDual:=by
  intro i j
  cases i <;> cases j <;> simp [charge,oppositeDual,Matrix.fromBlocks,Matrix.one_apply]
  all_goals intro same;subst same;ring

private def rawGaugeCoefficient (mu : Fin 4) (a : Fin 12) (s : ActionState) : SourceMatrix:=
  densityActionMatrix*(stateVolume s • (coefficientMatrix mu s.1*nativePrimal (originalUnit a)))

private theorem rawGaugeCoefficient_preserves (mu : Fin 4) (a : Fin 12) (s : ActionState) :
    primalPreserves (rawGaugeCoefficient mu a s):=
  primal_mul _ _ primal_densityAction (primal_smul _
    (primal_mul _ _ (primal_coefficient mu s.1) (primal_native a)) (stateVolume s))

private theorem rawGaugeSymbol_generated (mu : Fin 4) (a : Fin 12) (p : PhysicalMomentum)
    (s : ActionState) (nondegenerate : s.1.det≠0) :
    rawActionSymbol (gaugeField mu a) p s=oppositeDual*SourceRealScalarFock.branches (rawGaugeCoefficient mu a s):=by
  unfold rawActionSymbol rawFourier
  simp only [gauge_density mu a s nondegenerate]
  change oppositeDual*realFourierMatrix
    (fun i=>densityActionMatrix*(if i=0 then stateVolume s •
      (coefficientMatrix mu s.1*nativePrimal (originalUnit a)) else 0)) p= _
  simp [realFourierMatrix,affineMatrix,rawGaugeCoefficient,SourceRealScalarFock.branches]

theorem sourceRawGaugeMatrix_gradeZero (mu : Fin 4) (a : Fin 12) (p : PhysicalMomentum) (z : physicalChart) :
    Preserves (rawActionSymbol (gaugeField mu a) p (sourceState z.val)):=by
  rw [rawGaugeSymbol_generated mu a p (sourceState z.val) (coframe_nondegenerate z)]
  exact preserves_mul opposite_preserves (full_branches _ (rawGaugeCoefficient_preserves mu a _))

theorem sourceRawGaugeFiber_gradeZero (mu : Fin 4) (a : Fin 12) (p : PhysicalMomentum) (z : physicalChart) :
    Commute fiberGrade (rawStateFiber (gaugeField mu a) p (sourceState z.val)):=by
  rw [←rawActionSymbol_actual]
  exact blockWeight_quantized _ _ (sourceRawGaugeMatrix_gradeZero mu a p z)

private theorem sample_project (g : Label) (z : SourceCoordinateSlice) (u v : FockFiber) :
    pairSample z (fiberPiece g u) v=pairSample z u (fiberPiece g v):=by
  unfold pairSample
  apply Finset.sum_congr rfl
  intro word _
  simp only [fiberPiece_apply]
  by_cases same : NativeHistoryGrade.sourceLabel word=g <;> simp [same]

private theorem rawGaugeFiber_blocks (mu : Fin 4) (a : Fin 12) (p : PhysicalMomentum)
    (z : physicalChart) (g : Label) : Commute (fiberPiece g)
      (rawStateFiber (gaugeField mu a) p (sourceState z.val)):=by
  rw [←rawActionSymbol_actual]
  unfold fiberPiece
  exact blockWeight_quantized _ _ (sourceRawGaugeMatrix_gradeZero mu a p z)

private theorem rawGauge_weak_project (mu : Fin 4) (a : Fin 12) (p : PhysicalMomentum)
    (g : Label) (f h : QuantumTest) :
    rawForm (gaugeField mu a) p (project g f) h 0=rawForm (gaugeField mu a) p f (project g h) 0:=by
  rw [rawForm_original,rawForm_original]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  simp only [project_apply]
  by_cases inside : z∈physicalChart
  · rw [sample_project]
    have commutes:=congrArg (fun A : FockFiber→L[ℂ] FockFiber=>A (h z))
      (rawGaugeFiber_blocks mu a p ⟨z,inside⟩ g).eq
    simpa only [mul_apply_eq_comp] using congrArg (fun v=>pairSample z (f z) v) commutes
  · have off : z∉tsupport f:=fun member=>inside (f.tsupport_subset member)
    rw [image_eq_zero_of_notMem_tsupport off,map_zero,pairSample_zero_left,pairSample_zero_left]

private theorem frame_project (F : GaussUnitaryHistory.Index) (i : FrameIndex F) (g : Label) :
    project g (frameTest F i)=if g=i.1 then frameTest F i else 0:=by
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

private theorem rawGauge_frame_off (mu : Fin 4) (a : Fin 12) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (i j : FrameIndex F) (different : i.1≠j.1) :
    rawForm (gaugeField mu a) p (frameTest F i) (frameTest F j) 0=0:=by
  have paid:=rawGauge_weak_project mu a p i.1 (frameTest F i) (frameTest F j)
  rw [frame_project,if_pos rfl,frame_project,if_neg different] at paid
  refine paid.trans ?_
  rw [rawForm_original]
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

set_option backward.isDefEq.respectTransparency false in

theorem sourceRawGaugeReader_blocks (mu : Fin 4) (a : Fin 12) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (g : Label) :
    Commute (projection g) (rawReader (gaugeField mu a) p F 0):=by
  change projection g*rawReader (gaugeField mu a) p F 0=rawReader (gaugeField mu a) p F 0*projection g
  unfold rawReader finiteRiesz
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,frame_rank_left,frame_rank_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases same : i.1=j.1
  · have predicates : (g=i.1)↔(g=j.1):=by rw [same]
    simp only [predicates]
  · exact zeroScalar_smul_same (M:=GaussCoreHilbert.H→L[ℂ] GaussCoreHilbert.H)
      (rawForm (gaugeField mu a) p (frameTest F i) (frameTest F j) 0)
      (if g=i.1 then InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j) else 0)
      (if g=j.1 then InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j) else 0)
      (rawGauge_frame_off mu a p F i j same)

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

def sourceGaugeZeroHistoryKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) (t : ℝ) : GaussCoreHilbert.H→L[ℂ] GaussCoreHilbert.H:=
  time (actualC pL q.F) (-t)*CanonicalPhysicalResolvent.finiteResolvent pL q.F q.z*
    rawReader (gaugeField mu a) pR q.F 0*CanonicalPhysicalResolvent.finiteResolvent pR q.F q.w*
      time (actualC pR q.F) t

theorem sourceGaugeKernel_projected (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) (t : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceProjection*fiveKernel (gaugeField mu a) pR (pL-pR) q.F q.z q.w t 0=
      sourceGaugeZeroHistoryKernel q pL pR mu a t*sourceProjection:=by
  have leftMomentum : pR+(pL-pR)=pL:=by ext i;simp
  unfold fiveKernel sourceGaugeZeroHistoryKernel
  rw [leftMomentum]
  exact projected_word _ _ _ _ _ _ _ _ _ _
    ((actual_time_sourceProjection pL q.F (-t)).trans (bareTime_blocks pL q.F (-t)).eq)
    ((actual_resolvent_sourceProjection pL q.F q.z nonrealL).trans (bareResolvent_blocks pL q.F q.z nonrealL).eq)
    (sourceRawGaugeReader_blocks mu a pR q.F CanonicalGradedCurrent.sourceLabel).eq
    ((actual_resolvent_sourceProjection pR q.F q.w nonrealR).trans (bareResolvent_blocks pR q.F q.w nonrealR).eq)
    ((actual_time_sourceProjection pR q.F t).trans (bareTime_blocks pR q.F t).eq)

set_option backward.isDefEq.respectTransparency false in
theorem sourceGaugeCurrent_zeroHistory (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (mu : Fin 4) (a : Fin 12) (t : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot mu a)=
      -sourcePoleRead q.epsilon q.precision pL pR left right (sourceGaugeZeroHistoryKernel q pL pR mu a t):=by
  rw [sourcePoleActionEuler_source]
  have unitField : fieldUnit (gaugeSlot mu a)=gaugeField mu a:=rfl
  rw [unitField,sourcePoleRead_actual,sourcePoleRead_actual]
  congr 1
  have fixedL:=sourcePolePrepared_sourceProjection q.epsilon q.precision pL left
  have fixedR:=sourcePolePrepared_sourceProjection q.epsilon q.precision pR right
  let K:=fiveKernel (gaugeField mu a) pR (pL-pR) q.F q.z q.w t 0
  let X:=sourcePolePrepared q.epsilon q.precision pL left
  let Y:=sourcePolePrepared q.epsilon q.precision pR right
  have paired : inner ℂ (sourceProjection X) (K Y)=inner ℂ X (sourceProjection (K Y)):=by
    unfold sourceProjection
    exact NativeHistoryGrade.projection_symmetric _ X (K Y)
  have generated:=congrArg (fun A : GaussCoreHilbert.H→L[ℂ] GaussCoreHilbert.H=>A Y)
    (sourceGaugeKernel_projected q pL pR mu a t nonrealL nonrealR)
  simp only [mul_apply_eq_comp] at generated
  change sourceProjection (K Y)=sourceGaugeZeroHistoryKernel q pL pR mu a t (sourceProjection Y) at generated
  rw [show sourceProjection Y=Y from fixedR] at generated
  change inner ℂ X (K Y)=_
  exact (congrArg (fun v : GaussCoreHilbert.H=>inner ℂ v (K Y)) fixedL.symm).trans
    (paired.trans (congrArg (fun v : GaussCoreHilbert.H=>inner ℂ X v) generated))

private theorem read_projected_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (K : GaussCoreHilbert.H→L[ℂ] GaussCoreHilbert.H)
    (paid : sourceProjection*K=0) : sourcePoleRead q.epsilon q.precision pL pR left right K=0:=by
  rw [sourcePoleRead_actual]
  let X:=sourcePolePrepared q.epsilon q.precision pL left
  let Y:=sourcePolePrepared q.epsilon q.precision pR right
  have fixed : sourceProjection X=X:=sourcePolePrepared_sourceProjection q.epsilon q.precision pL left
  have paired : inner ℂ (sourceProjection X) (K Y)=inner ℂ X (sourceProjection (K Y)):=by
    unfold sourceProjection
    exact NativeHistoryGrade.projection_symmetric _ X (K Y)
  have generated:=congrArg (fun A : GaussCoreHilbert.H→L[ℂ] GaussCoreHilbert.H=>A Y) paid
  simp only [mul_apply_eq_comp,zero_apply] at generated
  change inner ℂ X (K Y)=0
  exact (congrArg (fun v : GaussCoreHilbert.H=>inner ℂ v (K Y)) fixed.symm).trans
    (paired.trans (by rw [generated,inner_zero_right]))

theorem sourcePrincipalGaugeBlock_positive_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (mu : Fin 4) (a : Fin 12) (j k : Fin 57) (t : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) (positive : 0<j.val+k.val) :
    sourcePoleRead q.epsilon q.precision pL pR left right
      (sourcePrincipalBlock q pL pR (gaugeField mu a) j k t)=0:=by
  by_cases leftPositive : 0<j.val
  · exact sourcePrincipalBlock_left_positive_zero q pL pR left right _ j k t leftPositive
  have leftZero : j=0:=Fin.ext (by omega)
  rw [leftZero]
  apply read_projected_zero
  unfold sourcePrincipalBlock
  have base : FullYSourceCutoffVolterra.finitePrefix (actualC pL q.F) (actualA pL q.F) 0 (-t)=
      time (actualC pL q.F) (-t):=by simp [FullYSourceCutoffVolterra.finitePrefix,FullYSourceCutoffVolterra.orderedIntegral]
  simp only [Fin.val_zero]
  rw [base]
  have generated:=projected_word sourceProjection
    (time (actualC pL q.F) (-t)) (jointResolvent pL q.F q.z 0) (rawReader (gaugeField mu a) pR q.F 0)
    (jointResolvent pR q.F q.w 0) (FullYSourceCutoffVolterra.finitePrefix (actualC pR q.F) (actualA pR q.F) k.val t)
    (time (actualC pL q.F) (-t)) (CanonicalPhysicalResolvent.finiteResolvent pL q.F q.z)
    (CanonicalPhysicalResolvent.finiteResolvent pR q.F q.w) 0
    (bareTime_blocks pL q.F (-t)).eq
    ((actual_resolvent_sourceProjection pL q.F q.z nonrealL).trans (bareResolvent_blocks pL q.F q.z nonrealL).eq)
    (sourceRawGaugeReader_blocks mu a pR q.F CanonicalGradedCurrent.sourceLabel).eq
    ((actual_resolvent_sourceProjection pR q.F q.w nonrealR).trans (bareResolvent_blocks pR q.F q.w nonrealR).eq)
    (by simpa only [zero_mul] using actual_prefix_sourceProjection pR q.F k.val t (by omega))
  simpa only [mul_zero,zero_mul] using generated

theorem sourcePrincipalGaugeEuler_positive_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (mu : Fin 4) (a : Fin 12) (n : Fin 113) (t : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) (positive : 0<n.val) :
    sourcePrincipalEulerSector q pL pR left right n t (gaugeSlot mu a)=0:=by
  unfold sourcePrincipalEulerSector sourcePrincipalSector
  rw [map_sum]
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro j _
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro k _
  by_cases same : j.val+k.val=n.val
  · rw [if_pos same]
    exact sourcePrincipalGaugeBlock_positive_zero q pL pR left right mu a j k t nonrealL nonrealR (by omega)
  · rw [if_neg same,map_zero]

theorem sourcePrincipalGaugeHalf_positive_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (mu : Fin 4) (a : Fin 12) (lambda : ℂ) (n : Fin 113)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) (positive : 0<n.val) :
    sourcePrincipalHalf q pL pR left right lambda n (gaugeSlot mu a)=0:=by
  unfold sourcePrincipalHalf
  simp_rw [sourcePrincipalGaugeEuler_positive_zero q pL pR left right mu a n _ nonrealL nonrealR positive,mul_zero]
  exact integral_zero _ _

theorem sourceGaugeHalf_zeroHistory (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (mu : Fin 4) (a : Fin 12) (lambda : ℂ) (off : 0<lambda.re)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourcePoleCurrentHalf q pL pR left right lambda (gaugeSlot mu a)=
      sourcePrincipalHalf q pL pR left right lambda 0 (gaugeSlot mu a):=by
  rw [sourcePrincipalHalf_generated q pL pR left right lambda off]
  apply Finset.sum_eq_single 0
  · intro n _ different
    exact sourcePrincipalGaugeHalf_positive_zero q pL pR left right mu a lambda n nonrealL nonrealR (by
      have differentVal : n.val≠0:=fun h=>different (Fin.ext h)
      omega)
  · simp

end LowEnergy.PreparationVacuumPhysicalGradeZeroRead
