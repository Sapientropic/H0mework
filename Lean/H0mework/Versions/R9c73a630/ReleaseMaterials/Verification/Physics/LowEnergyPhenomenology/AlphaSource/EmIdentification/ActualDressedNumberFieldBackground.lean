import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberFieldTime

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberField
open GaussCoreHilbert GaussCoreDifferential CanonicalGradedSpatialSource
open PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open PreparationVacuumUncutYukawa PreparationVacuumPhysicalNumberOneRead PreparationVacuumPhysicalN1WardCollapse
open GaussCoreLabel GaussYukawaCoefficient GaussYukawaGrade GaussNativePotential PreparationVacuumFieldConstraintResponse
open CanonicalGradedCurrent GaussComposite.SourceGraph
open CanonicalGradedSpatial (Localizer)
open ActualDressedNumberZero
open Filter
open scoped Topology
attribute [local irreducible] sourceProjection sourceExcitedProjection sourceN1Projection jointCompression jointY jointGenerator jointResolvent jointCResolvent physicalTime

set_option backward.isDefEq.respectTransparency false in
private theorem uncutOperator_N1G0_range (f : Field289) (phi : CanonicalGradedSpatial.Localizer) (r : ℝ) :
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
private theorem uncutOperator_N1G1_zero (f : Field289) (phi : CanonicalGradedSpatial.Localizer) (r : ℝ) :
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


theorem actual_joint_Y_N1G0_range (h : Field289) (phi : CanonicalGradedSpatial.Localizer) :
    sourceExcitedProjection*jointY phi h*sourceProjection=jointY phi h*sourceProjection := by
  rw [jointY_source]
  exact uncutOperator_N1G0_range h phi 1

theorem actual_joint_Y_N1G1_zero (h : Field289) (phi : CanonicalGradedSpatial.Localizer) : jointY phi h*sourceExcitedProjection=0 := by
  rw [jointY_source]
  exact uncutOperator_N1G1_zero h phi 1

theorem actual_joint_C_number_one (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) :
    Commute sourceN1Projection (jointCompression p F h) := by
  simpa only [sourceN1Projection,sourceProjection,sourceExcitedProjection] using
    (actual_joint_compression_blocks p F h CanonicalGradedCurrent.sourceLabel).add_left
      (actual_joint_compression_blocks p F h sourceExcitedLabel)

private theorem two_range {R : Type*} [Ring R] (P Q A : R) (left : P*A=0) (right : A*Q=0)
    (range : Q*A*P=A*P) : (P+Q)*A*(P+Q)=A*(P+Q) := by
  simp only [mul_add,add_mul,left,zero_add,range,right,add_zero]
  rw [mul_assoc Q A Q,right,mul_zero,add_zero]

theorem actual_joint_Y_number_one (h : Field289) (phi : CanonicalGradedSpatial.Localizer) :
    sourceN1Projection*jointY phi h*sourceN1Projection=jointY phi h*sourceN1Projection := by
  have left : sourceProjection*jointY phi h=0 :=
    positive_grade_left_zero _ 1 (by simpa only [Nat.cast_one,one_smul] using actual_joint_Y_raises h phi) (by omega)
  simpa only [sourceN1Projection] using two_range sourceProjection sourceExcitedProjection (jointY phi h)
    left (actual_joint_Y_N1G1_zero h phi) (actual_joint_Y_N1G0_range h phi)

private theorem shifted_range {R : Type*} [Ring R] [Algebra ℂ R] (P C A : R) (z : ℂ)
    (idem : P*P=P) (blocks : Commute P C) (range : P*A*P=A*P) : P*(C+A-z • 1)*P=(C+A-z • 1)*P := by
  have c : P*C*P=C*P := by rw [blocks.eq,mul_assoc,idem]
  have scalar : P*(z • (1:R))*P=(z • (1:R))*P := by
    simp only [mul_smul_comm,smul_mul_assoc,mul_one,one_mul,idem]
  simp only [mul_sub,sub_mul,mul_add,add_mul,c,range,scalar]

theorem actual_joint_generator_number_one (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (h : Field289) : sourceN1Projection*jointGenerator p F z h*sourceN1Projection=
      jointGenerator p F z h*sourceN1Projection := by
  unfold jointGenerator
  exact shifted_range _ _ _ z sourceN1Projection_idempotent (actual_joint_C_number_one p F h)
    (actual_joint_Y_number_one h (PreparationVacuumYukawaTransport.finiteRetainer p F))

local instance backgroundReal : NormedAlgebra ℝ ActualDressedNumberZero.Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance backgroundRational : NormedAlgebra ℚ ActualDressedNumberZero.Op:=NormedAlgebra.restrictScalars ℚ ℂ _

private theorem exp_range {B : Type*} [NormedRing B] [NormedAlgebra ℚ B] [CompleteSpace B]
    (P X : B) (idem : P*P=P) (range : P*X*P=X*P) : P*NormedSpace.exp X*P=NormedSpace.exp X*P := by
  have source : SemiconjBy P (P*X*P) X := by
    change P*(P*X*P)=X*P
    calc
      _=(P*P)*X*P := by noncomm_ring
      _=P*X*P := by rw [idem]
      _=X*P := range
  have generated:=source.exp_right.eq
  calc
    _=P*(NormedSpace.exp X*P) := by rw [mul_assoc]
    _=P*(P*NormedSpace.exp (P*X*P)) := by rw [←generated]
    _=(P*P)*NormedSpace.exp (P*X*P) := (mul_assoc P P _).symm
    _=P*NormedSpace.exp (P*X*P) := by rw [idem]
    _=NormedSpace.exp X*P := generated

private theorem scalar_range {B : Type*} [Ring B] [Algebra ℂ B] [Algebra ℝ B]
    (P X : B) (c : ℂ) (t : ℝ) (range : P*X*P=X*P) : P*(t • (c • X))*P=(t • (c • X))*P := by
  simp only [mul_smul_comm,smul_mul_assoc]
  exact congrArg (fun Y : B=>t • (c • Y)) range

theorem actual_joint_time_number_one_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (t : ℝ) (h : Field289) : sourceN1Projection*physicalTime p F t h*sourceN1Projection=
      physicalTime p F t h*sourceN1Projection := by
  unfold physicalTime SourceFiniteUnitary.time
  apply exp_range _ _ sourceN1Projection_idempotent
  exact scalar_range (B:=ActualDressedNumberZero.Op) _ _ (-Complex.I) t
    (actual_joint_generator_number_one p F 0 h)

theorem actual_joint_time_background_number_one (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (t : ℝ) (h : Field289) (profile : Profile) : sourceN1Projection (physicalTime p F t h (prepared profile))=
      physicalTime p F t h (prepared profile) := by
  have source:=congrArg (fun A : ActualDressedNumberZero.Op=>A (prepared profile))
    (actual_joint_time_number_one_range p F t h)
  simpa only [mul_apply_eq_comp,actual_background_number_one] using source

private theorem inverse_preserves_one (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (h : Field289) (P : ActualDressedNumberZero.Op) (blocks : Commute P (jointCompression p F h))
    (free : IsUnit (jointCompression p F h-z • (1:ActualDressedNumberZero.Op))) :
    Commute P (jointCResolvent p F z h) := by
  unfold jointCResolvent
  exact PreparationVacuumYukawaTransport.inverse_commuting _ _ free
    (blocks.sub_right ((Commute.one_right _).smul_right z))

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

private theorem two_step_terminal {R : Type*} [Ring R] (P Q B : R)
    (range : Q*B*P=B*P) (terminal : B*Q=0) : B*B*(P+Q)=0 := by
  have base_zero : B*B*P=0 := by
    calc
      _=B*(B*P) := by rw [mul_assoc]
      _=B*(Q*B*P) := by rw [range]
      _=(B*Q)*B*P := by noncomm_ring
      _=0 := by rw [terminal,zero_mul,zero_mul]
  rw [mul_add,base_zero,mul_assoc B B Q,terminal,mul_zero,add_zero]

/-- The same original N1 background has its own two Green words on the full field neighbourhood. -/
def jointN1GreenWords (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) (h : Field289) : ActualDressedNumberZero.Op :=
  let U:=jointCResolvent p F z h
  let A:=jointY (PreparationVacuumYukawaTransport.finiteRetainer p F) h
  U-U*A*U

theorem actual_joint_N1_resolvent_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) : ∀ᶠh : Field289 in 𝓝 0,jointResolvent p F z h*sourceN1Projection=
      jointN1GreenWords p F z h*sourceN1Projection := by
  filter_upwards [actual_joint_free_units_near_zero p F z nonreal,actual_joint_full_units_near_zero p F z nonreal]
    with h free full
  let U:=jointCResolvent p F z h
  let A:=jointY (PreparationVacuumYukawaTransport.finiteRetainer p F) h
  let B:=A*U
  have base : Commute sourceProjection (jointCompression p F h) := by
    simpa only [sourceProjection] using actual_joint_compression_blocks p F h CanonicalGradedCurrent.sourceLabel
  have excited : Commute sourceExcitedProjection (jointCompression p F h) := by
    simpa only [sourceExcitedProjection] using actual_joint_compression_blocks p F h sourceExcitedLabel
  have range : sourceExcitedProjection*B*sourceProjection=B*sourceProjection :=
    inverse_one_range _ _ _ _ (inverse_preserves_one p F z h _ base free)
      (actual_joint_Y_N1G0_range h (PreparationVacuumYukawaTransport.finiteRetainer p F))
  have terminal : B*sourceExcitedProjection=0 :=
    inverse_one_terminal _ _ _ (inverse_preserves_one p F z h _ excited free)
      (actual_joint_Y_N1G1_zero h (PreparationVacuumYukawaTransport.finiteRetainer p F))
  have generated : A*U*A*U*sourceN1Projection=0 := by
    have original:=two_step_terminal sourceProjection sourceExcitedProjection B range terminal
    simpa only [B,sourceN1Projection,mul_assoc] using original
  have free_inverse : (jointCompression p F h-z • (1:ActualDressedNumberZero.Op))*U=1 := by
    unfold U jointCResolvent
    exact Ring.mul_inverse_cancel _ free
  have full_inverse : jointResolvent p F z h*((jointCompression p F h-z • (1:ActualDressedNumberZero.Op))+A)=1 := by
    have original:=Ring.inverse_mul_cancel _ full
    simpa only [A,jointGenerator,jointResolvent,sub_add_eq_add_sub] using original
  simpa only [jointN1GreenWords] using inverse_two_return sourceN1Projection
    (jointCompression p F h-z • (1:ActualDressedNumberZero.Op)) A U (jointResolvent p F z h) free_inverse full_inverse generated

theorem actual_joint_background_inverse_time_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (profile : Profile) : ∀ᶠh : Field289 in 𝓝 0,∀t : ℝ,
    jointResolvent p F z h (physicalTime p F t h (prepared profile))=
      jointN1GreenWords p F z h (physicalTime p F t h (prepared profile)) := by
  filter_upwards [actual_joint_N1_resolvent_return p F z nonreal] with h source
  intro t
  have returned:=congrArg (fun A : ActualDressedNumberZero.Op=>A (physicalTime p F t h (prepared profile))) source
  simpa only [mul_apply_eq_comp,actual_joint_time_background_number_one] using returned

end LowEnergy.GaussComposite.ActualDressedNumberField
