import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMFullWard
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceFirstPoleGaugeReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMPoleWard
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing Stage9C.Material.SpinPair
open PreparationPhysicalNormalizedFullField PreparationPhysicalActualGaussChargeCurrent
open PreparationPhysicalNativePhaseChargeInventory PreparationPhysicalActualPhaseChargeReturn
open PreparationPhysicalActualNoetherVertexReturn
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalPhaseGaugeRealization
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open PreparationVacuumActionFieldLift CanonicalGradedCharge
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalPoleAmputation
open PreparationVacuumPhysicalFeedback
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open SourceQuantumFockGauge GaussFockLift GaussQuantumMultiplier GaussCoreHilbert
open SourceQuantumConfigurationHilbert GaussHistoryHilbert
open Electromagnetic.CanonicalCoframe Electromagnetic.CanonicalPacket
open SU7MotherLieAlgebra SU7MotherGaugeTheory SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction StageNineHolonomicField DiracExteriorMatterAction
open Stage10 Stage10.CanonicalMatter DiracCliffordRepresentation
open Stage10.HyperchargeResponse
open CanonicalGradedSpatialSource
open FullQuantum.CoframeResponse
open PreparationVacuumActualFieldQuantization
open GaussComposite.PhysicalEMVoltage
open GaussComposite.PhysicalEMGaugeRealization GaussComposite.PhysicalEMChargeReadout
open GaussComposite.PhysicalEMFieldCurrent GaussComposite.PhysicalEMFullWard
open scoped BigOperators Matrix
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

/-- `dEMLA` preserves negation on the embedded Lie block. -/
private theorem emla_neg (matrix : SU7MotherLieMatrix) :
    diracExteriorMotherLieAction (-matrix) =
      -diracExteriorMotherLieAction matrix := by
  rw [show (-matrix) = (-1:ℝ) • matrix from (neg_one_smul ℝ matrix).symm]
  rw [StageNineP286GaugeConnectionVariation.diracExteriorMotherLieAction_real_smul]
  push_cast
  module

/-- `dEMLA` preserves subtraction on the embedded Lie block. -/
private theorem emla_sub (first second : SU7MotherLieMatrix) :
    diracExteriorMotherLieAction (first - second) =
      diracExteriorMotherLieAction first - diracExteriorMotherLieAction second := by
  rw [sub_eq_add_neg,
    StageNineP286GaugeConnectionVariation.diracExteriorMotherLieAction_add, emla_neg]
  module

/-- The original phase gauge generator is the same generated root as the
    electromagnetic gauge action on the whole mother carrier. -/
theorem em_phase_gauge_action : sourcePhaseGaugeGenerator=emGaugeAction := by
  rw [sourcePhaseGaugeGenerator,sourceHyperchargeMother,emGaugeAction,emDirection,
    p286LieBlockEmbed_sub,p286LieBlockEmbed_neg,
    StageNineP286GaugeConnectionVariation.p286LieBlockEmbed_real_smul,
    emla_sub,emla_neg,
    StageNineP286GaugeConnectionVariation.diracExteriorMotherLieAction_real_smul]
  push_cast
  rfl

/-- The pole defect mother keeps the complete first-temporal difference. -/
def emPoleDefectMother : YangMills.FullPairing.Mother :=
  (-Complex.I) • sourceFirstTemporalDifference

/-- The actual first-pole temporal charge is the electromagnetic charge plus
    the retained pole difference on the whole mother carrier. -/
theorem em_pole_charge_full :
    sourceFirstTemporalCharge=Complex.I • emGaugeAction+emPoleDefectMother := by
  rw [sourceFirstTemporalCharge_full,sourcePhaseGaugeCharge,em_phase_gauge_action]
  rfl

/-- The full 504 pole charge matrix on the independent source branches. -/
def emPoleChargeMatrix : FullMatrix :=
  SourceRealScalarFock.branches (Quantum.operatorMatrix sourceFirstTemporalCharge)

/-- The full 504 pole defect matrix on the independent source branches. -/
def emPoleDefectMatrix : FullMatrix :=
  SourceRealScalarFock.branches (Quantum.operatorMatrix emPoleDefectMother)

/-- The pole Gauss charge on the whole source Hilbert space. -/
def emPoleCharge : H →L[ℂ] H :=
  GaussFockLift.lift (GaussQuantumMultiplier.quantized emPoleChargeMatrix)

/-- The pole defect charge on the whole source Hilbert space. -/
def emPoleDefectCharge : H →L[ℂ] H :=
  GaussFockLift.lift (GaussQuantumMultiplier.quantized emPoleDefectMatrix)

/-- The actual pole Gauss charge is the electromagnetic charge plus the
    retained pole defect charge on the whole Hilbert space. -/
theorem em_pole_gauss_full : emPoleCharge=emGaussCharge+emPoleDefectCharge := by
  have matrices : emPoleChargeMatrix=emGaugeChargeMatrix+emPoleDefectMatrix := by
    rw [emPoleChargeMatrix,emGaugeChargeMatrix,emPoleDefectMatrix,em_pole_charge_full,
      map_add]
    exact branchesLinear.map_add _ _
  rw [emPoleCharge,emGaussCharge,emPoleDefectCharge,matrices,←lift_add]
  congr 1
  exact map_add quantizer _ _

/-- The pole charge matrix is self-adjoint on the full independent branches:
    the source first-temporal weights are real. -/
theorem em_pole_matrix_hermitian :
    emPoleChargeMatrix.conjTranspose=emPoleChargeMatrix := by
  rw [emPoleChargeMatrix]
  unfold sourceFirstTemporalCharge
  rw [map_smul,sourceFirstTemporal_matrix]
  have diag : (-Complex.I) • Matrix.diagonal
      (fun i=>((sourceFirstWholeWeight i:ℚ):ℂ)*Complex.I)=
      Matrix.diagonal (fun i=>((sourceFirstWholeWeight i:ℚ):ℂ)):=by
    ext i j
    simp only [Matrix.smul_apply,Matrix.diagonal_apply,smul_eq_mul]
    by_cases h : i=j
    · subst j
      rw [if_pos rfl,if_pos rfl]
      calc -Complex.I*(↑(sourceFirstWholeWeight i)*Complex.I)
          =((-Complex.I)*Complex.I)*↑(sourceFirstWholeWeight i):=by ring
        _=↑(sourceFirstWholeWeight i):=by
          rw [neg_mul,Complex.I_mul_I,neg_neg,one_mul]
    · rw [if_neg h,if_neg h,mul_zero]
  rw [diag]
  ext i j
  rcases i with i|i <;> rcases j with j|j <;>
    simp [SourceRealScalarFock.branches,Matrix.conjTranspose_apply,
      Matrix.diagonal_apply,eq_comm]
  all_goals
    by_cases same : i=j
    · subst j
      simp
    · simp [same]

/-- The pole Gauss charge is self-adjoint on the full source Hilbert
    space. -/
theorem em_pole_pair (v w : H) :
    inner ℂ (emPoleCharge v) w=inner ℂ v (emPoleCharge w) := by
  apply GaussFockLift.lift_pair
  intro f g
  have generated := SourceQuantumFockGauge.quantizedFiber_adjoint
    emPoleChargeMatrix f g
  rw [em_pole_matrix_hermitian] at generated
  exact generated

/-- The pole defect charge is self-adjoint as the difference of the two
    self-adjoint charge operators. -/
private theorem emPoleDefect_pair (v w : H) :
    inner ℂ (emPoleDefectCharge v) w=inner ℂ v (emPoleDefectCharge w) := by
  have split : emPoleDefectCharge=emPoleCharge-emGaussCharge:=by
    rw [em_pole_gauss_full]
    abel
  rw [split]
  simp only [sub_apply,inner_sub_left,inner_sub_right]
  rw [em_pole_pair,em_gauss_pair]

/-- The pole charge matrix acts on the prepared charged coordinates by the
    actual source charge. -/
private theorem emPoleChargeMatrix_coordinates (side edge : Fin 2) :
    emPoleChargeMatrix*ᵥsourceChargedCoordinates side edge=
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedCoordinates side edge := by
  have primal := congrArg Quantum.coordinates
    (sourceFirstTemporalCharge_actualColumn side edge)
  rw [←Quantum.matrix_action,map_smul] at primal
  unfold emPoleChargeMatrix SourceRealScalarFock.branches sourceChargedCoordinates
  rw [Matrix.fromBlocks_mulVec]
  have left : (Sum.elim (Quantum.coordinates (sourceChargedRestriction side edge))
      (fun _ : Quantum.Index=>(0:ℂ))) ∘ Sum.inl=
      Quantum.coordinates (sourceChargedRestriction side edge) := rfl
  have right : (Sum.elim (Quantum.coordinates (sourceChargedRestriction side edge))
      (fun _ : Quantum.Index=>(0:ℂ))) ∘ Sum.inr=0 := rfl
  rw [left,right,Matrix.zero_mulVec,Matrix.zero_mulVec,Matrix.mulVec_zero,
    add_zero,zero_add,primal]
  funext i
  cases i with
  | inl i=>simp only [Sum.elim_inl,Pi.smul_apply]
  | inr i=>simp

/-- The quantized pole charge acts on the one-particle charged fiber by the
    actual source charge. -/
private theorem em_pole_fiber (side edge : Fin 2) :
    quantized emPoleChargeMatrix (sourceChargedFiber side edge)=
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedFiber side edge := by
  rw [sourceChargedFiber,quantized_oneParticle,emPoleChargeMatrix_coordinates]
  change fiberCoordinates.symm (Fermion.oneParticleLinear
    ((sourceActualPhaseCharge edge:ℂ) • sourceChargedCoordinates side edge))=_
  rw [map_smul,map_smul]
  rfl

/-- The actual pole Gauss charge returns the actual source charge on every
    prepared charged/neutral state. -/
theorem em_pole_gauss_prepared (epsilon : ℝ) (precision : 0<epsilon)
    (side edge : Fin 2) :
    emPoleCharge (sourceChargedGaussPrepared epsilon precision side edge)=
      (sourceActualPhaseCharge edge:ℂ) •
        sourceChargedGaussPrepared epsilon precision side edge := by
  apply GaussHalfDensity.fockHalfDensityEquiv.injective
  rw [map_smul]
  apply PiLp.ext
  intro word
  rw [show emPoleCharge=lift (quantized emPoleChargeMatrix) from rfl,
    sourceChargedGauss_action_coordinates,em_pole_fiber]
  simp only [PiLp.smul_apply,sourceChargedGaussPrepared_coordinates,smul_smul,smul_eq_mul]

/-- The pole difference is zero on the bare preparations; its insertion
    inside the full resolvents remains a separate response. -/
theorem em_pole_defect_prepared_zero (epsilon : ℝ) (precision : 0<epsilon)
    (side edge : Fin 2) :
    emPoleDefectCharge (sourceChargedGaussPrepared epsilon precision side edge)=0 := by
  have split : emPoleDefectCharge=emPoleCharge-emGaussCharge:=by
    rw [em_pole_gauss_full]
    abel
  rw [split,sub_apply,em_pole_gauss_prepared,em_gauss_prepared,sub_self]

/-- The absolute pole charge on the full source Hilbert space. -/
def emPoleAbsoluteCharge : H →L[ℂ] H :=
  (Stage10.ActionNormalization.phaseMomentum:ℂ) • emPoleCharge

/-- The absolute pole defect charge on the full source Hilbert space. -/
def emPoleAbsoluteDefect : H →L[ℂ] H :=
  (Stage10.ActionNormalization.phaseMomentum:ℂ) • emPoleDefectCharge

/-- The pole Noether vertex between the two actual resolvents. -/
def emPoleVertex (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) :
    H →L[ℂ] H :=
  jointResolvent pL q.F q.z 0*emPoleAbsoluteCharge*jointResolvent pR q.F q.w 0

/-- The full pole Noether response generated by the whole original joint
    generators on both legs. -/
def emPoleResponse (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) :
    H →L[ℂ] H :=
  jointResolvent pL q.F q.z 0*
    (jointGenerator pL q.F 0 0*emPoleAbsoluteCharge-
      emPoleAbsoluteCharge*jointGenerator pR q.F 0 0)*jointResolvent pR q.F q.w 0

/-- The pole defect vertex between the two actual resolvents. -/
def emPoleDefectVertex (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) :
    H →L[ℂ] H :=
  jointResolvent pL q.F q.z 0*emPoleAbsoluteDefect*jointResolvent pR q.F q.w 0

/-- The pole defect response on the same actual resolvent legs. -/
def emPoleDefectResponse (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) :
    H →L[ℂ] H :=
  jointResolvent pL q.F q.z 0*
    (jointGenerator pL q.F 0 0*emPoleAbsoluteDefect-
      emPoleAbsoluteDefect*jointGenerator pR q.F 0 0)*jointResolvent pR q.F q.w 0

/-- The pole vertex is the electromagnetic vertex plus the defect vertex on
    the same two actual resolvents. -/
theorem em_pole_vertex_full (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) :
    emPoleVertex q pL pR=emNoetherVertex q pL pR+emPoleDefectVertex q pL pR := by
  unfold emPoleVertex emNoetherVertex emPoleDefectVertex
  unfold emPoleAbsoluteCharge emAbsoluteCharge emPoleAbsoluteDefect
  rw [em_pole_gauss_full,smul_add]
  noncomm_ring

/-- The pole response decomposes into the electromagnetic and defect
    responses generated by the same whole joint generators. -/
theorem em_pole_response_full (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) :
    emPoleResponse q pL pR=emNoetherResponse q pL pR+emPoleDefectResponse q pL pR := by
  unfold emPoleResponse emNoetherResponse emPoleDefectResponse
  unfold emPoleAbsoluteCharge emAbsoluteCharge emPoleAbsoluteDefect
  rw [em_pole_gauss_full,smul_add]
  simp only [sub_eq_add_neg,neg_add,mul_add,add_mul]
  noncomm_ring

/-- The inverse-Ward algebra with both actual material inverses retained. -/
private theorem em_pole_inverse_ward {R : Type*} [Ring R] [Algebra ℂ R]
    (CLeft CRight invLeft invRight Q : R) (z w : ℂ)
    (left : invLeft*(CLeft-z • 1)=1) (right : (CRight-w • 1)*invRight=1) :
    (z-w) • (invLeft*Q*invRight)=
      invLeft*Q-Q*invRight+invLeft*(CLeft*Q-Q*CRight)*invRight := by
  have l : invLeft*CLeft=1+z • invLeft := by
    have h:=left
    rw [mul_sub,mul_smul_comm,mul_one] at h
    exact sub_eq_iff_eq_add.mp h
  have r : CRight*invRight=1+w • invRight := by
    have h:=right
    rw [sub_mul,smul_mul_assoc,one_mul] at h
    exact sub_eq_iff_eq_add.mp h
  have generated : invLeft*(CLeft*Q-Q*CRight)*invRight=
      Q*invRight-invLeft*Q+(z-w) • (invLeft*Q*invRight) := by
    calc
      _=(invLeft*CLeft)*Q*invRight-invLeft*Q*(CRight*invRight) := by noncomm_ring
      _=(1+z • invLeft)*Q*invRight-invLeft*Q*(1+w • invRight) := by rw [l,r]
      _=_ := by
        simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,sub_smul]
        abel
  rw [generated]
  abel

/-- The pole defect full-resolvent Ward identity inside the same actual
    resolvents: the retained difference is transported, not dropped. -/
theorem em_pole_defect_ward (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    (q.z-q.w) • emPoleDefectVertex q pL pR=
      jointResolvent pL q.F q.z 0*emPoleAbsoluteDefect-
        emPoleAbsoluteDefect*jointResolvent pR q.F q.w 0+
          emPoleDefectResponse q pL pR := by
  exact em_pole_inverse_ward _ _ _ _ _ _ _
    (sourceMaterialInverse_left pL q.F q.z left)
    (sourceMaterialInverse_right pR q.F q.w right)

/-- The full pole Ward identity: the actual first-pole temporal charge in
    both legs, with the defect retained inside the response. -/
theorem em_pole_full_ward (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    (q.z-q.w) • emPoleVertex q pL pR=
      jointResolvent pL q.F q.z 0*emPoleAbsoluteCharge-
        emPoleAbsoluteCharge*jointResolvent pR q.F q.w 0+
          emPoleResponse q pL pR := by
  exact em_pole_inverse_ward _ _ _ _ _ _ _
    (sourceMaterialInverse_left pL q.F q.z left)
    (sourceMaterialInverse_right pR q.F q.w right)

/-- The pole charge on the two prepared ends, inside the actual source
    quantum readout. -/
private theorem emPolePreparedCharge_ends (q : PhysicalResponsePoint)
    (sL eL sR eR : Fin 2) (A : H →L[ℂ] H) :
    sourceQuantumChargedRead q sL eL sR eR (emPoleAbsoluteCharge*A)=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eL:ℂ)*
        sourceQuantumChargedRead q sL eL sR eR A ∧
    sourceQuantumChargedRead q sL eL sR eR (A*emPoleAbsoluteCharge)=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eR:ℂ)*
        sourceQuantumChargedRead q sL eL sR eR A := by
  simp only [sourceQuantumChargedRead,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply,innerSL_apply_apply,mul_apply_eq_comp,
    emPoleAbsoluteCharge]
  constructor
  · rw [smul_apply,inner_smul_right]
    rw [←em_pole_pair,em_pole_gauss_prepared,inner_smul_left]
    rw [starRingEnd_apply]
    have realq : star (↑(sourceActualPhaseCharge eL):ℂ)=
        ↑(sourceActualPhaseCharge eL):=by simp
    rw [realq]
    ring
  · rw [smul_apply,map_smul,em_pole_gauss_prepared,map_smul,smul_smul,inner_smul_right]

/-- The prepared defect contribution vanishes at the bare endpoints: the
    pole Ward returns exactly the defect response on the actual four
    columns. -/
theorem em_pole_prepared_defect_return (q : PhysicalResponsePoint)
    (pL pR : PhysicalMomentum) (sL eL sR eR : Fin 2)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    (q.z-q.w)*sourceQuantumChargedRead q sL eL sR eR (emPoleDefectVertex q pL pR)=
      sourceQuantumChargedRead q sL eL sR eR (emPoleDefectResponse q pL pR) := by
  have ends : ∀ (A : H →L[ℂ] H),
      sourceQuantumChargedRead q sL eL sR eR (emPoleAbsoluteDefect*A)=0 ∧
      sourceQuantumChargedRead q sL eL sR eR (A*emPoleAbsoluteDefect)=0 := by
    intro A
    simp only [sourceQuantumChargedRead,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply,innerSL_apply_apply,mul_apply_eq_comp,
      emPoleAbsoluteDefect]
    constructor
    · rw [smul_apply,inner_smul_right,←emPoleDefect_pair,
        em_pole_defect_prepared_zero,inner_zero_left]
      ring
    · rw [smul_apply,map_smul,em_pole_defect_prepared_zero]
      simp
  have generated:=congrArg (sourceQuantumChargedRead q sL eL sR eR)
    (em_pole_defect_ward q pL pR left right)
  simp only [map_smul,smul_eq_mul,map_add,map_sub,
    (ends _).1,(ends _).2] at generated
  convert generated using 1
  abel

/-- The scalar actual-source charged readout of the pole full Ward identity
    on all four bilateral charged/neutral combinations. -/
theorem em_pole_prepared_full_ward (q : PhysicalResponsePoint)
    (pL pR : PhysicalMomentum) (sL eL sR eR : Fin 2)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    (q.z-q.w)*sourceQuantumChargedRead q sL eL sR eR (emPoleVertex q pL pR)=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eR:ℂ)*
        sourceQuantumChargedRead q sL eL sR eR (jointResolvent pL q.F q.z 0)-
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eL:ℂ)*
        sourceQuantumChargedRead q sL eL sR eR (jointResolvent pR q.F q.w 0)+
      sourceQuantumChargedRead q sL eL sR eR
        (emNoetherResponse q pL pR+emPoleDefectResponse q pL pR) := by
  have generated:=congrArg (sourceQuantumChargedRead q sL eL sR eR)
    (em_pole_full_ward q pL pR left right)
  rw [em_pole_response_full] at generated
  simp only [map_smul,smul_eq_mul,map_add,map_sub,
    (emPolePreparedCharge_ends q sL eL sR eR _).1,
    (emPolePreparedCharge_ends q sL eL sR eR _).2] at generated
  rw [map_add (sourceQuantumChargedRead q sL eL sR eR)]
  exact generated

/-- Rest-index agreement on the actual four columns is exactly index
    equality. -/
private theorem pole_rest_index_eq (i j : ActualPreparedIndex) :
    (sourceChargedRestIndex i.1 i.2=sourceChargedRestIndex j.1 j.2)↔i=j := by
  rcases i with ⟨a,b⟩
  rcases j with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

/-- The physical pole temporal energy is exactly the negative electromagnetic
    voltage energy on the actual generated source state. -/
theorem em_pole_temporal_voltage (epsilon : ℝ) (precision : 0<epsilon)
    (p : PhysicalMomentum) (i j : ActualPreparedIndex) :
    sourceFirstEnergyFour epsilon precision p (Pi.single 0 1) i j=
      -emVoltageEnergy epsilon precision p (sourceState sourcePoint.val)
        i.1 i.2 j.1 j.2 := by
  rw [sourceFirstEnergyFour_value]
  rw [em_voltage_energy_read epsilon precision p (sourceState sourcePoint.val)
    (sourceState_valid sourcePoint)]
  simp only [Matrix.diagonal_apply,sourceFirstPreparedCoefficient,Pi.single_eq_same,
    Pi.single_eq_of_ne (show (3:Fin 4)≠0 by decide),one_mul,mul_zero,
    neg_mul,neg_neg]
  by_cases same : i=j
  · subst j
    simp
  · have diff : sourceChargedRestIndex i.1 i.2≠sourceChargedRestIndex j.1 j.2:=by
      intro h
      exact same ((pole_rest_index_eq i j).mp h)
    simp [same,diff]

end LowEnergy.GaussComposite.PhysicalEMPoleWard
