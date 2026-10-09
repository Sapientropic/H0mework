import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalPolarization

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedTemporalHalf
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField
open CanonicalGradedSpatialSource GaussCoreHilbert GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumGaugeSourceInjection
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalHalfAxis PreparationVacuumPropagationPencil
open PreparationVacuumTemporalCharge PreparationVacuumSourceChargeWard PreparationVacuumNoetherChart
open PreparationVacuumRawJointFeedback PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumWeightedChargeActionWard PreparationVacuumFieldConstraintResponse
open SourcePropagationResolvent SourcePropagationFieldFeedback SourcePropagationNearFieldTime
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedSylvester
open ActualDressedNonlinearHalf ActualDressedStaticResponse
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
local instance : NormedAlgebra ℝ ResponseOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : ContinuousENorm SourcePropagationResolvent.TransferOp :=by
  convert! (SeminormedAddGroup.toContinuousENorm (E:=SourcePropagationResolvent.TransferOp)) using 1
attribute [local irreducible] jointResolvent sourceHamiltonian noetherTimeInsertion noetherReader
  noetherBackgroundInitial temporalGaussInitial temporalGaussReader sourceInverse propagationPencil
  noetherNonlinearHalf temporalGaussHalf dressedEulerObserver

/-- The halfline Ward insertion keeps the same left and right material preparation operators. -/
def temporalGaussWardInitial (q : PhysicalResponsePoint) (a : Fin 12) : ResponseOp :=
  jointResolvent (q.p+q.k) q.F q.z 0*noetherTimeInsertion q (temporalField a)*
    jointResolvent q.p q.F q.w 0

theorem temporal_gauss_ward_action (q : PhysicalResponsePoint) (a : Fin 12) (x : H) :
    temporalGaussWardInitial q a x=
      jointResolvent (q.p+q.k) q.F q.z 0
        (sourceApprox q.F (embed (weightedWardCore q.p q.k a
          (sourceTestApprox q.F (jointResolvent q.p q.F q.w 0 x))))+
        leftCompressionDefect (q.p+q.k) q.F (rawChargeCore a
          (sourceTestApprox q.F (jointResolvent q.p q.F q.w 0 x)))+
        leftUncutDefect (q.p+q.k) q.F (rawChargeCore a
          (sourceTestApprox q.F (jointResolvent q.p q.F q.w 0 x)))-
        sourceApprox q.F (embed (rawChargeCore a
          (rightCompressionDefect q.p q.F (jointResolvent q.p q.F q.w 0 x)+
            rightUncutDefect q.p q.F (jointResolvent q.p q.F q.w 0 x))))) :=by
  unfold temporalGaussWardInitial
  simp only [mul_apply_eq_comp,temporalInsertion_action_return]

private theorem temporal_raw_initial (q : PhysicalResponsePoint) (a : Fin 12) :
    rawInitial q (temporalField a)=temporalGaussInitial q a 0 :=
  (noether_background_initial_source q (temporalField a)).symm.trans
    (temporal_gauss_initial_generated q a 0 (by simpa using temporal_frame_radius_positive q.F))

theorem temporal_gauss_half_inverse (q : PhysicalResponsePoint) (a : Fin 12) (lambda : ℂ)
    (positive : 0<lambda.re) :
    temporalGaussHalf q a lambda 0=sourceInverse q lambda (temporalGaussInitial q a 0) :=by
  calc
    _=noetherNonlinearHalf q (temporalField a) lambda 0 :=
      (temporal_gauss_half_generated q a lambda 0 (by simpa using temporal_frame_radius_positive q.F)).symm
    _=noetherBackgroundOperator q (temporalField a) lambda 0 :=
      (noether_nonlinear_half_background q (temporalField a) lambda positive).self_of_nhds
    _=rawHalf q (temporalField a) lambda :=noether_background_operator_source q (temporalField a) lambda positive
    _=sourceInverse q lambda (rawInitial q (temporalField a)) :=rawHalf_true_inverse q (temporalField a) lambda positive
    _=_ :=congrArg (sourceInverse q lambda) (temporal_raw_initial q a)

private theorem bracket_slide {A : Type*} [Ring A] (L J R H K : A)
    (LH : L*H=H*L) (RK : R*K=K*R) :
    H*(L*J*R)-(L*J*R)*K=L*(H*J-J*K)*R :=by
  have first : H*(L*J*R)=L*(H*J)*R :=by
    calc
      _=(H*L)*J*R:=by simp only [mul_assoc]
      _=(L*H)*J*R:=by rw [LH]
      _=_:=by simp only [mul_assoc]
  have second : (L*J*R)*K=L*(J*K)*R :=by
    calc
      _=L*J*(R*K):=by simp only [mul_assoc]
      _=L*J*(K*R):=by rw [RK]
      _=_:=by simp only [mul_assoc]
  rw [first,second,mul_sub,sub_mul]

private theorem scalar_bracket {A : Type*} [AddCommGroup A] [Module ℂ A] (X Y Z : A) :
    X-(X+(-Complex.I) • Y-(-Complex.I) • Z)=Complex.I • (Y-Z) :=by
  simp only [neg_smul,smul_sub]
  abel

private theorem temporal_initial_ward (q : PhysicalResponsePoint) (a : Fin 12) (lambda : ℂ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    lambda • temporalGaussInitial q a 0-propagationPencil q lambda (temporalGaussInitial q a 0)=
      Complex.I • temporalGaussWardInitial q a :=by
  rw [←temporal_raw_initial q a,propagationPencil_actual]
  have raw : rawReader (temporalField a) q.p q.F 0=noetherReader (temporalField a) q.p q.F 0 :=
    (noetherReader_source (temporalField a) q.p q.F).symm
  have algebra:=bracket_slide (jointResolvent (q.p+q.k) q.F q.z 0)
    (noetherReader (temporalField a) q.p q.F 0) (jointResolvent q.p q.F q.w 0)
    (sourceHamiltonian (q.p+q.k) q.F) (sourceHamiltonian q.p q.F)
    (sourceResolvent_commutes (q.p+q.k) q.F q.z hz) (sourceResolvent_commutes q.p q.F q.w hw)
  simp only [sourceHamiltonian] at algebra
  simp only [leftGenerator,rightGenerator,rawInitial,raw,smul_mul_assoc,mul_smul_comm]
  have source := scalar_bracket
    (lambda • (jointResolvent (q.p+q.k) q.F q.z 0*noetherReader (temporalField a) q.p q.F 0*
      jointResolvent q.p q.F q.w 0))
    (jointGenerator (q.p+q.k) q.F 0 0*(jointResolvent (q.p+q.k) q.F q.z 0*
      noetherReader (temporalField a) q.p q.F 0*jointResolvent q.p q.F q.w 0))
    (jointResolvent (q.p+q.k) q.F q.z 0*noetherReader (temporalField a) q.p q.F 0*
      jointResolvent q.p q.F q.w 0*jointGenerator q.p q.F 0 0)
  have paid:=source.trans (congrArg (fun A : ResponseOp=>Complex.I • A) algebra)
  simpa only [temporalGaussWardInitial,noetherTimeInsertion,sourceHamiltonian] using! paid

/-- The exact nonzero Ward responsibility is the source weighted action insertion plus its four original defects. -/
theorem temporal_gauss_half_ward (q : PhysicalResponsePoint) (a : Fin 12) (lambda : ℂ)
    (positive : 0<lambda.re) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    lambda • temporalGaussHalf q a lambda 0-temporalGaussInitial q a 0=
      Complex.I • sourceInverse q lambda (temporalGaussWardInitial q a) :=by
  have paid:=congrArg (sourceInverse q lambda) (temporal_initial_ward q a lambda hz hw)
  have cancel:=congrArg (fun T : SourcePropagationResolvent.TransferOp=>T (temporalGaussInitial q a 0))
    (sourceInverse_right q lambda positive)
  simp only [mul_apply_eq_comp,one_apply_eq_self] at cancel
  simpa only [map_sub,map_smul,cancel,←temporal_gauss_half_inverse q a lambda positive] using! paid

/-- The Ward right-hand side is itself the original physical two-time Bochner halfline. -/
theorem temporal_gauss_ward_integral (q : PhysicalResponsePoint) (a : Fin 12) (lambda : ℂ)
    (positive : 0<lambda.re) :
    sourceInverse q lambda (temporalGaussWardInitial q a)=
      ∫t in Ioi (0:ℝ),laplaceWeight lambda t • physicalBackgroundMap q 0 t (temporalGaussWardInitial q a) :=by
  have generated:=ContinuousLinearMap.integral_apply (sourceInverse_integrable q lambda positive)
    (temporalGaussWardInitial q a)
  simpa only [sourceInverse,physicalBackgroundMap_base,smul_apply] using! generated

/-- Actual creation-minus-background reads the genuine halfline Ward, with its material initial endpoint intact. -/
theorem temporal_actual_half_ward (event : DressedEvent) (transfer : PhysicalMomentum) (a : Fin 12)
    (lambda : ℂ) (positive : 0<lambda.re) :
    lambda*dressedNoetherHalfSource event transfer lambda 0 (gaugeSlot 0 a)-
      dressedEulerObserver event (temporalGaussInitial (dressedKinematicPoint event transfer) a 0)=
        Complex.I*dressedEulerObserver event
          (sourceInverse (dressedKinematicPoint event transfer) lambda
            (temporalGaussWardInitial (dressedKinematicPoint event transfer) a)) :=by
  have actual:=temporal_actual_half_source event transfer a lambda positive 0
    (by simpa using temporal_frame_radius_positive event.frame)
    ((timeDomain_source_near (dressedKinematicPoint event transfer) lambda positive).self_of_nhds)
  rw [actual]
  have paid:=congrArg (dressedEulerObserver event)
    (temporal_gauss_half_ward (dressedKinematicPoint event transfer) a lambda positive event.nonreal event.nonreal)
  simpa only [map_sub,map_smul,smul_eq_mul] using! paid

end LowEnergy.GaussComposite.ActualDressedTemporalHalf
