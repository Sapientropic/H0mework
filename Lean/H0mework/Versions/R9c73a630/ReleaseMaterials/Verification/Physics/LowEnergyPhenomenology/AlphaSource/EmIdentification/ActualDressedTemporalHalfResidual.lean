import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparationWardResidual

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedTemporalResidual
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
open ActualDressedTemporalHalf ActualDressedPreparationEnergy ActualDressedSourcePreparation
open PreparationVacuumSourcePreparedState PreparationVacuumPreparedCurrent
attribute [local irreducible] jointResolvent sourceHamiltonian noetherTimeInsertion noetherReader
  noetherBackgroundInitial temporalGaussInitial temporalGaussReader sourceInverse propagationPencil
  noetherNonlinearHalf temporalGaussHalf dressedEulerObserver


/-- These are the actual physical-action endpoints minus the two original preparation-action endpoints, on one operator event. -/
def physicalPreparationMismatch (event : DressedEvent) (transfer : PhysicalMomentum) : ResponseOp→L[ℂ]ℂ :=
  (dressedEulerObserver event).comp
      (ContinuousLinearMap.mul ℂ ResponseOp (sourceHamiltonian (event.momentum-transfer) event.frame))-
    preparationLeftObserver event-
    ((dressedEulerObserver event).comp
      ((ContinuousLinearMap.mul ℂ ResponseOp).flip (sourceHamiltonian event.momentum event.frame))-
        preparationRightObserver event)

theorem physical_preparation_return (event : DressedEvent) (transfer : PhysicalMomentum) (A : ResponseOp) :
    dressedEulerObserver event
      (sourceHamiltonian (event.momentum-transfer) event.frame*A-A*sourceHamiltonian event.momentum event.frame)=
      physicalPreparationMismatch event transfer A+preparationWardObserver event A :=by
  simp only [physicalPreparationMismatch,preparationWardObserver,sub_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply',ContinuousLinearMap.flip_apply,map_sub]
  abel

private theorem action_balance {A : Type*} [Ring A] [Module ℂ A]
    (lambda : ℂ) (V L R B : A)
    (paid : lambda • V+(-Complex.I) • (L*V)-(-Complex.I) • (V*R)=B) :
    lambda • V-B=Complex.I • (L*V-V*R) :=by
  rw [←paid]
  module

/-- The source inverse returns the original physical Hamiltonian endpoints, without identifying that Hamiltonian with the preparation operator. -/
theorem temporal_half_physical_action (q : PhysicalResponsePoint) (a : Fin 12) (lambda : ℂ)
    (positive : 0<lambda.re) :
    lambda • temporalGaussHalf q a lambda 0-temporalGaussInitial q a 0=
      Complex.I • (sourceHamiltonian (q.p+q.k) q.F*temporalGaussHalf q a lambda 0-
        temporalGaussHalf q a lambda 0*sourceHamiltonian q.p q.F) :=by
  have paid:=congrArg (fun T : SourcePropagationResolvent.TransferOp=>T (temporalGaussInitial q a 0))
    (sourceInverse_left q lambda positive)
  simp only [mul_apply_eq_comp,one_apply_eq_self,←temporal_gauss_half_inverse q a lambda positive,
    propagationPencil_actual,leftGenerator,rightGenerator,smul_mul_assoc,mul_smul_comm] at paid
  simpa only [sourceHamiltonian] using!
    action_balance lambda _ (jointGenerator (q.p+q.k) q.F 0 0) (jointGenerator q.p q.F 0 0) _ paid

private theorem observe_action {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (O : E→L[ℂ]ℂ) (lambda : ℂ) (V B Z : E) (paid : lambda • V-B=Complex.I • Z) :
    lambda*O V-O B=Complex.I*O Z := by
  simpa only [map_sub,map_smul,smul_eq_mul] using! congrArg O paid

private theorem remove_mismatch (a b m r : ℂ) (paid : a-b=Complex.I*(m+r)) :
    a-b-Complex.I*m=Complex.I*r := by linear_combination paid

/-- The actual halfline Ward contains a source-small two-endpoint residual and the explicit physical/preparation difference. -/
theorem temporal_half_preparation_return (event : DressedEvent) (transfer : PhysicalMomentum) (a : Fin 12)
    (lambda : ℂ) (positive : 0<lambda.re) :
    lambda*dressedNoetherHalfSource event transfer lambda 0 (gaugeSlot 0 a)-
      dressedEulerObserver event (temporalGaussInitial (dressedKinematicPoint event transfer) a 0)-
      Complex.I*physicalPreparationMismatch event transfer
        (temporalGaussHalf (dressedKinematicPoint event transfer) a lambda 0)=
      Complex.I*preparationWardObserver event
        (temporalGaussHalf (dressedKinematicPoint event transfer) a lambda 0) :=by
  have half:=temporal_actual_half_source event transfer a lambda positive 0
    (by simpa using temporal_frame_radius_positive event.frame)
    ((timeDomain_source_near (dressedKinematicPoint event transfer) lambda positive).self_of_nhds)
  rw [half]
  have paid:=observe_action (dressedEulerObserver event) lambda _ _ _
    (temporal_half_physical_action (dressedKinematicPoint event transfer) a lambda positive)
  have action :
      lambda*dressedEulerObserver event (temporalGaussHalf (dressedKinematicPoint event transfer) a lambda 0)-
        dressedEulerObserver event (temporalGaussInitial (dressedKinematicPoint event transfer) a 0)=
      Complex.I*dressedEulerObserver event
        (sourceHamiltonian (event.momentum-transfer) event.frame*
          temporalGaussHalf (dressedKinematicPoint event transfer) a lambda 0-
          temporalGaussHalf (dressedKinematicPoint event transfer) a lambda 0*
            sourceHamiltonian event.momentum event.frame) :=by
    simpa only [dressedKinematicPoint,sub_eq_add_neg] using! paid
  have transport:=congrArg (fun z : ℂ=>Complex.I*z)
    (physical_preparation_return event transfer (temporalGaussHalf (dressedKinematicPoint event transfer) a lambda 0))
  exact remove_mismatch _ _ _ _ (action.trans transport)

theorem temporal_half_preparation_price (event : DressedEvent) (transfer : PhysicalMomentum) (a : Fin 12)
    (lambda : ℂ) (positive : 0<lambda.re) :
    ‖lambda*dressedNoetherHalfSource event transfer lambda 0 (gaugeSlot 0 a)-
      dressedEulerObserver event (temporalGaussInitial (dressedKinematicPoint event transfer) a 0)-
      Complex.I*physicalPreparationMismatch event transfer
        (temporalGaussHalf (dressedKinematicPoint event transfer) a lambda 0)‖≤
      (2*(2*‖sourceLeg true 1 0‖+1))*event.epsilon*
        ‖temporalGaussHalf (dressedKinematicPoint event transfer) a lambda 0‖ :=by
  rw [temporal_half_preparation_return event transfer a lambda positive,norm_mul,Complex.norm_I,one_mul]
  exact ((preparationWardObserver event).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (preparation_ward_observer_price event) (norm_nonneg _))

theorem temporal_half_preparation_limit (event : DressedEvent) (transfer : PhysicalMomentum) (a : Fin 12)
    (lambda : ℂ) (positive : 0<lambda.re) :
    Tendsto (fun n : ℕ=>
      lambda*dressedNoetherHalfSource (preparationEventSequence event n) transfer lambda 0 (gaugeSlot 0 a)-
      dressedEulerObserver (preparationEventSequence event n)
        (temporalGaussInitial (dressedKinematicPoint (preparationEventSequence event n) transfer) a 0)-
      Complex.I*physicalPreparationMismatch (preparationEventSequence event n) transfer
        (temporalGaussHalf (dressedKinematicPoint (preparationEventSequence event n) transfer) a lambda 0)) atTop (𝓝 0) :=by
  have fixed (n : ℕ) : temporalGaussHalf (dressedKinematicPoint (preparationEventSequence event n) transfer) a lambda 0=
      temporalGaussHalf (dressedKinematicPoint event transfer) a lambda 0 :=by
    unfold temporalGaussHalf temporalGaussInitial physicalBackgroundMap dressedKinematicPoint preparationEventSequence
    rfl
  have evaluated:=((ContinuousLinearMap.apply ℂ ℂ
    (temporalGaussHalf (dressedKinematicPoint event transfer) a lambda 0)).continuous.tendsto
      (0 : ResponseOp→L[ℂ]ℂ)).comp (preparation_ward_observer_limit event)
  have generated : Tendsto (fun n : ℕ=>preparationWardObserver (preparationEventSequence event n)
      (temporalGaussHalf (dressedKinematicPoint event transfer) a lambda 0)) atTop (𝓝 (0:ℂ)) := by
    simpa only [ContinuousLinearMap.apply_apply,zero_apply] using! evaluated
  have multiplied : Tendsto (fun n : ℕ=>Complex.I*preparationWardObserver (preparationEventSequence event n)
      (temporalGaussHalf (dressedKinematicPoint event transfer) a lambda 0)) atTop (𝓝 (0:ℂ)) := by
    simpa only [mul_zero] using! generated.const_mul Complex.I
  apply Tendsto.congr' _ multiplied
  exact Filter.Eventually.of_forall (fun n=>
    ((temporal_half_preparation_return (preparationEventSequence event n) transfer a lambda positive).trans
      (congrArg (fun A : ResponseOp=>Complex.I*preparationWardObserver (preparationEventSequence event n) A)
        (fixed n))).symm)

end LowEnergy.GaussComposite.ActualDressedTemporalResidual
