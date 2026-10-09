import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalHalfResidual

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedTemporalResidual
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumGaugeSourceInjection
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalHalfAxis PreparationVacuumPropagationPencil
open PreparationVacuumNoetherChart PreparationVacuumRawJointFeedback PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumPreparedCurrent SourcePropagationResolvent SourcePropagationNearFieldTime
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedSylvester
open ActualDressedNonlinearHalf ActualDressedStaticResponse ActualDressedTemporalHalf
open ActualDressedTemporalNormalization
open PreparationVacuumTemporalCharge PreparationVacuumSourceChargeWard
open ActualDressedPreparationEnergy
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
local instance : NormedAlgebra ℝ ResponseOp:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] temporalGaussHalfJet temporalGaussHalf temporalGaussInitialJet
  jointCurrent jointGenerator sourceHamiltonian leftCurrent rightCurrent sourceInverse propagationPencil
  physicalPreparationMismatch preparationWardObserver dressedEulerObserver staticQuantumCorrection

/-- The actual current derivatives act on both original time legs. -/
def temporalPhysicalDrive (q : PhysicalResponsePoint) (a : Fin 12) (force : Field289) (lambda : ℂ) : ResponseOp :=
  jointCurrent (q.p+q.k) q.F 0 0 force*temporalGaussHalf q a lambda 0-
    temporalGaussHalf q a lambda 0*jointCurrent q.p q.F 0 0 force

attribute [local irreducible] temporalPhysicalDrive

private theorem driven_balance {E : Type*} [AddCommGroup E] [Module ℂ E]
    (lambda : ℂ) (X B L R JL JR : E)
    (paid : lambda • X+(-Complex.I) • L-(-Complex.I) • R=B-(-Complex.I) • JL+(-Complex.I) • JR) :
    lambda • X-B-Complex.I • (JL-JR)=Complex.I • (L-R) := by
  calc
    _ = (lambda • X+(-Complex.I) • L-(-Complex.I) • R)-B-
        Complex.I • (JL-JR)-(-Complex.I) • L+(-Complex.I) • R := by module
    _ = (B-(-Complex.I) • JL+(-Complex.I) • JR)-B-
        Complex.I • (JL-JR)-(-Complex.I) • L+(-Complex.I) • R := by rw [paid]
    _ = _ := by module

/-- The full half-current derivative returns its preparation jet, both driven legs and physical Hamiltonian endpoints. -/
theorem temporal_quantum_physical_action (q : PhysicalResponsePoint) (a : Fin 12) (force : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) :
    lambda • temporalGaussHalfJet q a force lambda-temporalGaussInitialJet q a force-
      Complex.I • temporalPhysicalDrive q a force lambda=
      Complex.I • (sourceHamiltonian (q.p+q.k) q.F*temporalGaussHalfJet q a force lambda-
        temporalGaussHalfJet q a force lambda*sourceHamiltonian q.p q.F) := by
  have paid:=noether_static_half_pencil q (temporalField a) force lambda positive
  have initial : rawHalf q (temporalField a) lambda=temporalGaussHalf q a lambda 0 :=
    (rawHalf_true_inverse q (temporalField a) lambda positive).trans
      ((congrArg (sourceInverse q lambda)
        ((noether_background_initial_source q (temporalField a)).symm.trans
          (temporal_gauss_initial_generated q a 0 (by simpa using temporal_frame_radius_positive q.F)))).trans
            (temporal_gauss_half_inverse q a lambda positive).symm)
  have normalized :
      lambda • temporalGaussHalfJet q a force lambda+
        (-Complex.I) • (jointGenerator (q.p+q.k) q.F 0 0*temporalGaussHalfJet q a force lambda)-
        (-Complex.I) • (temporalGaussHalfJet q a force lambda*jointGenerator q.p q.F 0 0)=
      temporalGaussInitialJet q a force-
        (-Complex.I) • (jointCurrent (q.p+q.k) q.F 0 0 force*temporalGaussHalf q a lambda 0)+
        (-Complex.I) • (temporalGaussHalf q a lambda 0*jointCurrent q.p q.F 0 0 force) := by
    simpa only [temporal_gauss_half_jet q a force lambda positive,temporal_gauss_initial_jet q a force,
      initial,propagationPencil_actual,leftGenerator,rightGenerator,leftCurrent,rightCurrent,
      smul_mul_assoc,mul_smul_comm] using! paid
  have balance:=driven_balance lambda _ _ _ _ _ _ normalized
  simpa only [sourceHamiltonian,temporalPhysicalDrive] using! balance

private theorem observed_driven {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (O : E→L[ℂ]ℂ) (lambda : ℂ) (X B D Z : E)
    (paid : lambda • X-B-Complex.I • D=Complex.I • Z) :
    lambda*O X-O B-Complex.I*O D=Complex.I*O Z := by
  simpa only [map_sub,map_smul,smul_eq_mul] using! congrArg O paid

private theorem subtract_residual (a b d m r : ℂ) (paid : a-b-d=Complex.I*(m+r)) :
    a-b-d-Complex.I*m=Complex.I*r := by linear_combination paid

/-- Complete normalized temporal quantum rows consume the source-small two-endpoint preparation residual. -/
theorem temporal_quantum_preparation_return (event : DressedEvent) (transfer : PhysicalMomentum)
    (a : Fin 12) (force : Field289) (lambda : ℂ) (positive : 0<lambda.re) :
    (staticQuantumCorrection event transfer lambda*ᵥ(fun j=>(force j:ℂ))) (gaugeSlot 0 a)-
      dressedEulerObserver event (temporalGaussInitialJet (dressedKinematicPoint event transfer) a force)-
      Complex.I*dressedEulerObserver event (temporalPhysicalDrive (dressedKinematicPoint event transfer) a force lambda)-
      Complex.I*physicalPreparationMismatch event transfer
        (temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda)=
      Complex.I*preparationWardObserver event
        (temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda) := by
  have correction:=temporal_actual_normalized_polarization event transfer a force lambda positive
  rw [static_input_normalizer_generated lambda positive] at correction
  have observed:=observed_driven (dressedEulerObserver event) lambda _ _ _ _
    (temporal_quantum_physical_action (dressedKinematicPoint event transfer) a force lambda positive)
  have physical :
      lambda*dressedEulerObserver event (temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda)-
        dressedEulerObserver event (temporalGaussInitialJet (dressedKinematicPoint event transfer) a force)-
        Complex.I*dressedEulerObserver event (temporalPhysicalDrive (dressedKinematicPoint event transfer) a force lambda)=
      Complex.I*(physicalPreparationMismatch event transfer
        (temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda)+
        preparationWardObserver event (temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda)) := by
    have action:=physical_preparation_return event transfer
      (temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda)
    have original :
        lambda*dressedEulerObserver event (temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda)-
          dressedEulerObserver event (temporalGaussInitialJet (dressedKinematicPoint event transfer) a force)-
          Complex.I*dressedEulerObserver event (temporalPhysicalDrive (dressedKinematicPoint event transfer) a force lambda)=
        Complex.I*dressedEulerObserver event
          (sourceHamiltonian (event.momentum-transfer) event.frame*temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda-
            temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda*sourceHamiltonian event.momentum event.frame) := by
      simpa only [dressedKinematicPoint,sub_eq_add_neg] using! observed
    exact original.trans (congrArg (fun z : ℂ=>Complex.I*z) action)
  have result:=subtract_residual _ _ _ _ _ physical
  exact (congrArg (fun z : ℂ=>z-
    dressedEulerObserver event (temporalGaussInitialJet (dressedKinematicPoint event transfer) a force)-
    Complex.I*dressedEulerObserver event (temporalPhysicalDrive (dressedKinematicPoint event transfer) a force lambda)-
    Complex.I*physicalPreparationMismatch event transfer
      (temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda)) correction).trans result

theorem temporal_quantum_preparation_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (a : Fin 12) (force : Field289) (lambda : ℂ) (positive : 0<lambda.re) :
    ‖(staticQuantumCorrection event transfer lambda*ᵥ(fun j=>(force j:ℂ))) (gaugeSlot 0 a)-
      dressedEulerObserver event (temporalGaussInitialJet (dressedKinematicPoint event transfer) a force)-
      Complex.I*dressedEulerObserver event (temporalPhysicalDrive (dressedKinematicPoint event transfer) a force lambda)-
      Complex.I*physicalPreparationMismatch event transfer
        (temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda)‖ ≤
      (2*(2*‖sourceLeg true 1 0‖+1))*event.epsilon*
        ‖temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda‖ := by
  rw [temporal_quantum_preparation_return event transfer a force lambda positive,norm_mul,Complex.norm_I,one_mul]
  exact ((preparationWardObserver event).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (preparation_ward_observer_price event) (norm_nonneg _))

theorem temporal_quantum_preparation_limit (event : DressedEvent) (transfer : PhysicalMomentum)
    (a : Fin 12) (force : Field289) (lambda : ℂ) (positive : 0<lambda.re) :
    Tendsto (fun n : ℕ=>
      (staticQuantumCorrection (preparationEventSequence event n) transfer lambda*ᵥ(fun j=>(force j:ℂ))) (gaugeSlot 0 a)-
        dressedEulerObserver (preparationEventSequence event n)
          (temporalGaussInitialJet (dressedKinematicPoint (preparationEventSequence event n) transfer) a force)-
        Complex.I*dressedEulerObserver (preparationEventSequence event n)
          (temporalPhysicalDrive (dressedKinematicPoint (preparationEventSequence event n) transfer) a force lambda)-
        Complex.I*physicalPreparationMismatch (preparationEventSequence event n) transfer
          (temporalGaussHalfJet (dressedKinematicPoint (preparationEventSequence event n) transfer) a force lambda))
      atTop (𝓝 0) := by
  have fixed (n : ℕ) :
      temporalGaussHalfJet (dressedKinematicPoint (preparationEventSequence event n) transfer) a force lambda=
        temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda := by
    unfold temporalGaussHalfJet temporalGaussInitialJet sourceInverse temporalGaussInitial
      leftCurrent rightCurrent dressedKinematicPoint preparationEventSequence
    rfl
  have evaluated:=((ContinuousLinearMap.apply ℂ ℂ
    (temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda)).continuous.tendsto
      (0 : ResponseOp→L[ℂ]ℂ)).comp (preparation_ward_observer_limit event)
  have generated : Tendsto (fun n : ℕ=>preparationWardObserver (preparationEventSequence event n)
      (temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda)) atTop (𝓝 (0:ℂ)) := by
    simpa only [ContinuousLinearMap.apply_apply,zero_apply] using! evaluated
  have multiplied : Tendsto (fun n : ℕ=>Complex.I*preparationWardObserver (preparationEventSequence event n)
      (temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda)) atTop (𝓝 (0:ℂ)) := by
    simpa only [mul_zero] using! generated.const_mul Complex.I
  apply Tendsto.congr' _ multiplied
  exact Filter.Eventually.of_forall (fun n=>
    ((temporal_quantum_preparation_return (preparationEventSequence event n) transfer a force lambda positive).trans
      (congrArg (fun A : ResponseOp=>Complex.I*preparationWardObserver (preparationEventSequence event n) A)
        (fixed n))).symm)

end LowEnergy.GaussComposite.ActualDressedTemporalResidual
