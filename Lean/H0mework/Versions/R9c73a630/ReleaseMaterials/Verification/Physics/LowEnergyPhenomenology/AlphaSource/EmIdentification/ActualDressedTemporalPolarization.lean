import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalHalfResponse

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedTemporalHalf
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField
open PreparationVacuumNoetherChart PreparationVacuumGaugeSourceInjection
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumGaugeSourceInjection
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalHalfAxis PreparationVacuumPropagationPencil
open PreparationVacuumTemporalCharge PreparationVacuumSourceChargeWard PreparationVacuumNoetherChart
open PreparationVacuumRawJointFeedback
open SourcePropagationResolvent SourcePropagationFieldFeedback SourcePropagationNearFieldTime
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedSylvester
open ActualDressedNonlinearHalf ActualDressedStaticResponse
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
local instance : NormedAlgebra ℝ ResponseOp := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] noetherReader noetherReaderContact rawReader rawReaderContact jointResolvent jointCurrent
  noetherStaticInitial noetherStaticContact slopeInitial rawInitial noetherStaticHalf sourceInverse
  noetherBackgroundInitial temporalGaussInitial temporalGaussReader

/-- The temporal contact is zero, while both original preparation-resolvent variations remain. -/
def temporalGaussInitialJet (q : PhysicalResponsePoint) (a : Fin 12) (force : Field289) : ResponseOp :=
  (-(jointResolvent (q.p+q.k) q.F q.z 0*jointCurrent (q.p+q.k) q.F q.z 0 force*
    jointResolvent (q.p+q.k) q.F q.z 0))*(-temporalGaussReader q.F a)*jointResolvent q.p q.F q.w 0+
  jointResolvent (q.p+q.k) q.F q.z 0*(-temporalGaussReader q.F a)*
    (-(jointResolvent q.p q.F q.w 0*jointCurrent q.p q.F q.w 0 force*jointResolvent q.p q.F q.w 0))

private theorem temporal_raw_gauss (q : PhysicalResponsePoint) (a : Fin 12) :
    rawReader (temporalField a) q.p q.F 0= -temporalGaussReader q.F a :=
  (noetherReader_source (temporalField a) q.p q.F).symm.trans
    (temporal_reader_gauss q.F 0 (by simpa using temporal_frame_radius_positive q.F) a q.p)

private theorem initial_cancel {A : Type*} [Ring A] (L J R CL CR raw : A) :
    ((-(L*CL*L))*J*R+L*raw*R+L*J*(-(R*CR*R)))+L*(0-raw)*R=
      (-(L*CL*L))*J*R+L*J*(-(R*CR*R)) :=by
  simp only [zero_sub,mul_neg,neg_mul]
  abel

theorem temporal_gauss_initial_jet (q : PhysicalResponsePoint) (a : Fin 12) (force : Field289) :
    noetherStaticInitial q (temporalField a) force=temporalGaussInitialJet q a force :=by
  unfold noetherStaticInitial slopeInitial noetherStaticContact temporalGaussInitialJet
  simp only [temporalContactReader_zero a force q.p q.F,temporal_raw_gauss q a]
  exact initial_cancel _ _ _ _ _ _

/-- The actual halfline derivative keeps the two preparation terms and both ordered time drives. -/
def temporalGaussHalfJet (q : PhysicalResponsePoint) (a : Fin 12) (force : Field289) (lambda : ℂ) : ResponseOp :=
  sourceInverse q lambda
    (temporalGaussInitialJet q a force-
      leftCurrent q force*sourceInverse q lambda (temporalGaussInitial q a 0)+
      sourceInverse q lambda (temporalGaussInitial q a 0)*rightCurrent q force)

theorem temporal_gauss_half_jet (q : PhysicalResponsePoint) (a : Fin 12) (force : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) :
    noetherStaticHalf q (temporalField a) force lambda=temporalGaussHalfJet q a force lambda :=by
  rw [noether_static_half_inverse q (temporalField a) force lambda positive,
    temporal_gauss_initial_jet q a force]
  have initial : rawInitial q (temporalField a)=temporalGaussInitial q a 0 :=by
    exact (noether_background_initial_source q (temporalField a)).symm.trans
      (temporal_gauss_initial_generated q a 0 (by simpa using temporal_frame_radius_positive q.F))
  rw [initial]
  rfl

theorem temporal_actual_half_derivative (event : DressedEvent) (transfer : PhysicalMomentum) (a : Fin 12)
    (force : Field289) (lambda : ℂ) (positive : 0<lambda.re) :
    HasDerivAt (fun r : ℝ=>dressedNoetherHalfSource event transfer lambda (r • force) (gaugeSlot 0 a))
      (dressedEulerObserver event
        (temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda)) 0 :=by
  have generated:=hasDerivAt_pi.mp (dressed_noether_half_derivative event transfer force lambda positive) (gaugeSlot 0 a)
  have slot : fieldUnit (gaugeSlot 0 a)=temporalField a:=rfl
  simpa only [slot,temporal_gauss_half_jet _ a force lambda positive] using! generated

/-- A row of the full actual polarization is computed by the same source weighted-Gauss halfline, without discarding its endpoints. -/
theorem temporal_actual_polarization (event : DressedEvent) (transfer : PhysicalMomentum) (a : Fin 12)
    (force : Field289) (lambda : ℂ) (positive : 0<lambda.re) :
    (dressedStaticPolarization event transfer lambda*ᵥ(fun j=>(force j:ℂ))) (gaugeSlot 0 a)=
      dressedEulerObserver event (temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda) :=by
  exact (hasDerivAt_pi.mp (dressed_noether_half_full_derivative event transfer lambda positive force)
    (gaugeSlot 0 a)).unique (temporal_actual_half_derivative event transfer a force lambda positive)

theorem temporal_actual_normalized_polarization (event : DressedEvent) (transfer : PhysicalMomentum) (a : Fin 12)
    (force : Field289) (lambda : ℂ) (positive : 0<lambda.re) :
    (staticQuantumCorrection event transfer lambda*ᵥ(fun j=>(force j:ℂ))) (gaugeSlot 0 a)=
      staticInputNormalizer lambda*dressedEulerObserver event
        (temporalGaussHalfJet (dressedKinematicPoint event transfer) a force lambda) :=by
  have generated:=(temporal_actual_half_derivative event transfer a force lambda positive).const_mul
    (staticInputNormalizer lambda)
  have actual:=hasDerivAt_pi.mp (dressed_normalized_noether_derivative event transfer lambda positive force)
    (gaugeSlot 0 a)
  exact actual.unique (by simpa only [dressedNormalizedNoetherSource,Pi.smul_apply,smul_eq_mul] using! generated)

end LowEnergy.GaussComposite.ActualDressedTemporalHalf
