import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleCurrentSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMStandardLongRange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalN3SourceEnergy
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedEMPhysicalRead
open ActualDressedNoetherCoulombUnit ActualDressedEMTensorClock
open ActualDressedAngularSpherePrice ActualDressedAngularSectorFourier
open ActualDressedZeroClockVector ActualDressedEMZeroClockColumns
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualEMCarrierOwn ActualEMCurrentSplit ActualEMResponseSplit
open MeasureTheory Filter Set
open scoped Matrix BigOperators Topology SchwartzMap
attribute [local irreducible] physicalN3PoleCurrent physicalN3PoleRawEMPoleObserver
  correctedGreen correctedEMTensor sourceStaticNoetherTensor noetherPairScale

def physicalN3PoleNoetherCurrent (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) : Fin 4→ℂ :=
  (Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹ •
    emCurrent (physicalN3PoleCurrent event leg poles)

theorem physical_n3_pole_noether_current_temporal (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) :
    physicalN3PoleNoetherCurrent event leg poles 0 =
      physicalN3PoleRawEMPoleObserver event leg poles := by
  have h := physical_n3_pole_current_em_charge event leg poles
  have nonzero : (Stage10.ActionNormalization.phaseMomentum : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne'
  unfold physicalN3PoleNoetherCurrent
  simp only [Pi.smul_apply, smul_eq_mul, h, ← mul_assoc, inv_mul_cancel₀ nonzero, one_mul]

theorem physical_n3_pole_coordinate_noether_unit (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) :
    emCoordinateCurrent (physicalN3PoleCurrent event leg poles) =
      noetherPairScale • physicalN3PoleNoetherCurrent event leg poles := by
  have nonzero : (Stage10.ActionNormalization.phaseMomentum : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne'
  unfold physicalN3PoleNoetherCurrent noetherPairScale emCoordinateCurrent
  rw [smul_smul]
  congr 1
  field_simp [nonzero]

private theorem noether_tensor_pair_scale (T : Matrix (Fin 4) (Fin 4) ℂ)
    (a : ℂ) (qd qs : Fin 4→ℂ) :
    dotProduct (a • qd) (T*ᵥ(a • qs)) = dotProduct qd ((a^2 • T)*ᵥqs) := by
  simp only [Matrix.mulVec_smul, Matrix.smul_mulVec, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring

def physicalN3PoleNonPureRead (fieldEvent detector source : DressedEvent)
    (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg)
    (eps s sigma : ℝ) (n : PhysicalMomentum) : ℂ :=
  let G := correctedGreen fieldEvent eps s sigma n
  let fd := physicalN3PoleCurrent detector dLeg dPoles
  let fs := physicalN3PoleCurrent source sLeg sPoles
  emCurrentObservation G (emCurrentForce fd) (emCurrentResidual fs) +
    emCurrentObservation G (emCurrentResidual fd) (emCurrentForce fs) +
    emCurrentObservation G (emCurrentResidual fd) (emCurrentResidual fs)

/-- The original full field receives independent actual pole currents without a pure-EM replacement. -/
theorem physical_n3_pole_corrected_four_parts (fieldEvent detector source : DressedEvent)
    (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg)
    (eps s sigma : ℝ) (n : PhysicalMomentum) :
    emCurrentObservation (correctedGreen fieldEvent eps s sigma n)
        (physicalN3PoleCurrent detector dLeg dPoles) (physicalN3PoleCurrent source sLeg sPoles) =
      dotProduct (physicalN3PoleNoetherCurrent detector dLeg dPoles)
        ((noetherPairScale^2 • correctedEMTensor fieldEvent eps s sigma n)*ᵥ
          physicalN3PoleNoetherCurrent source sLeg sPoles) +
        physicalN3PoleNonPureRead fieldEvent detector source dLeg sLeg dPoles sPoles eps s sigma n := by
  have full := em_response_four_parts (correctedGreen fieldEvent eps s sigma n)
    (physicalN3PoleCurrent detector dLeg dPoles) (physicalN3PoleCurrent source sLeg sPoles)
  have pure : emPureObservation (correctedGreen fieldEvent eps s sigma n)
      (physicalN3PoleCurrent detector dLeg dPoles) (physicalN3PoleCurrent source sLeg sPoles) =
      dotProduct (physicalN3PoleNoetherCurrent detector dLeg dPoles)
        ((noetherPairScale^2 • correctedEMTensor fieldEvent eps s sigma n)*ᵥ
          physicalN3PoleNoetherCurrent source sLeg sPoles) := by
    unfold emPureObservation
    rw [physical_n3_pole_coordinate_noether_unit, physical_n3_pole_coordinate_noether_unit]
    rw [correctedEMTensor.eq_def]
    exact noether_tensor_pair_scale _ _ _ _
  rw [pure] at full
  exact full.trans (by unfold physicalN3PoleNonPureRead; ring)

def physicalN3PoleStaticEMRead (fieldEvent detector source : DressedEvent)
    (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (n : PhysicalMomentum) : ℂ :=
  dotProduct (physicalN3PoleNoetherCurrent detector dLeg dPoles)
    (sourceStaticNoetherTensor fieldEvent n*ᵥphysicalN3PoleNoetherCurrent source sLeg sPoles) /
      (4*(Real.pi : ℂ))

def physicalN3PoleOtherEMRead (fieldEvent detector source : DressedEvent)
    (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (n : PhysicalMomentum) : ℂ :=
  (∑ mu : Fin 4, ∑ nu : Fin 4, if mu=0 ∧ nu=0 then 0 else
    physicalN3PoleNoetherCurrent detector dLeg dPoles mu *
      sourceStaticNoetherTensor fieldEvent n mu nu *
      physicalN3PoleNoetherCurrent source sLeg sPoles nu) / (4*(Real.pi : ℂ))

private theorem pole_temporal_tensor_split (T : Matrix (Fin 4) (Fin 4) ℂ)
    (qd qs : Fin 4→ℂ) :
    dotProduct qd (T*ᵥqs) = qd 0*T 0 0*qs 0 +
      ∑ mu : Fin 4, ∑ nu : Fin 4, if mu=0 ∧ nu=0 then 0 else qd mu*T mu nu*qs nu := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_four]
  ring

theorem physical_n3_pole_static_em_charge_pair (fieldEvent detector source : DressedEvent)
    (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (n : PhysicalMomentum) :
    physicalN3PoleStaticEMRead fieldEvent detector source dLeg sLeg dPoles sPoles n =
      physicalN3PoleRawEMPoleObserver detector dLeg dPoles *
        physicalN3PoleRawEMPoleObserver source sLeg sPoles *
          (sourceStaticNoetherTensor fieldEvent n 0 0 / (4*(Real.pi : ℂ))) +
        physicalN3PoleOtherEMRead fieldEvent detector source dLeg sLeg dPoles sPoles n := by
  have split := pole_temporal_tensor_split (sourceStaticNoetherTensor fieldEvent n)
    (physicalN3PoleNoetherCurrent detector dLeg dPoles) (physicalN3PoleNoetherCurrent source sLeg sPoles)
  rw [physical_n3_pole_noether_current_temporal, physical_n3_pole_noether_current_temporal] at split
  unfold physicalN3PoleStaticEMRead physicalN3PoleOtherEMRead
  rw [split]
  ring

private theorem pole_standard_temporal (electric magnetic : ℂ) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) :
    sourceStandardStaticTensor electric magnetic n 0 0 = electric := by
  simp only [sourceStandardStaticTensor, sourceStandardStaticNumerator, and_self, if_true,
    map_mul, MvPolynomial.eval_C, source_spatial_square_polynomial, unit,
    Complex.ofReal_one, one_pow, mul_one, div_one]

theorem physical_n3_pole_standard_cem_charge_pair (fieldEvent detector source : DressedEvent)
    (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg)
    (denominator : directionLeadingDenominator fieldEvent≠0)
    (checked : sourceStandardStaticRemainder fieldEvent=0) (n : PhysicalMomentum)
    (regular : directionLeadingRead fieldEvent n≠0) (unit : spatialSquare n=1) :
    physicalN3PoleStaticEMRead fieldEvent detector source dLeg sLeg dPoles sPoles n =
      physicalN3PoleRawEMPoleObserver detector dLeg dPoles *
        physicalN3PoleRawEMPoleObserver source sLeg sPoles * sourceGeneratedScalarCEM fieldEvent +
        physicalN3PoleOtherEMRead fieldEvent detector source dLeg sLeg dPoles sPoles n := by
  have tensor := (source_static_standard_iff fieldEvent denominator).mp checked n regular
    (by rw [unit]; exact one_ne_zero)
  have temporal := congrArg (fun T : Matrix (Fin 4) (Fin 4) ℂ => T 0 0) tensor
  have returned := physical_n3_pole_static_em_charge_pair fieldEvent detector source dLeg sLeg dPoles sPoles n
  rw [temporal, pole_standard_temporal _ _ n unit] at returned
  exact returned

end LowEnergy.GaussComposite.PhysicalN3SourceEnergy
