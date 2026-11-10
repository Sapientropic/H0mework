import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleCoulombRead
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceElectronChargeUnit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalN3SourceEnergy
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource ActualCompositeFieldCurrent ActualDressedFullCoulomb
open ActualDressedEMPhysicalRead ActualDressedNoetherCoulombUnit
open ActualDressedAngularSpherePrice ActualDressedAngularSectorFourier
open ActualDressedAngularWholeChart ActualEMCarrierOwn
open PreparationVacuumPhysicalCharacteristic
open PreparationPhysicalElectronChargeUnitReturn
open ActualDressedEMZeroClockColumns PreparationVacuumPhysicalPoleSheet
open MeasureTheory Filter Set
open scoped Topology SchwartzMap
attribute [local irreducible] physicalN3PoleRawEMPoleObserver

def physicalN3PoleChargePair (detector source : DressedEvent) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) : ℂ :=
  physicalN3PoleRawEMPoleObserver detector dLeg dPoles *
    physicalN3PoleRawEMPoleObserver source sLeg sPoles

/-- The temporal channel is the original whole-direction field packet on the actual charges. -/
def physicalN3PoleTemporalCoulombPacket (fieldEvent detector source : DressedEvent)
    (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg)
    (chart : SourceWholeDirectionChart fieldEvent) (test : 𝓢(PhysicalMomentum,ℂ))
    (x : PhysicalMomentum) : ℂ :=
  physicalN3PoleChargePair detector source dLeg sLeg dPoles sPoles *
    (noetherPairScale^2 *
      sectorCoefficientPacket fieldEvent (directionZeroClockEM fieldEvent 0 0) chart.eta test x)

theorem physical_n3_pole_actual_coulomb_convolution (fieldEvent detector source : DressedEvent)
    (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg)
    (chart : SourceWholeDirectionChart fieldEvent)
    (denominator : directionLeadingDenominator fieldEvent≠0)
    (checked : sourceStandardStaticRemainder fieldEvent=0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    physicalN3PoleTemporalCoulombPacket fieldEvent detector source dLeg sLeg dPoles sPoles chart test x =
      ∫ y : PhysicalMomentum,
        (physicalN3PoleChargePair detector source dLeg sLeg dPoles sPoles *
          sourceGeneratedScalarCEM fieldEvent) / (Real.sqrt (spatialSquare y) : ℂ) *
          emPacket test (x-y) := by
  have source_field := source_standard_actual_coulomb_convolution fieldEvent chart denominator checked test x
  unfold physicalN3PoleTemporalCoulombPacket
  calc
    _ = physicalN3PoleChargePair detector source dLeg sLeg dPoles sPoles *
        (∫ y : PhysicalMomentum, sourceGeneratedScalarCEM fieldEvent /
          (Real.sqrt (spatialSquare y) : ℂ) * emPacket test (x-y)) :=
      congrArg (fun a : ℂ => physicalN3PoleChargePair detector source dLeg sLeg dPoles sPoles * a) source_field
    _ = ∫ y : PhysicalMomentum,
        physicalN3PoleChargePair detector source dLeg sLeg dPoles sPoles *
          (sourceGeneratedScalarCEM fieldEvent / (Real.sqrt (spatialSquare y) : ℂ) *
            emPacket test (x-y)) := (integral_const_mul _ _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      ring

theorem physical_n3_pole_coulomb_spatial_return (fieldEvent detector source : DressedEvent)
    (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg)
    (chart : SourceWholeDirectionChart fieldEvent)
    (denominator : directionLeadingDenominator fieldEvent≠0)
    (checked : sourceStandardStaticRemainder fieldEvent=0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ =>
        physicalN3PoleChargePair detector source dLeg sLeg dPoles sPoles *
          (noetherPairScale^2 * sectorFourierPacket fieldEvent
            (directionZeroClockEM fieldEvent 0 0) chart.eta scale test x))
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (physicalN3PoleTemporalCoulombPacket fieldEvent detector source dLeg sLeg dPoles sPoles chart test x)) := by
  have returned := (source_standard_coulomb_spatial_return fieldEvent chart denominator checked test x).const_mul
    (physicalN3PoleChargePair detector source dLeg sLeg dPoles sPoles)
  unfold physicalN3PoleTemporalCoulombPacket
  rw [source_standard_actual_coulomb_convolution fieldEvent chart denominator checked test x]
  exact returned

def physicalN3PoleEMCouplingExpression (fieldEvent : DressedEvent) : ℂ :=
  ((sourceElectronNoetherUnit 0)^2 * sourceGeneratedScalarCEM fieldEvent) /
    ((Stage10.ActionNormalization.phaseMomentum * sourceGeneratedPhysicalC fieldEvent : ℝ) : ℂ)

theorem physical_n3_pole_electron_unit_coupling (fieldEvent : DressedEvent) :
    physicalN3PoleEMCouplingExpression fieldEvent =
      sourceGeneratedScalarCEM fieldEvent /
        ((Stage10.ActionNormalization.phaseMomentum * sourceGeneratedPhysicalC fieldEvent : ℝ) : ℂ) := by
  simp only [physicalN3PoleEMCouplingExpression, sourceElectronNoetherUnit_generated,
    sourceElectronChargeUnit_generated,
    one_pow, one_mul]

theorem physical_n3_pole_em_normalization_nonzero (fieldEvent : DressedEvent)
    (physical : 0<sourceGeneratedPhysicalC fieldEvent) :
    ((Stage10.ActionNormalization.phaseMomentum * sourceGeneratedPhysicalC fieldEvent : ℝ) : ℂ)≠0 :=
  Complex.ofReal_ne_zero.mpr (mul_pos Stage10.ActionNormalization.phaseMomentum_positive physical).ne'

private theorem normalized_coulomb_scalar (q C n r phase : ℂ) (nonzero : n≠0) :
    (q*C/r*phase)*n⁻¹ = q*(C/n)/r*phase := by
  change (q*C/r*phase)/n = _
  apply (div_eq_iff nonzero).mpr
  calc
    _ = (q*C/r*phase)*(n⁻¹*n) := by rw [inv_mul_cancel₀ nonzero, mul_one]
    _ = _ := by simp only [div_eq_mul_inv]; ring

theorem physical_n3_pole_coulomb_normalized_read (fieldEvent detector source : DressedEvent)
    (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg)
    (chart : SourceWholeDirectionChart fieldEvent)
    (denominator : directionLeadingDenominator fieldEvent≠0)
    (checked : sourceStandardStaticRemainder fieldEvent=0)
    (physical : 0<sourceGeneratedPhysicalC fieldEvent)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    physicalN3PoleTemporalCoulombPacket fieldEvent detector source dLeg sLeg dPoles sPoles chart test x /
        ((Stage10.ActionNormalization.phaseMomentum * sourceGeneratedPhysicalC fieldEvent : ℝ) : ℂ) =
      ∫ y : PhysicalMomentum,
        physicalN3PoleChargePair detector source dLeg sLeg dPoles sPoles *
          physicalN3PoleEMCouplingExpression fieldEvent / (Real.sqrt (spatialSquare y) : ℂ) *
          emPacket test (x-y) := by
  have normalization := physical_n3_pole_em_normalization_nonzero fieldEvent physical
  rw [physical_n3_pole_actual_coulomb_convolution fieldEvent detector source
    dLeg sLeg dPoles sPoles chart denominator checked test x]
  rw [div_eq_mul_inv, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with y
  rw [physical_n3_pole_electron_unit_coupling]
  exact normalized_coulomb_scalar _ _ _ _ _ normalization

end LowEnergy.GaussComposite.PhysicalN3SourceEnergy
