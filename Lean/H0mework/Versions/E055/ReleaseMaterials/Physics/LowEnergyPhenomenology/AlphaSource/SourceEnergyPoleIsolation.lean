import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceEnergyCliffordCurrent
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhysicalEnergyResidues

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalEnergyPoleChargeReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalChargedPacketVoltage PreparationVacuumVoltageGaussGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumChargedLongRangeRead PreparationVacuumCausalPoleResponse
open PreparationVacuumChargedSpatialResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumFullSlowFieldResponse PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalFeedback PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open CanonicalGradedSpatialSource FullQuantum.CoframeResponse FullQuantum.StateGreen
open GaussHistoryHilbert PreparationVacuumStaticVoltageSource
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace
local instance poleIsolationQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationVacuumObservedBoundaryResidue PreparationVacuumPhysicalCharacteristic

/-- The physical imaginary-axis denominator is generated from its original temporal and spatial coefficients. -/
theorem sourceEnergyDenominator_axis (n : PhysicalMomentum) (frequency : ℝ) (i : Fin 3) :
    sourceChargedDenominator n (Complex.I*(frequency:ℂ)) i=
      ((sourceChargedSpatialCoefficient i*spatialSquare n-sourceChargedTemporalCoefficient i*frequency^2:ℝ):ℂ) := by
  simp only [sourceChargedDenominator,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_pow,
    mul_pow,Complex.I_sq]
  ring

private theorem coefficient_ratio (i : Fin 3) :
    sourceChargedSpatialCoefficient i/sourceChargedTemporalCoefficient i=
      if i=0 then -(1/3:ℝ) else if i=1 then 594/1675 else 18/25 := by
  have two : Real.sqrt 2≠0:=by positivity
  have fifteen : Real.sqrt 15≠0:=by positivity
  fin_cases i <;> norm_num [sourceChargedSpatialCoefficient,sourceChargedTemporalCoefficient]
  all_goals field_simp
  all_goals ring

theorem sourceEnergyDenominator_zero_iff (n : PhysicalMomentum) (frequency : ℝ) (i : Fin 3) :
    sourceChargedDenominator n (Complex.I*(frequency:ℂ)) i=0 ↔
      frequency^2=(if i=0 then -(1/3:ℝ) else if i=1 then 594/1675 else 18/25)*spatialSquare n := by
  rw [sourceEnergyDenominator_axis,Complex.ofReal_eq_zero,←coefficient_ratio,
    div_mul_eq_mul_div,eq_div_iff (sourceChargedTemporalCoefficient_nonzero i)]
  constructor <;> intro equation <;> nlinarith

/-- The complete first channel remains in the response but has no nonzero real-frequency pole. -/
theorem sourceEnergyDenominator_zero_nonzero (n : PhysicalMomentum) (frequency : ℝ) (nonzero : frequency≠0) :
    sourceChargedDenominator n (Complex.I*(frequency:ℂ)) 0≠0 := by
  intro pole
  have equation:=(sourceEnergyDenominator_zero_iff n frequency 0).mp pole
  norm_num [Fin.ext_iff] at equation
  have positive : 0<frequency^2:=sq_pos_of_ne_zero nonzero
  have spatial : (0:ℝ)≤PreparationVacuumPhysicalCharacteristic.spatialSquare n:=by
    unfold PreparationVacuumPhysicalCharacteristic.spatialSquare
    positivity
  nlinarith

/-- Distinct source speeds separate the two propagating poles without assigning an electromagnetic label. -/
theorem sourceEnergyDenominator_poles_disjoint (n : PhysicalMomentum) (frequency : ℝ) (nonzero : frequency≠0) :
    ¬(sourceChargedDenominator n (Complex.I*(frequency:ℂ)) 1=0 ∧
      sourceChargedDenominator n (Complex.I*(frequency:ℂ)) 2=0) := by
  rintro ⟨one,two⟩
  have first:=(sourceEnergyDenominator_zero_iff n frequency 1).mp one
  have second:=(sourceEnergyDenominator_zero_iff n frequency 2).mp two
  norm_num [Fin.ext_iff] at first second
  have positive : 0<frequency^2:=sq_pos_of_ne_zero nonzero
  nlinarith

private theorem isolated_residue (n : PhysicalMomentum) (frequency : ℝ) (i : Fin 3)
    (pole : sourceChargedDenominator n (Complex.I*(frequency:ℂ)) i=0) :
    sourceChargedDenominatorResidue n frequency i=
      ((sourceChargedTemporalCoefficient i:ℂ)*(2*Complex.I*(frequency:ℂ)))⁻¹ := by
  rw [sourceChargedDenominatorResidue,if_pos pole]

/-- At a true channel-one pole, the entire retainer numerator and every physical energy component remain. -/
theorem sourcePhysicalEnergyBoundary_one_isolated (q : PhysicalResponsePoint) (shift : Position) (frequency : ℝ)
    (nonzero : frequency≠0) (pole : sourceChargedDenominator (physicalMomentum shift) (Complex.I*(frequency:ℂ)) 1=0)
    (a b c d sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyBoundary q shift a b c d sideL edgeL sideR edgeR frequency=
      ((sourceChargedTemporalCoefficient 1:ℂ)*(2*Complex.I*(frequency:ℂ)))⁻¹*
        sourceSlowRead (sourceNativeBoundaryResidue q (physicalMomentum shift) frequency
          (sourceChargedRestIndex a b) (sourceChargedRestIndex c d)) 1*
        sourcePhysicalEnergyChannel shift (Complex.I*(frequency:ℂ)) 1 sideL edgeL sideR edgeR := by
  have other : sourceChargedDenominator (physicalMomentum shift) (Complex.I*(frequency:ℂ)) 2≠0:=
    fun same=>sourceEnergyDenominator_poles_disjoint _ frequency nonzero ⟨pole,same⟩
  rw [sourcePhysicalEnergyBoundary_channels,Fin.sum_univ_three,isolated_residue _ _ 1 pole]
  simp only [sourceChargedDenominatorResidue,if_neg (sourceEnergyDenominator_zero_nonzero _ frequency nonzero),
    if_neg other,zero_mul,zero_add,add_zero]
  rfl

theorem sourcePhysicalEnergyBoundary_two_isolated (q : PhysicalResponsePoint) (shift : Position) (frequency : ℝ)
    (nonzero : frequency≠0) (pole : sourceChargedDenominator (physicalMomentum shift) (Complex.I*(frequency:ℂ)) 2=0)
    (a b c d sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyBoundary q shift a b c d sideL edgeL sideR edgeR frequency=
      ((sourceChargedTemporalCoefficient 2:ℂ)*(2*Complex.I*(frequency:ℂ)))⁻¹*
        sourceSlowRead (sourceNativeBoundaryResidue q (physicalMomentum shift) frequency
          (sourceChargedRestIndex a b) (sourceChargedRestIndex c d)) 2*
        sourcePhysicalEnergyChannel shift (Complex.I*(frequency:ℂ)) 2 sideL edgeL sideR edgeR := by
  have other : sourceChargedDenominator (physicalMomentum shift) (Complex.I*(frequency:ℂ)) 1≠0:=
    fun same=>sourceEnergyDenominator_poles_disjoint _ frequency nonzero ⟨same,pole⟩
  rw [sourcePhysicalEnergyBoundary_channels,Fin.sum_univ_three,isolated_residue _ _ 2 pole]
  simp only [sourceChargedDenominatorResidue,if_neg (sourceEnergyDenominator_zero_nonzero _ frequency nonzero),
    if_neg other,zero_mul,zero_add,add_zero]
  rfl

end LowEnergy.PreparationPhysicalEnergyPoleChargeReturn
