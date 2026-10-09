import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCommonSpatialReturn
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChannelGreen
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
local instance ChannelGreenIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationPhysicalEnergyPoleChargeReturn
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open FullQuantum.Triangular

open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalJointGeneratorEnergyReturn
open PreparationVacuumMixedFieldReturn GaussComposite.PhysicalFullFieldScattering
open Electromagnetic.CanonicalCoframe

open PreparationPhysicalChargedHamiltonianRead PreparationPhysicalChargedScatteringPoleReturn

open PreparationPhysicalChargedVertexDomainReturn PreparationPhysicalChargedScatteringFourierReturn

open PreparationPhysicalChargedScatteringDomainPrice

open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor PreparationVacuumSharedPoleCarrier
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic PreparationVacuumWholeOrigin

open PreparationPhysicalChargedSoftScatteringReturn PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalScatteringFrequencyWard

open Stage10.CanonicalMatter StageNineCurrentCoframeMatterTemporalPrincipal
open PreparationVacuumGaugeSourceInjection GaussNativeMatter SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates SU7MotherLieAlgebra


open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing Stage9C.Material.SpinPair
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalChargedSoftObservable
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalChargedSoftScatteringReturn
open PreparationPhysicalNormalizedFullField PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open Electromagnetic.CanonicalCoframe FullQuantum.Triangular
open MeasureTheory Filter
open scoped Topology InnerProductSpace

open PreparationPhysicalNativeSoftWardBoundary
open Set

open PreparationPhysicalFinitePoleVertices PreparationPhysicalFiniteOriginCovariance
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativeWardFiniteObservation
open PreparationPhysicalNativePolarizationEmitter

open PreparationVacuumFullPoleContinuation PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationPhysicalFiniteObservationSoftReturn PreparationVacuumSoftPoleSelection

open PreparationVacuumStaticPoleResponse PreparationVacuumFullOriginResponse

open PreparationVacuumStaticSpatialSource PreparationVacuumStaticSimpleCoupling

open PreparationPhysicalCommonCurrentStaticRead PreparationPhysicalActualRetardedWard

open PreparationPhysicalCommonObservableUnits PreparationVacuumPhysicalPinnedVelocity
open PreparationVacuumGaugeSlowFrequency PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalSlowBlock PreparationVacuumSharedPoleCarrier
open PreparationVacuumObservedPoleTensor
open PreparationVacuumActualSpatialPacket
open scoped Matrix.Norms.Operator SchwartzMap

open PreparationPhysicalCommonSpatialGreen

/-- Exact ratios of the original three temporal and spatial coefficients. -/
def sourceChannelMassSquare (i : Fin 3) : ℝ :=
  if i=0 then 3 else if i=1 then 1675/594 else 25/18

theorem sourceChannelMassSquare_positive (i : Fin 3) : 0<sourceChannelMassSquare i := by
  fin_cases i <;> norm_num [sourceChannelMassSquare]

def sourceChannelMassFactor (negative : Bool) (i : Fin 3) : ℂ :=
  (if i=0 then (if negative then Complex.I else -Complex.I) else 1)*
    (Real.sqrt (sourceChannelMassSquare i):ℂ)

def sourceChannelMass (branch : Fin 2) (negative : Bool) (eta : ℝ) (i : Fin 3) : ℂ :=
  sourceChannelMassFactor negative i*sourcePoleSide (sourceSignedSpeed branch negative) eta

theorem sourceChannelMassFactor_square (negative : Bool) (i : Fin 3) :
    (sourceChargedSpatialCoefficient i:ℂ)*(sourceChannelMassFactor negative i)^2=
      (sourceChargedTemporalCoefficient i:ℂ) := by
  have square : ((Real.sqrt (sourceChannelMassSquare i):ℝ):ℂ)^2=(sourceChannelMassSquare i:ℂ) := by
    exact_mod_cast Real.sq_sqrt (sourceChannelMassSquare_positive i).le
  rw [sourceChannelMassFactor,mul_pow,square]
  fin_cases i <;> cases negative <;>
    norm_num [sourceChannelMassSquare,sourceChargedSpatialCoefficient,sourceChargedTemporalCoefficient,
      Complex.ofReal_mul,Complex.ofReal_div,Complex.I_sq] <;> ring

/-- The branch is fixed by the original sign of the source frequency; all generated masses lie in the right half-plane. -/
theorem sourceChannelMass_real (branch : Fin 2) (negative : Bool) (eta : ℝ) (i : Fin 3) :
    (sourceChannelMass branch negative eta i).re=
      Real.sqrt (sourceChannelMassSquare i)*(if i=0 then sourceSpeed branch else eta) := by
  fin_cases i <;> cases negative <;>
    simp [sourceChannelMass,sourceChannelMassFactor,sourceSignedSpeed,sourcePoleSide,Complex.mul_re,Complex.mul_im]

theorem sourceChannelMass_positive (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (i : Fin 3) : 0<(sourceChannelMass branch negative eta i).re := by
  rw [sourceChannelMass_real]
  apply mul_pos (Real.sqrt_pos.mpr (sourceChannelMassSquare_positive i))
  split_ifs
  · exact sourceSpeed_positive branch
  · exact positive

/-- Original static and temporal coefficients generate the exact scalar factor of every full field channel. -/
theorem sourceChannelDenominator_generated (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (n : PhysicalMomentum) (i : Fin 3) :
    sourceChargedDenominator n (sourcePoleSide (sourceSignedSpeed branch negative) eta) i=
      (sourceChargedSpatialCoefficient i:ℂ)*((spatialSquare n:ℂ)+(sourceChannelMass branch negative eta i)^2) := by
  rw [sourceChargedDenominator,sourceChannelMass,mul_pow,mul_add,←mul_assoc,sourceChannelMassFactor_square]

/-- The source complex mass itself selects the convergent heat ray; there is no caller direction or domain certificate. -/
def sourceChannelHeatRay (branch : Fin 2) (negative : Bool) (eta : ℝ) (i : Fin 3) : ℂ :=
  (sourceChannelMass branch negative eta i)⁻¹

theorem sourceChannelHeatRay_positive (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (i : Fin 3) : 0<(sourceChannelHeatRay branch negative eta i).re := by
  rw [sourceChannelHeatRay,Complex.inv_re]
  exact div_pos (sourceChannelMass_positive branch negative eta positive i)
    (Complex.normSq_pos.mpr (fun zero=>by
      have re:=sourceChannelMass_positive branch negative eta positive i
      rw [zero,Complex.zero_re] at re
      exact lt_irrefl _ re))

theorem sourceChannelHeatRay_mass (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (i : Fin 3) :
    sourceChannelHeatRay branch negative eta i*(sourceChannelMass branch negative eta i)^2=
      sourceChannelMass branch negative eta i := by
  have nz : sourceChannelMass branch negative eta i≠0 := by
    intro zero
    have re:=sourceChannelMass_positive branch negative eta positive i
    rw [zero,Complex.zero_re] at re
    exact lt_irrefl _ re
  rw [sourceChannelHeatRay,pow_two,←mul_assoc,inv_mul_cancel₀ nz,one_mul]

/-- The original ray controls the entire physical frequency space, at each positive radial mass scale. -/
theorem sourceChannelHeatRay_frequency (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (i : Fin 3) (d : ℝ) (radial : 0<d) (n : PhysicalMomentum) :
    0<(sourceChannelHeatRay branch negative eta i*
      ((spatialSquare n:ℂ)+(d:ℂ)^2*(sourceChannelMass branch negative eta i)^2)).re := by
  have same : sourceChannelHeatRay branch negative eta i*
      ((spatialSquare n:ℂ)+(d:ℂ)^2*(sourceChannelMass branch negative eta i)^2)=
      (spatialSquare n:ℂ)*sourceChannelHeatRay branch negative eta i+(d:ℂ)^2*sourceChannelMass branch negative eta i := by
    calc
      _=(spatialSquare n:ℂ)*sourceChannelHeatRay branch negative eta i+
        (d:ℂ)^2*(sourceChannelHeatRay branch negative eta i*(sourceChannelMass branch negative eta i)^2) := by ring
      _=_ := by rw [sourceChannelHeatRay_mass branch negative eta positive i]
  rw [same]
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,←Complex.ofReal_pow,zero_mul,sub_zero]
  apply add_pos_of_nonneg_of_pos
  · exact mul_nonneg (by unfold spatialSquare;positivity) (sourceChannelHeatRay_positive branch negative eta positive i).le
  · exact mul_pos (sq_pos_of_pos radial) (sourceChannelMass_positive branch negative eta positive i)

end LowEnergy.PreparationPhysicalChannelGreen
