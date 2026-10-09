import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChannelGreenMass

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
local instance ChannelHeatIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

def sourceChannelHeatRate (branch : Fin 2) (negative : Bool) (eta : ℝ) (i : Fin 3)
    (d : ℝ) (n : PhysicalMomentum) : ℂ :=
  sourceChannelHeatRay branch negative eta i*((spatialSquare n:ℂ)+(d:ℂ)^2*(sourceChannelMass branch negative eta i)^2)

def sourceChannelHeatMultiplier (branch : Fin 2) (negative : Bool) (eta : ℝ) (i : Fin 3)
    (d : ℝ) (n : PhysicalMomentum) (t : ℝ) : ℂ :=
  (sourceChannelHeatRay branch negative eta i/(sourceChargedSpatialCoefficient i:ℂ))*
    Complex.exp (-sourceChannelHeatRate branch negative eta i d n*(t:ℂ))

theorem sourceChannelHeatMultiplier_integrable (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (i : Fin 3) (d : ℝ) (radial : 0<d) (n : PhysicalMomentum) :
    IntegrableOn (sourceChannelHeatMultiplier branch negative eta i d n) (Set.Ioi 0) :=
  (integrableOn_exp_mul_complex_Ioi (a:= -sourceChannelHeatRate branch negative eta i d n)
    (by simpa only [sourceChannelHeatRate,Complex.neg_re,neg_lt_zero] using sourceChannelHeatRay_frequency branch negative eta positive i d radial n) 0).const_mul _

/-- Exact Laplace representation of the original field denominator on its generated convergent ray. -/
theorem sourceChannelHeatMultiplier_generated (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (i : Fin 3) (d : ℝ) (radial : 0<d) (n : PhysicalMomentum) :
    (∫t : ℝ in Set.Ioi 0,sourceChannelHeatMultiplier branch negative eta i d n t)=
      (sourceChargedDenominator n ((d:ℂ)*sourcePoleSide (sourceSignedSpeed branch negative) eta) i)⁻¹ := by
  have generated:=integral_exp_mul_complex_Ioi (a:= -sourceChannelHeatRate branch negative eta i d n)
    (by simpa only [sourceChannelHeatRate,Complex.neg_re,neg_lt_zero] using sourceChannelHeatRay_frequency branch negative eta positive i d radial n) 0
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,neg_div_neg_eq,one_div] at generated
  have rateNZ : sourceChannelHeatRate branch negative eta i d n≠0 := by
    intro zero
    have p:=sourceChannelHeatRay_frequency branch negative eta positive i d radial n
    change 0<(sourceChannelHeatRate branch negative eta i d n).re at p
    rw [zero,Complex.zero_re] at p
    exact lt_irrefl _ p
  have rayNZ : sourceChannelHeatRay branch negative eta i≠0 := (mul_ne_zero_iff.mp rateNZ).1
  have sumNZ : (spatialSquare n:ℂ)+(d:ℂ)^2*(sourceChannelMass branch negative eta i)^2≠0 := (mul_ne_zero_iff.mp rateNZ).2
  have aNZ : (sourceChargedSpatialCoefficient i:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (sourceChargedSpatialCoefficient_positive i).ne'
  have denominator : sourceChargedDenominator n ((d:ℂ)*sourcePoleSide (sourceSignedSpeed branch negative) eta) i=
      (sourceChargedSpatialCoefficient i:ℂ)*((spatialSquare n:ℂ)+(d:ℂ)^2*(sourceChannelMass branch negative eta i)^2) := by
    rw [sourceChargedDenominator,sourceChannelMass,mul_pow,mul_pow]
    have factor:=sourceChannelMassFactor_square negative i
    calc
      _=(sourceChargedSpatialCoefficient i:ℂ)*(spatialSquare n:ℂ)+
        (d:ℂ)^2*((sourceChargedSpatialCoefficient i:ℂ)*(sourceChannelMassFactor negative i)^2)*
          (sourcePoleSide (sourceSignedSpeed branch negative) eta)^2 := by rw [factor];ring
      _=_ := by ring
  simp only [sourceChannelHeatMultiplier,integral_const_mul]
  rw [generated,denominator]
  unfold sourceChannelHeatRate
  field_simp [rayNZ,sumNZ,aNZ]

/-- The source physical 2pi momentum map fixes this Gaussian coefficient. -/
def sourceChannelGaussianCoefficient (branch : Fin 2) (negative : Bool) (eta : ℝ) (i : Fin 3) (t : ℝ) : ℂ :=
  ((4*Real.pi^2*t:ℝ):ℂ)*sourceChannelHeatRay branch negative eta i

private theorem gaussian_positive (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (i : Fin 3) (t : ℝ) (time : 0<t) :
    0<(sourceChannelGaussianCoefficient branch negative eta i t).re := by
  simp only [sourceChannelGaussianCoefficient,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_pos (by positivity) (sourceChannelHeatRay_positive branch negative eta positive i)

def sourceChannelGaussianIntegrand (branch : Fin 2) (negative : Bool) (eta : ℝ) (i : Fin 3)
    (t : ℝ) (x frequency : PhysicalMomentum) : ℂ :=
  sourceSpatialPhase frequency x*Complex.exp (-((t:ℂ)*sourceChannelHeatRay branch negative eta i)*
    (spatialSquare (sourceSpatialMomentum frequency):ℂ))

def sourceChannelGaussianKernel (branch : Fin 2) (negative : Bool) (eta : ℝ) (i : Fin 3)
    (t : ℝ) (x : PhysicalMomentum) : ℂ :=
  ∫frequency,sourceChannelGaussianIntegrand branch negative eta i t x frequency

private theorem gaussian_integrand (branch : Fin 2) (negative : Bool) (eta : ℝ) (i : Fin 3)
    (t : ℝ) (x frequency : PhysicalMomentum) :
    sourceChannelGaussianIntegrand branch negative eta i t x frequency=
      Complex.exp (-sourceChannelGaussianCoefficient branch negative eta i t*(∑j : Fin 3,(frequency j:ℂ)^2)+
        ∑j : Fin 3,((2*Real.pi:ℝ):ℂ)*Complex.I*(x j:ℂ)*(frequency j:ℂ)) := by
  rw [sourceChannelGaussianIntegrand,sourceSpatialPhase,←Complex.exp_add]
  congr 1
  simp only [sourceChannelGaussianCoefficient,sourceSpatialMomentum,spatialSquare,Pi.smul_apply,smul_eq_mul,
    Fin.sum_univ_three,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow]
  push_cast
  ring

theorem sourceChannelGaussian_integrable (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (i : Fin 3) (t : ℝ) (time : 0<t) (x : PhysicalMomentum) :
    Integrable (sourceChannelGaussianIntegrand branch negative eta i t x) := by
  have same : sourceChannelGaussianIntegrand branch negative eta i t x=
      fun frequency=>Complex.exp (-sourceChannelGaussianCoefficient branch negative eta i t*(∑j : Fin 3,(frequency j:ℂ)^2)+
        ∑j : Fin 3,((2*Real.pi:ℝ):ℂ)*Complex.I*(x j:ℂ)*(frequency j:ℂ)) := by
    funext frequency
    exact gaussian_integrand branch negative eta i t x frequency
  rw [same]
  exact GaussianFourier.integrable_cexp_neg_mul_sum_add (gaussian_positive branch negative eta positive i t time) _

/-- Original inverse Fourier normalization is generated by the complete three-dimensional complex Gaussian integral. -/
theorem sourceChannelGaussian_generated (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (i : Fin 3) (t : ℝ) (time : 0<t) (x : PhysicalMomentum) :
    sourceChannelGaussianKernel branch negative eta i t x=
      ((Real.pi:ℂ)/sourceChannelGaussianCoefficient branch negative eta i t)^(3/2:ℂ)*
        Complex.exp (-((Real.pi:ℂ)^2/sourceChannelGaussianCoefficient branch negative eta i t)*(spatialSquare x:ℂ)) := by
  unfold sourceChannelGaussianKernel
  simp_rw [gaussian_integrand]
  rw [GaussianFourier.integral_cexp_neg_mul_sum_add (gaussian_positive branch negative eta positive i t time)]
  norm_num only [Fintype.card_fin]
  congr 1
  congr 1
  simp only [Fin.sum_univ_three,spatialSquare,Complex.ofReal_add,Complex.ofReal_pow,Complex.ofReal_mul]
  ring_nf
  simp only [Complex.I_sq,Complex.ofReal_ofNat]
  ring

end LowEnergy.PreparationPhysicalChannelGreen
