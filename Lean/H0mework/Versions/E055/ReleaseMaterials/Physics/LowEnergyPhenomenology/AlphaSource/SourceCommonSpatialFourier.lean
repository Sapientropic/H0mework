import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCommonSpatialPrice

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCommonSpatialGreen
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
local instance CommonSpatialFourierIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

private theorem phase_norm (frequency position : PhysicalMomentum) : ‖sourceSpatialPhase frequency position‖=1 := by
  simp [sourceSpatialPhase,Complex.norm_exp]

private theorem momentum_coordinate_bound (frequency : PhysicalMomentum) (j : Fin 3) :
    ‖(sourceSpatialMomentum frequency j:ℂ)‖≤(2*Real.pi)*‖frequency‖ := by
  simp only [sourceSpatialMomentum,Pi.smul_apply,smul_eq_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,
    abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos)]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm frequency j) (by positivity)

/-- Original inverse physical Fourier phase, with every angular/material source channel retained. -/
def sourceCommonMomentIntegrand (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex)
    (i j : Fin 3) (m : ℕ) (test : 𝓢(PhysicalMomentum,ℂ)) (x frequency : PhysicalMomentum) : ℂ :=
  (Complex.I*(sourceSpatialMomentum frequency j:ℂ))^m*sourceSpatialPhase frequency x*test frequency*
    sourceCommonCausalChannel q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r i

def sourceCommonSpatialMoment (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex)
    (i j : Fin 3) (m : ℕ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫frequency,sourceCommonMomentIntegrand q c eta l r i j m test x frequency

private theorem moment_continuous (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i j : Fin 3) (m : ℕ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Continuous (sourceCommonMomentIntegrand q c eta l r i j m test x) := by
  have channel:=sourceCommonChannel_continuous q c eta frequency positive l r i
  unfold sourceCommonMomentIntegrand sourceSpatialPhase sourceSpatialMomentum
  fun_prop

theorem sourceCommonMoment_bound (q : PhysicalResponsePoint) (c eta : ℝ)
    (nonzero : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i j : Fin 3) (m : ℕ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x frequency : PhysicalMomentum) :
    ‖sourceCommonMomentIntegrand q c eta l r i j m test x frequency‖≤
      ((2*Real.pi)^m*sourceCommonChannelPrice q c eta l r i)*(‖frequency‖^m*‖test frequency‖) := by
  rw [sourceCommonMomentIntegrand]
  simp only [norm_mul,norm_pow,Complex.norm_I,one_mul,phase_norm,mul_one]
  have coordinate:=pow_le_pow_left₀ (norm_nonneg ((sourceSpatialMomentum frequency j:ℂ)))
    (momentum_coordinate_bound frequency j) m
  have channel:=sourceCommonChannel_bound q (sourceSpatialMomentum frequency) c eta nonzero positive l r i
  calc
    _≤((2*Real.pi)*‖frequency‖)^m*‖test frequency‖*sourceCommonChannelPrice q c eta l r i := by gcongr
    _=_ := by rw [mul_pow];ring

theorem sourceCommonMoment_integrable (q : PhysicalResponsePoint) (c eta : ℝ)
    (nonzero : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i j : Fin 3) (m : ℕ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (sourceCommonMomentIntegrand q c eta l r i j m test x) :=
  ((test.integrable_pow_mul volume m).const_mul ((2*Real.pi)^m*sourceCommonChannelPrice q c eta l r i)).mono'
    (moment_continuous q c eta nonzero positive l r i j m test x).aestronglyMeasurable
    (Eventually.of_forall (sourceCommonMoment_bound q c eta nonzero positive l r i j m test x))

private theorem phase_shift (frequency x : PhysicalMomentum) (j : Fin 3) (t : ℝ) :
    sourceSpatialPhase frequency (x+t • (Pi.single j 1 : PhysicalMomentum))=sourceSpatialPhase frequency x*
      Complex.exp (Complex.I*(sourceSpatialMomentum frequency j:ℂ)*(t:ℂ)) := by
  have dot : (∑k : Fin 3,sourceSpatialMomentum frequency k*(x+t • (Pi.single j 1 : PhysicalMomentum) : PhysicalMomentum) k)=
      (∑k : Fin 3,sourceSpatialMomentum frequency k*x k)+sourceSpatialMomentum frequency j*t := by
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same,mul_one]
    · intro k _ different
      rw [Pi.single_eq_of_ne different,mul_zero,mul_zero]
    · simp
  simp only [sourceSpatialPhase,dot,Complex.ofReal_add,Complex.ofReal_mul,mul_add,Complex.exp_add,mul_assoc]

private theorem phase_derivative (frequency x : PhysicalMomentum) (j : Fin 3) (t : ℝ) :
    HasDerivAt (fun s : ℝ=>sourceSpatialPhase frequency (x+s • (Pi.single j 1 : PhysicalMomentum)))
      (Complex.I*(sourceSpatialMomentum frequency j:ℂ)*sourceSpatialPhase frequency (x+t • (Pi.single j 1 : PhysicalMomentum))) t := by
  simp_rw [phase_shift]
  have h:=(((Complex.ofRealCLM.hasFDerivAt (x:=t)).hasDerivAt.const_mul (Complex.I*(sourceSpatialMomentum frequency j:ℂ))).cexp).const_mul
    (sourceSpatialPhase frequency x)
  convert! h using 1
  simp [Complex.ofRealCLM]
  ring

attribute [local irreducible] sourceCommonCausalChannel sourceCommonChannelPrice

/-- Strong coordinate derivative under the full inverse Fourier integral, paid by source prices and Schwartz moments. -/
theorem sourceCommonMoment_derivative (q : PhysicalResponsePoint) (c eta : ℝ)
    (nonzero : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i j : Fin 3) (m : ℕ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (t : ℝ) :
    HasDerivAt (fun s : ℝ=>sourceCommonSpatialMoment q c eta l r i j m test (x+s • (Pi.single j 1 : PhysicalMomentum)))
      (sourceCommonSpatialMoment q c eta l r i j (m+1) test (x+t • (Pi.single j 1 : PhysicalMomentum))) t := by
  have generated:=hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀:=t) (μ:=volume) (s:=Set.univ) (Filter.univ_mem)
    (F:=fun s frequency=>sourceCommonMomentIntegrand q c eta l r i j m test (x+s • (Pi.single j 1 : PhysicalMomentum)) frequency)
    (F':=fun s frequency=>sourceCommonMomentIntegrand q c eta l r i j (m+1) test (x+s • (Pi.single j 1 : PhysicalMomentum)) frequency)
    (bound:=fun frequency=>((2*Real.pi)^(m+1)*sourceCommonChannelPrice q c eta l r i)*(‖frequency‖^(m+1)*‖test frequency‖))
    (Eventually.of_forall (fun s=>(sourceCommonMoment_integrable q c eta nonzero positive l r i j m test (x+s • (Pi.single j 1 : PhysicalMomentum))).aestronglyMeasurable))
    (sourceCommonMoment_integrable q c eta nonzero positive l r i j m test (x+t • (Pi.single j 1 : PhysicalMomentum)))
    (sourceCommonMoment_integrable q c eta nonzero positive l r i j (m+1) test (x+t • (Pi.single j 1 : PhysicalMomentum))).aestronglyMeasurable
    (Eventually.of_forall (fun frequency s _=>sourceCommonMoment_bound q c eta nonzero positive l r i j (m+1) test (x+s • (Pi.single j 1 : PhysicalMomentum)) frequency))
    ((test.integrable_pow_mul volume (m+1)).const_mul _)
    (Eventually.of_forall (fun frequency s _=>by
      have h:=((phase_derivative frequency x j s).const_mul ((Complex.I*(sourceSpatialMomentum frequency j:ℂ))^m)).mul_const
        (test frequency) |>.mul_const (sourceCommonCausalChannel q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r i)
      simpa only [sourceCommonMomentIntegrand,pow_succ,mul_assoc] using h))
  exact generated.2

end LowEnergy.PreparationPhysicalCommonSpatialGreen
