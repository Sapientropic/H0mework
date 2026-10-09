import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCausalRadialHomogeneity

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCausalSpatialDilation
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
local instance CausalDilationIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationPhysicalCommonSpatialGreen PreparationPhysicalActualGaussChargeCurrent
open PreparationPhysicalActualNoetherVertexReturn PreparationPhysicalActualPhaseChargeReturn

open Set GaussianFourier


open PreparationPhysicalChannelGreen


open PreparationPhysicalChannelRadialJet PreparationVacuumObservedStaticResidue


open GaussCoreHilbert SourceJointResidualEnergy PreparationVacuumQuantumSlowResponse
open PreparationPhysicalJointRadialForcing

open PreparationVacuumPhysicalHalfAxis CanonicalGradedCurrent GaussUnitaryHistory
open PreparationPhysicalRetainerResolventSquare PreparationVacuumStaticSpatialSource
attribute [local irreducible] sourceCommonCausalChannel sourceMasterChannel sourceMasterChannelDerivative
  sourceMasterChannelCorrection sourceActualPreparedWeight sourceCommonOriginColumn

/-- This is the original Schwartz observation pulled back by the physical spatial dilation. -/
def sourceDilatedTest (s : ℝ) (nonzero : s≠0) (test : 𝓢(PhysicalMomentum,ℂ)) : 𝓢(PhysicalMomentum,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearEquiv.smulOfNeZero ℝ PhysicalMomentum s nonzero).toContinuousLinearEquiv) test

theorem sourceDilatedTest_apply (s : ℝ) (nonzero : s≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (n : PhysicalMomentum) :
    sourceDilatedTest s nonzero test n=test (s • n) := rfl

private theorem side_radial (s c eta : ℝ) :
    sourcePoleSide (s*c) (s*eta)=(s:ℂ)*sourcePoleSide c eta := by
  simp only [sourcePoleSide,Complex.ofReal_mul]
  ring

private theorem momentum_radial (s : ℝ) (n : PhysicalMomentum) :
    sourceSpatialMomentum (s • n)=s • sourceSpatialMomentum n := by
  simp only [sourceSpatialMomentum,smul_smul]
  congr 1
  ring

private theorem phase_radial (s : ℝ) (n x : PhysicalMomentum) :
    sourceSpatialPhase (s • n) x=sourceSpatialPhase n (s • x) := by
  unfold sourceSpatialPhase
  rw [momentum_radial]
  congr 3
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

private theorem three_dimensional_change (f g : PhysicalMomentum→ℂ) (s : ℝ) (positive : 0<s)
    (k : ℕ) (point : ∀n,f (s • n)=((s:ℂ)⁻¹)^k*g n) :
    ((s:ℂ)⁻¹)^3*(∫n,f n)=((s:ℂ)⁻¹)^k*(∫n,g n) := by
  have jacobian:=MeasureTheory.Measure.integral_comp_smul (μ:=volume) f s
  have actualJacobian : (∫n,f (s • n))=((s:ℂ)⁻¹)^3*(∫n,f n) := by
    simpa only [Module.finrank_fin_fun,inv_pow,abs_of_pos (inv_pos.mpr (pow_pos positive 3)),
      Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_inv] using jacobian
  rw [←actualJacobian]
  simp only [point,integral_const_mul]

/-- The complete original causal Fourier channel is transported by its exact three-dimensional Jacobian. -/
theorem sourceCommonSpatialMoment_dilation (q : PhysicalResponsePoint) (c eta : ℝ)
    (_frequency : c≠0) (causal : 0<eta) (s : ℝ) (positive : 0<s) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceCommonSpatialMoment q (s*c) (s*eta) l r i 0 0 test x=
      sourceCommonSpatialMoment q c eta l r i 0 0 (sourceDilatedTest s positive.ne' test) (s • x) := by
  let f : PhysicalMomentum→ℂ:=fun n=>sourceSpatialPhase n x*test n*
    sourceCommonCausalChannel q (sourceSpatialMomentum n) (sourcePoleSide (s*c) (s*eta)) l r i
  let g : PhysicalMomentum→ℂ:=fun n=>sourceSpatialPhase n (s • x)*sourceDilatedTest s positive.ne' test n*
    sourceCommonCausalChannel q (sourceSpatialMomentum n) (sourcePoleSide c eta) l r i
  have point (n : PhysicalMomentum) : f (s • n)=((s:ℂ)⁻¹)^3*g n := by
    simp only [f,g,phase_radial,momentum_radial,side_radial,sourceDilatedTest_apply,
      sourceCompleteChannel_radial q _ (sourcePoleSide c eta) (by simpa [sourcePoleSide] using causal) s positive]
    ring
  have generated:=three_dimensional_change f g s positive 3 point
  have scalarNonzero : ((s:ℂ)⁻¹)^3≠0:=pow_ne_zero _ (inv_ne_zero (Complex.ofReal_ne_zero.mpr positive.ne'))
  have equal:=mul_left_cancel₀ scalarNonzero generated
  simpa only [sourceCommonSpatialMoment,sourceCommonMomentIntegrand,pow_zero,one_mul,f,g] using equal

/-- Both sides of the dilation are legal original Schwartz observations on the source causal side. -/
theorem sourceCommonDilation_integrable (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (causal : 0<eta) (s : ℝ) (positive : 0<s) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (sourceCommonMomentIntegrand q (s*c) (s*eta) l r i 0 0 test x) ∧
      Integrable (sourceCommonMomentIntegrand q c eta l r i 0 0 (sourceDilatedTest s positive.ne' test) (s • x)) :=
  ⟨sourceCommonMoment_integrable q (s*c) (s*eta) (mul_ne_zero positive.ne' frequency) (mul_pos positive causal) l r i 0 0 test x,
    sourceCommonMoment_integrable q c eta frequency causal l r i 0 0 (sourceDilatedTest s positive.ne' test) (s • x)⟩

open Lean Elab Term in
elab "paidDilationMaster% " id:ident : term => do
  let member:=id.getId
  unless member==`master_integrable || member==`master_channel_bound do
    throwError "Only the original master integrability or channel price payer is accepted"
  let wanted:=`LowEnergy.PreparationPhysicalRetainerResolventSquare ++ member
  let candidates:=(←getEnv).constants.toList.filter fun (name,_)=>
    name.toString.startsWith "_private.H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCausalMasterDerivative." && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>throwError "Expected unique original SourceCausalMasterDerivative payer {wanted}"

theorem sourceMasterDilation_integrable (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (causal : 0<eta) (s : ℝ) (positive : 0<s) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (fun n : PhysicalMomentum=>sourceSpatialPhase n x*test n*
      sourceMasterChannel q (sourceSpatialMomentum n) (sourcePoleSide (s*c) (s*eta)) l r i) ∧
    Integrable (fun n : PhysicalMomentum=>sourceSpatialPhase n (s • x)*test (s • n)*
      sourceMasterChannel q (sourceSpatialMomentum n) (sourcePoleSide c eta) l r i) := by
  constructor
  · exact (paidDilationMaster% master_integrable) q (s*c) (s*eta)
      (mul_ne_zero positive.ne' frequency) (mul_pos positive causal) l r i test x
  · exact (paidDilationMaster% master_integrable) q c eta frequency causal l r i
      (sourceDilatedTest s positive.ne' test) (s • x)

/-- The degree-minus-two master acquires the actual remaining spatial scale after the same Jacobian. -/
theorem sourceMasterSpatialChannel_dilation (q : PhysicalResponsePoint) (c eta : ℝ)
    (_frequency : c≠0) (causal : 0<eta) (s : ℝ) (positive : 0<s) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceMasterSpatialChannel q (sourcePoleSide (s*c) (s*eta)) l r i test x=
      (s:ℂ)*sourceMasterSpatialChannel q (sourcePoleSide c eta) l r i (sourceDilatedTest s positive.ne' test) (s • x) := by
  let f : PhysicalMomentum→ℂ:=fun n=>sourceSpatialPhase n x*test n*
    sourceMasterChannel q (sourceSpatialMomentum n) (sourcePoleSide (s*c) (s*eta)) l r i
  let g : PhysicalMomentum→ℂ:=fun n=>sourceSpatialPhase n (s • x)*sourceDilatedTest s positive.ne' test n*
    sourceMasterChannel q (sourceSpatialMomentum n) (sourcePoleSide c eta) l r i
  have point (n : PhysicalMomentum) : f (s • n)=((s:ℂ)⁻¹)^2*g n := by
    simp only [f,g,phase_radial,momentum_radial,side_radial,sourceDilatedTest_apply,
      sourceMasterChannel_radial q _ (sourcePoleSide c eta) (by simpa [sourcePoleSide] using causal) s positive]
    ring
  have generated:=three_dimensional_change f g s positive 2 point
  change (∫n,f n)=(s:ℂ)*(∫n,g n)
  apply mul_left_cancel₀ (pow_ne_zero 3 (inv_ne_zero (Complex.ofReal_ne_zero.mpr positive.ne')))
  rw [generated]
  field_simp

/-- Full289 and all three source columns pass through the same exact Fourier dilation. -/
theorem sourceCommonSpatialField_dilation (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (causal : 0<eta) (s : ℝ) (positive : 0<s) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceCommonSpatialField q (s*c) (s*eta) l r test x=
      sourceCommonSpatialField q c eta l r (sourceDilatedTest s positive.ne' test) (s • x) := by
  rw [sourceCommonSpatialField_generated q (s*c) (s*eta) (mul_ne_zero positive.ne' frequency) (mul_pos positive causal),
    sourceCommonSpatialField_generated q c eta frequency causal]
  simp only [sourceCommonSpatialMoment_dilation q c eta frequency causal s positive]

theorem sourceActualSpatialField_dilation (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (c eta : ℝ) (frequency : c≠0) (causal : 0<eta) (s : ℝ) (positive : 0<s)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualSpatialField q sL eL sR eR (s*c) (s*eta) test x=
      sourceActualSpatialField q sL eL sR eR c eta (sourceDilatedTest s positive.ne' test) (s • x) := by
  rw [sourceActualSpatialField_generated q sL eL sR eR (s*c) (s*eta)
    (mul_ne_zero positive.ne' frequency) (mul_pos positive causal),
    sourceActualSpatialField_generated q sL eL sR eR c eta frequency causal]
  simp only [sourceCommonSpatialField_dilation q c eta frequency causal s positive]

/-- The existing actual radial potential is exactly the fixed causal field acting on its generated dilated observation. -/
theorem sourceActualRadialPotential_dilation (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (branch : Fin 2) (negative : Bool) (eta : ℝ) (causal : 0<eta) (d : ℝ) (positive : 0<d)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualRadialPotential q sL eL sR eR branch negative eta d test x=
      sourceActualSpatialField q sL eL sR eR (sourceSignedSpeed branch negative) eta
        (sourceDilatedTest d positive.ne' test) (d • x) := by
  rw [sourceActualRadialPotential_return q sL eL sR eR branch negative eta causal d positive,
    sourceActualSpatialField_dilation q sL eL sR eR _ eta (sourceSignedSpeed_nonzero branch negative) causal d positive]

open PreparationPhysicalActualLegNormalization

/-- The independent actual unit-leg detector consumes the same full spatial dilation, with every original normalization and defect retained in its read. -/
theorem sourceActualUnitRadialPotential_dilation (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (causal : 0<eta) (d : ℝ) (positive : 0<d)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
      (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x)=
    sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
      (sourceActualSpatialField q sL eL sR eR (sourceSignedSpeed branch negative) eta
        (sourceDilatedTest d positive.ne' test) (d • x)) := by
  rw [sourceActualRadialPotential_dilation q sL eL sR eR branch negative eta causal d positive]

end LowEnergy.PreparationPhysicalCausalSpatialDilation
