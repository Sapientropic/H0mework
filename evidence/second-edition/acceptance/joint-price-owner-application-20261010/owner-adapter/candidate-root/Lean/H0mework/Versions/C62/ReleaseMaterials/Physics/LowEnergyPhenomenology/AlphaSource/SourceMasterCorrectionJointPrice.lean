import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceMasterSimpleNumerator

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalMasterCorrectionReturn
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
local instance CorrectionPriceIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
open PreparationPhysicalCausalSpatialDilation
attribute [local irreducible] sourceMasterCurrent sourceMasterNative sourceNativeReaderFirst sourcePoleRead

open Lean Elab Term in
elab "paidCorrectionGeometry% " id:ident : term => do
  let member:=id.getId
  let (owner,namespaceName)←
    if member==`spatial_positive then pure ("_private.H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointRadialSpatialReturn.",`LowEnergy.PreparationPhysicalJointRadialForcing)
    else if member==`physical_price_shape then pure ("_private.H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointRadialPrice.",`LowEnergy.PreparationPhysicalJointRadialForcing)
    else throwError "Only original source spatial positivity and physical price shape are accepted"
  let wanted:=namespaceName ++ member
  let candidates:=(←getEnv).constants.toList.filter fun (name,_)=>name.toString.startsWith owner && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>throwError "Expected unique original source geometry payer {wanted}"

private theorem side_scaled (c eta d : ℝ) : sourcePoleSide (d*c) (d*eta)=(d:ℂ)*sourcePoleSide c eta := by
  simp only [sourcePoleSide,Complex.ofReal_mul]
  ring

private theorem price_scaled (c eta d : ℝ) (i : Fin 3) :
    sourceChargedDenominatorPrice (d*c) (d*eta) i=d⁻¹^2*sourceChargedDenominatorPrice c eta i := by
  unfold sourceChargedDenominatorPrice
  rw [show 2*sourceChargedTemporalCoefficient i*(d*eta)*(d*c)=d^2*(2*sourceChargedTemporalCoefficient i*eta*c) by ring,
    abs_mul,abs_of_nonneg (sq_nonneg d),mul_inv_rev,inv_pow]
  ring

/-- The original whole-momentum price controls the small momentum layer of every causal channel. -/
theorem sourceCorrectionInverse_small (n : PhysicalMomentum) (c eta : ℝ) (frequency : c≠0)
    (causal : 0<eta) (d : ℝ) (radial : 0<d) (i : Fin 3) :
    d^2*‖(sourceChargedDenominator n ((d:ℂ)*sourcePoleSide c eta) i)⁻¹‖≤ sourceChargedDenominatorPrice c eta i := by
  have paid:=sourceChargedDenominator_bound n (d*c) (d*eta) (mul_ne_zero radial.ne' frequency) (mul_pos radial causal) i
  rw [price_scaled,side_scaled] at paid
  exact (mul_le_mul_of_nonneg_left paid (sq_nonneg d)).trans_eq (by field_simp)

/-- Both original source budgets jointly control the complete moving transition layer without excluding any angle. -/
theorem sourceCorrectionInverse_joint (n : PhysicalMomentum) (c eta : ℝ) (frequency : c≠0)
    (causal : 0<eta) (d : ℝ) (radial : 0<d) (i : Fin 3) :
    d*(d*‖sourcePoleSide c eta‖+‖n‖)*‖(sourceChargedDenominator n ((d:ℂ)*sourcePoleSide c eta) i)⁻¹‖≤
      (‖sourcePoleSide c eta‖+1)*sourceChargedDenominatorPrice c eta i+sourceChargedQuadraticPrice c eta i := by
  let inverse:=‖(sourceChargedDenominator n ((d:ℂ)*sourcePoleSide c eta) i)⁻¹‖
  have small:=sourceCorrectionInverse_small n c eta frequency causal d radial i
  have large:=sourceJointRadialInverse_bound n c eta frequency causal d radial i
  rw [side_scaled] at large
  have mixed : d*‖n‖≤ d^2+‖n‖^2:=by nlinarith [sq_nonneg (d-‖n‖)]
  calc
    _=‖sourcePoleSide c eta‖*(d^2*inverse)+(d*‖n‖)*inverse:=by dsimp only [inverse];ring
    _≤‖sourcePoleSide c eta‖*sourceChargedDenominatorPrice c eta i+(d^2+‖n‖^2)*inverse:=
      add_le_add (mul_le_mul_of_nonneg_left small (norm_nonneg _))
        (mul_le_mul_of_nonneg_right mixed (norm_nonneg _))
    _≤‖sourcePoleSide c eta‖*sourceChargedDenominatorPrice c eta i+
        (sourceChargedDenominatorPrice c eta i+sourceChargedQuadraticPrice c eta i):=by
      rw [add_mul]
      exact add_le_add (le_refl _) (add_le_add small large)
    _=_:=by ring

private theorem slow_smul (z : ℂ) (v : Fin 289→ℂ) (i : Fin 5) : sourceSlowRead (z • v) i=z*sourceSlowRead v i := by
  simp only [sourceSlowRead,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> simp only [mul_zero]

private theorem slow_continuous (i : Fin 5) : Continuous (fun v : Fin 289→ℂ=>sourceSlowRead v i) := by
  unfold sourceSlowRead
  split_ifs <;> fun_prop

def sourceDenominatorCorrection (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (i : Fin 3) : ℂ :=
  (2*(sourceChargedTemporalCoefficient i:ℂ)*zeta)*((sourceChargedDenominator n zeta i)⁻¹)^2*
    sourceSlowRead (sourceMasterNative q n zeta l r) ⟨i.val,by omega⟩

private theorem scaled_master_native (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (d : ℝ) :
    (d:ℂ) • sourceMasterNative q n ((d:ℂ)*zeta) l r=
      sourceNativeReaderFirst (fixedMomentum n ((d:ℂ)*zeta))*ᵥ((d:ℂ) • sourceMasterCurrent q n ((d:ℂ)*zeta) l r) := by
  simp only [sourceMasterNative,Matrix.mulVec_smul]

private theorem scaled_native_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (d : ℝ) (radial : 0<d) (l r : RestStateIndex) :
    ‖(d:ℂ) • sourceMasterNative q n ((d:ℂ)*zeta) l r‖≤
      ‖sourceReaderLinear‖*(d*‖zeta‖+‖n‖)*(sourceMasterCurrentPrice q l r/zeta.re) := by
  rw [scaled_master_native]
  have reader:=sourceReaderLinear_bound n ((d:ℂ)*zeta)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos radial] at reader
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul reader (sourceMasterCurrent_simple_bound q n zeta causal d radial l r) (norm_nonneg _) (by positivity))

private theorem normalized_denominator (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (i : Fin 3) (d : ℝ) :
    (d:ℂ)*sourceDenominatorCorrection q n ((d:ℂ)*zeta) l r i=
      (2*(sourceChargedTemporalCoefficient i:ℂ)*zeta)*((sourceChargedDenominator n ((d:ℂ)*zeta) i)⁻¹)^2*
        ((d:ℂ)*sourceSlowRead ((d:ℂ) • sourceMasterNative q n ((d:ℂ)*zeta) l r) ⟨i.val,by omega⟩) := by
  simp only [sourceDenominatorCorrection,slow_smul]
  ring

def sourceDenominatorCorrectionPrice (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex) (i : Fin 3) : ℝ :=
  ‖2*(sourceChargedTemporalCoefficient i:ℂ)*sourcePoleSide c eta‖*‖slowFastFrame.transpose‖*‖sourceReaderLinear‖*
    (sourceMasterCurrentPrice q l r/eta)*
      ((‖sourcePoleSide c eta‖+1)*sourceChargedDenominatorPrice c eta i+sourceChargedQuadraticPrice c eta i)*
        sourceChargedQuadraticPrice c eta i

private theorem correction_price_nonneg (q : PhysicalResponsePoint) (c eta : ℝ) (causal : 0<eta)
    (l r : RestStateIndex) (i : Fin 3) : 0≤ sourceDenominatorCorrectionPrice q c eta l r i := by
  unfold sourceDenominatorCorrectionPrice sourceMasterCurrentPrice sourceChargedQuadraticPrice sourceChargedDenominatorPrice
  have spatial:=(sourceChargedSpatialCoefficient_positive i).le
  positivity

/-- The normalized derivative-of-denominator term has a source-generated inverse-square momentum bound. -/
theorem sourceDenominatorCorrection_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum) (nonzero : n≠0)
    (c eta : ℝ) (frequency : c≠0) (causal : 0<eta) (d : ℝ) (radial : 0<d)
    (l r : RestStateIndex) (i : Fin 3) :
    ‖(d:ℂ)*sourceDenominatorCorrection q n ((d:ℂ)*sourcePoleSide c eta) l r i‖≤
      sourceDenominatorCorrectionPrice q c eta l r i*(‖n‖^2)⁻¹ := by
  let zeta:=sourcePoleSide c eta
  let inverse:=‖(sourceChargedDenominator n ((d:ℂ)*zeta) i)⁻¹‖
  have zp : 0<zeta.re:=by simpa [zeta,sourcePoleSide] using causal
  have real : zeta.re=eta:=by simp [zeta,sourcePoleSide]
  have native:=scaled_native_bound q n zeta zp d radial l r
  rw [real] at native
  have slow:=(paidSpatial% slow_bound) ((d:ℂ) • sourceMasterNative q n ((d:ℂ)*zeta) l r) ⟨i.val,by omega⟩
  have joint:=sourceCorrectionInverse_joint n c eta frequency causal d radial i
  have large:=sourceJointRadialInverse_bound n c eta frequency causal d radial i
  rw [side_scaled] at large
  have normPositive : 0<‖n‖^2:=sq_pos_of_pos (norm_pos_iff.mpr nonzero)
  have inverseBound : inverse≤ sourceChargedQuadraticPrice c eta i*(‖n‖^2)⁻¹ := by
    rw [←div_eq_mul_inv]
    exact (le_div_iff₀ normPositive).mpr (by simpa only [mul_comm] using large)
  have currentNonneg : 0≤ sourceMasterCurrentPrice q l r/eta := by unfold sourceMasterCurrentPrice;positivity
  have jointNonneg : 0≤(‖zeta‖+1)*sourceChargedDenominatorPrice c eta i+sourceChargedQuadraticPrice c eta i := by
    unfold sourceChargedQuadraticPrice sourceChargedDenominatorPrice
    have spatial:=(sourceChargedSpatialCoefficient_positive i).le
    positivity
  rw [normalized_denominator]
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos radial]
  calc
    _≤‖(2:ℂ)‖*‖(sourceChargedTemporalCoefficient i:ℂ)‖*‖zeta‖*inverse^2*
      (d*(‖slowFastFrame.transpose‖*(‖sourceReaderLinear‖*(d*‖zeta‖+‖n‖)*(sourceMasterCurrentPrice q l r/eta)))) := by
      simp only [Complex.norm_real,Real.norm_eq_abs,zeta]
      gcongr
      exact slow.trans (mul_le_mul_of_nonneg_left native (norm_nonneg _))
    _=(‖2*(sourceChargedTemporalCoefficient i:ℂ)*zeta‖*‖slowFastFrame.transpose‖*‖sourceReaderLinear‖*
      (sourceMasterCurrentPrice q l r/eta))*(d*(d*‖zeta‖+‖n‖)*inverse)*inverse := by rw [norm_mul,norm_mul];ring
    _≤(‖2*(sourceChargedTemporalCoefficient i:ℂ)*zeta‖*‖slowFastFrame.transpose‖*‖sourceReaderLinear‖*
      (sourceMasterCurrentPrice q l r/eta))*
      ((‖zeta‖+1)*sourceChargedDenominatorPrice c eta i+sourceChargedQuadraticPrice c eta i)*
        (sourceChargedQuadraticPrice c eta i*(‖n‖^2)⁻¹) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left joint (by positivity)) inverseBound (norm_nonneg _) (by positivity)
    _=_:=by unfold sourceDenominatorCorrectionPrice;dsimp only [zeta];ring

/-- The same causal inverse has its static spatial limit at every nonzero physical momentum. -/
theorem sourceCorrectionInverse_return (n : PhysicalMomentum) (nonzero : n≠0) (zeta : ℂ) (i : Fin 3) :
    Tendsto (fun d : ℝ=>(sourceChargedDenominator n ((d:ℂ)*zeta) i)⁻¹) (𝓝[>] 0)
      (𝓝 ((sourceChargedDenominator n 0 i)⁻¹)) := by
  have denominatorNZ : sourceChargedDenominator n 0 i≠0 := by
    simp only [sourceChargedDenominator,zero_pow (by omega : 2≠0),mul_zero,add_zero]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (sourceChargedSpatialCoefficient_positive i).ne')
      (Complex.ofReal_ne_zero.mpr ((paidCorrectionGeometry% spatial_positive) n nonzero).ne')
  have continuous : Continuous (fun d : ℝ=>sourceChargedDenominator n ((d:ℂ)*zeta) i) := by unfold sourceChargedDenominator;fun_prop
  have generated:=(continuous.continuousAt (x:=0)).tendsto
  simp only [Complex.ofReal_zero,zero_mul] at generated
  exact (generated.inv₀ denominatorNZ).mono_left nhdsWithin_le_nhds

private theorem scaled_native_return (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (l r : RestStateIndex) :
    Tendsto (fun d : ℝ=>(d:ℂ) • sourceMasterNative q n ((d:ℂ)*zeta) l r) (𝓝[>] 0)
      (𝓝 (sourceNativeReaderFirst (fixedMomentum n 0)*ᵥ(-(zeta⁻¹ • sourceStaticCurrent q n l r)))) := by
  have readerContinuous : Continuous (fun d : ℝ=>sourceNativeReaderFirst (fixedMomentum n ((d:ℂ)*zeta))) := by
    simp_rw [←sourceReaderLinear_generated]
    apply sourceReaderLinear.continuous.comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · change Continuous (fun d : ℝ=>(d:ℂ)*zeta)
      fun_prop
    · change Continuous (fun _d : ℝ=>Complex.I*(n j:ℂ))
      exact continuous_const
  have reader:=((readerContinuous.continuousAt (x:=0)).tendsto).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  simp only [Complex.ofReal_zero,zero_mul] at reader
  have current:=sourceMasterCurrent_simple q n zeta causal l r
  have generated:=(continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp (reader.prodMk_nhds current)
  simpa only [Function.comp_def,scaled_master_native] using generated

theorem sourceDenominatorCorrection_return (q : PhysicalResponsePoint) (n : PhysicalMomentum) (nonzero : n≠0)
    (zeta : ℂ) (causal : 0<zeta.re) (l r : RestStateIndex) (i : Fin 3) :
    Tendsto (fun d : ℝ=>(d:ℂ)*sourceDenominatorCorrection q n ((d:ℂ)*zeta) l r i) (𝓝[>] 0) (𝓝 0) := by
  have scalar : Tendsto (fun d : ℝ=>(d:ℂ)) (𝓝[>] 0) (𝓝 (0:ℂ)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have native:=(slow_continuous ⟨i.val,by omega⟩).continuousAt.tendsto.comp (scaled_native_return q n zeta causal l r)
  have inverse:=sourceCorrectionInverse_return n nonzero zeta i
  have generated:=((inverse.pow 2).const_mul (2*(sourceChargedTemporalCoefficient i:ℂ)*zeta)).mul (scalar.mul native)
  simpa only [zero_mul,mul_zero,Function.comp_def,←normalized_denominator] using generated

private theorem denominator_continuous (q : PhysicalResponsePoint) (c eta : ℝ) (frequency : c≠0)
    (causal : 0<eta) (l r : RestStateIndex) (i : Fin 3) :
    Continuous (fun n : PhysicalMomentum=>sourceDenominatorCorrection q n (sourcePoleSide c eta) l r i) := by
  have inverse : Continuous (fun n : PhysicalMomentum=>(sourceChargedDenominator n (sourcePoleSide c eta) i)⁻¹) := by
    have base : Continuous (fun n : PhysicalMomentum=>sourceChargedDenominator n (sourcePoleSide c eta) i):=by unfold sourceChargedDenominator spatialSquare;fun_prop
    exact base.inv₀ (fun n=>sourceChargedDenominator_nonzero n c eta frequency causal i)
  have zp : 0<(sourcePoleSide c eta).re:=by simpa [sourcePoleSide] using causal
  have current:=(paidCorrectionMaster% master_current_continuous) q (sourcePoleSide c eta) zp l r
  have reader : Continuous (fun n : PhysicalMomentum=>sourceNativeReaderFirst (fixedMomentum n (sourcePoleSide c eta))) := by
    simp_rw [←sourceReaderLinear_generated]
    exact sourceReaderLinear.continuous.comp ((paidSpatial% physical_point_continuous) (sourcePoleSide c eta))
  have native:=reader.matrix_mulVec current
  have slow:=(slow_continuous ⟨i.val,by omega⟩).comp native
  apply ((continuous_const (y:=2*(sourceChargedTemporalCoefficient i:ℂ)*sourcePoleSide c eta)).mul (inverse.pow 2) |>.mul slow).congr
  intro n
  simp only [Pi.mul_apply,Pi.pow_apply,Function.comp_def,sourceDenominatorCorrection,sourceMasterNative]

theorem sourceDenominatorCorrection_fourier_bound (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (causal : 0<eta) (d : ℝ) (radial : 0<d) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x n : PhysicalMomentum) (nonzero : n≠0) :
    ‖sourceSpatialPhase n x*test n*((d:ℂ)*sourceDenominatorCorrection q (sourceSpatialMomentum n)
      ((d:ℂ)*sourcePoleSide c eta) l r i)‖≤ sourceDenominatorCorrectionPrice q c eta l r i*sourceRadialSchwartzPrice test n := by
  have momentumNZ : sourceSpatialMomentum n≠0:=by unfold sourceSpatialMomentum;exact smul_ne_zero (by positivity : (2*Real.pi:ℝ)≠0) nonzero
  have bound:=sourceDenominatorCorrection_bound q (sourceSpatialMomentum n) momentumNZ c eta frequency causal d radial l r i
  have price:=correction_price_nonneg q c eta causal l r i
  have extra : (‖sourceSpatialMomentum n‖^2)⁻¹≤(1+‖sourceSpatialMomentum n‖)*(‖sourceSpatialMomentum n‖^2)⁻¹ :=
    le_mul_of_one_le_left (by positivity) (by linarith [norm_nonneg (sourceSpatialMomentum n)])
  rw [norm_mul,norm_mul,(paidRadialGreen% phase_norm),one_mul]
  calc
    _≤‖test n‖*(sourceDenominatorCorrectionPrice q c eta l r i*(‖sourceSpatialMomentum n‖^2)⁻¹):=
      mul_le_mul_of_nonneg_left bound (norm_nonneg _)
    _≤‖test n‖*(sourceDenominatorCorrectionPrice q c eta l r i*((1+‖n‖)*(‖n‖^2)⁻¹)):=by
      gcongr
      exact extra.trans ((paidCorrectionGeometry% physical_price_shape) n nonzero)
    _=_:=by unfold sourceRadialSchwartzPrice;ring

/-- The original derivative-of-field-denominator correction vanishes in the whole actual spatial simple normalization. -/
theorem sourceDenominatorCorrection_spatial_zero (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (causal : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>∫n : PhysicalMomentum,sourceSpatialPhase n x*test n*((d:ℂ)*
      sourceDenominatorCorrection q (sourceSpatialMomentum n) ((d:ℂ)*sourcePoleSide c eta) l r i))
      (𝓝[>] 0) (𝓝 0) := by
  have aenonzero : ∀ᵐ n : PhysicalMomentum ∂volume,n≠0:=by rw [ae_iff];simp
  have zeroIntegral : (∫_n : PhysicalMomentum,(0:ℂ))=0:=integral_zero _ _
  rw [←zeroIntegral]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun n=>sourceDenominatorCorrectionPrice q c eta l r i*sourceRadialSchwartzPrice test n)
  · filter_upwards [self_mem_nhdsWithin] with d dp
    have kernel:=(denominator_continuous q (d*c) (d*eta) (mul_ne_zero dp.ne' frequency) (mul_pos dp causal) l r i)
    have momentum : Continuous sourceSpatialMomentum:=by unfold sourceSpatialMomentum;fun_prop
    have complete : Continuous (fun n : PhysicalMomentum=>sourceSpatialPhase n x*test n*((d:ℂ)*
        sourceDenominatorCorrection q (sourceSpatialMomentum n) ((d:ℂ)*sourcePoleSide c eta) l r i)) := by
      rw [←side_scaled]
      have composed:=kernel.comp momentum
      unfold sourceSpatialPhase
      fun_prop
    exact complete.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with d dp
    filter_upwards [aenonzero] with n nz
    exact sourceDenominatorCorrection_fourier_bound q c eta frequency causal d dp l r i test x n nz
  · exact (sourceRadialSchwartzPrice_integrable test).const_mul _
  · filter_upwards [aenonzero] with n nz
    have momentumNZ : sourceSpatialMomentum n≠0:=by unfold sourceSpatialMomentum;exact smul_ne_zero (by positivity : (2*Real.pi:ℝ)≠0) nz
    have zp : 0<(sourcePoleSide c eta).re:=by simpa [sourcePoleSide] using causal
    simpa only [mul_zero] using (sourceDenominatorCorrection_return q (sourceSpatialMomentum n) momentumNZ
      (sourcePoleSide c eta) zp l r i).const_mul (sourceSpatialPhase n x*test n)

end LowEnergy.PreparationPhysicalMasterCorrectionReturn
