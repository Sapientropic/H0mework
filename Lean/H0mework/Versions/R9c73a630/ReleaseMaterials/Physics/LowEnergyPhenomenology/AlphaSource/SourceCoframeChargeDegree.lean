import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCoframePreparedPotential

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCoframeChargeSelection
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
local instance CoframeChargeIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
open PreparationPhysicalMasterCorrectionReturn PreparationPhysicalPhaseGaugeRealization
open PreparationPhysicalGaugeSeedNull PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets
open PreparationPhysicalActionSeedReduction PreparationVacuumLowerClassical PreparationVacuumJointFieldResponse
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open GaussCoreDifferential GaussCoreLabel NativeHistoryGrade GaussFockLabel GaussYukawaGrade
open PreparationVacuumPropagationPencil PreparationVacuumRawJointFeedback
open PreparationVacuumPhysicalNumberOneRead PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumPhysicalGradeZeroRead
open PreparationPhysicalLorentzSeedReturn
open PreparationVacuumYukawaTransport

open PreparationPhysicalTriangularSeedReturn PreparationVacuumPhysicalModeContact
open PreparationVacuumPhysicalGaussMaterialContact PreparationVacuumNativeLocalWard
open SourceQuantumResidualGaugeSlice SourceQuantumScalarChart


open PreparationPhysicalOriginConfigurationReturn PreparationVacuumRestModeCoupling
open PreparationPhysicalActionUnits

open PreparationPhysicalCoframeOriginPolynomial
open Stage9DEF Stage9DEF.Compatibility Stage10.ChargedPreparation.Dynamics
open GaussQuantumMultiplier GaussFockLift CanonicalGradedCharge

open PreparationPhysicalCoframePreparedReturn PreparationPhysicalActualGaussChargeCurrent
open PreparationPhysicalNativePhaseChargeInventory PreparationVacuumPhysicalGaussMaterialContact
open PreparationVacuumNativeFieldInjection StageNineP286GaugeAuxiliaryVariation StageNineCoframeGravityGaugeRegularity
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

local instance : DecidableEq Mode:=Classical.decEq _

private abbrev primalCharge : SourceMatrix :=
  Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)

/-- The same full252 phase charge retains the original native gauge generator and its entire hypercharge/phase difference. -/
theorem sourceCoframeCharge_nativeDifference :
    Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)=
      Complex.I • nativePrimal sourcePhaseGaugeLie+
        Complex.I • Quantum.operatorMatrix sourcePhaseGaugeDifference := by
  rw [sourcePhaseNoether_canonical,map_smul,sourcePhaseGaugeGenerator_full,map_add,smul_add,
    sourcePhaseGaugeGenerator_native]

open Lean Elab Term in
elab "paidCoframePhaseMatrix%" member:ident : term => do
  let tag:=member.getId.toString
  unless tag=="operatorMatrix_sub" || tag=="operatorMatrix_neg" do
    throwError "Closed original phase-matrix payer whitelist"
  let wanted:=Name.str `LowEnergy.PreparationPhysicalPhaseGaugeRealization tag
  let all:=(←getEnv).constants.toList
  let candidates:=all.filter fun (name,_)=>name.toString.startsWith "_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhaseGaugeGenerator." && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>throwError "Expected unique original SourcePhaseGaugeGenerator phase-matrix payer; actual candidates: {all.filterMap (fun (name,_)=>if privateToUserName name==wanted then some name else none)}"

/-- The central half-matter phase is derived from the actual X, not replaced by a native hypercharge eigenvalue. -/
theorem sourceCoframeCharge_primal :
    Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)=
      -Complex.I • nativePrimal (colorGenerator 2)+(1/2:ℂ) • (1:SourceMatrix) := by
  rw [sourceCoframeCharge_nativeDifference,←sourcePhaseGaugeGenerator_native,←smul_add,←map_add,
    ←sourcePhaseGaugeGenerator_full]
  have colour : Quantum.operatorMatrix
      (diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator 2)))=
        nativePrimal (colorGenerator 2) := by
    change _=Quantum.operatorMatrix (diracExteriorMotherLieAction
      (p286LieBlockEmbed (p286CoordinateEquiv.symm (p286CoordinateEquiv (sourceColorP286Generator 2)))))
    rw [LinearEquiv.symm_apply_apply]
  unfold sourceNativeOriginGenerator
  rw [paidCoframePhaseMatrix% operatorMatrix_sub,paidCoframePhaseMatrix% operatorMatrix_neg,map_smul,colour]
  have identity : Quantum.operatorMatrix (LinearMap.id : Module.End ℂ DiracExteriorMatterCarrier)=1:=map_one Quantum.operatorMatrix
  rw [identity]
  change Complex.I • (-nativePrimal (colorGenerator 2)-(Complex.I/2) • (1:SourceMatrix))=_
  simp only [smul_sub,smul_neg,smul_smul]
  have ii : Complex.I*(Complex.I/2)=-(1/2:ℂ) := by rw [←mul_div_assoc,Complex.I_mul_I];ring
  rw [ii,neg_smul]
  module

private def ad (C : SourceMatrix) : SourceMatrix→ₗ[ℂ]SourceMatrix where
  toFun A:=C*A-A*C
  map_add' A B:=by simp only [mul_add,add_mul];abel
  map_smul' c A:=by simp only [mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

private theorem colour_zero :
    ad (nativePrimal (colorGenerator 2)) (nativePrimal (colorGenerator 0))=
      -nativePrimal (colorGenerator 1) := by
  have bracket : (show NativeLie from p286CoordinateLieBracket (colorGenerator 2) (colorGenerator 0))=
      -colorGenerator 1 := by
    change jointP286CoordinateLieBracket _ _=_
    rw [colorGenerator_bracket]
    rfl
  have original:=originalGauge_commutator (colorGenerator 2) (colorGenerator 0)
  rw [bracket,map_neg] at original
  exact original.symm

private theorem colour_one :
    ad (nativePrimal (colorGenerator 2)) (nativePrimal (colorGenerator 1))=
      nativePrimal (colorGenerator 0) := by
  have bracket : (show NativeLie from p286CoordinateLieBracket (colorGenerator 2) (colorGenerator 1))=
      colorGenerator 0 := by
    change jointP286CoordinateLieBracket _ _=_
    rw [colorGenerator_bracket]
    rfl
  have original:=originalGauge_commutator (colorGenerator 2) (colorGenerator 1)
  rw [bracket] at original
  exact original.symm

private theorem ad_factor (C B A : SourceMatrix) (commute : C*B=B*C) :
    ad C (B*A)=B*ad C A := by
  change C*(B*A)-(B*A)*C=B*(C*A-A*C)
  rw [←mul_assoc C B,commute]
  noncomm_ring

private theorem spin_density_commute (mu : Fin 4) :
    Commute (nativePrimal (colorGenerator 2)) (densityActionMatrix*sourceCoframeModeGamma mu) := by
  have density : Commute (nativePrimal (colorGenerator 2)) densityActionMatrix := by
    rw [sourceDensityActionMatrix_momentum]
    change _*((ActionNormalization.phaseMomentum:ℂ) • Quantum.operatorMatrix flipMatter)=
      ((ActionNormalization.phaseMomentum:ℂ) • Quantum.operatorMatrix flipMatter)*_
    rw [mul_smul_comm,smul_mul_assoc,sourceColour_flip.eq]
  have gamma : Commute (nativePrimal (colorGenerator 2)) (sourceCoframeModeGamma mu) := by
    have h:=GaussMatterCore.spin_native_commute (diracGamma mu) (colorGenerator 2)
    rw [←GaussCoframeSpin.spinLift_source] at h
    change spinCoordinates (diracGamma mu)*nativePrimal (colorGenerator 2)=
      nativePrimal (colorGenerator 2)*spinCoordinates (diracGamma mu) at h
    change _*(Complex.I • spinCoordinates (diracGamma mu))=(Complex.I • spinCoordinates (diracGamma mu))*_
    rw [mul_smul_comm,smul_mul_assoc,h]
  exact density.mul_right gamma

private theorem matrix_colour_square (mu : Fin 4) (a : Fin 2) :
    ad (nativePrimal (colorGenerator 2)) (ad (nativePrimal (colorGenerator 2))
      (densityActionMatrix*(sourceCoframeModeGamma mu*nativePrimal (colorGenerator a.castSucc))))=
        -(densityActionMatrix*(sourceCoframeModeGamma mu*nativePrimal (colorGenerator a.castSucc))) := by
  rw [←mul_assoc,ad_factor _ _ _ (spin_density_commute mu).eq,ad_factor _ _ _ (spin_density_commute mu).eq]
  fin_cases a
  · change _*(ad _ (ad _ (nativePrimal (colorGenerator 0))))=_
    rw [colour_zero,map_neg,colour_one,mul_neg]
    rfl
  · change _*(ad _ (ad _ (nativePrimal (colorGenerator 1))))=_
    rw [colour_one,colour_zero,mul_neg]
    rfl

private theorem fixed_colour_square (k : Fin 3) :
    ad (nativePrimal (colorGenerator 2)) (ad (nativePrimal (colorGenerator 2)) (sourceCoframeModeMatrix k))=
      -sourceCoframeModeMatrix k := by
  fin_cases k
  · exact matrix_colour_square 1 1
  · exact matrix_colour_square 1 0
  · exact matrix_colour_square 2 0

private theorem coefficient_colour_square (z : SourceCoordinateSlice) :
    ad (nativePrimal (colorGenerator 2)) (ad (nativePrimal (colorGenerator 2)) (sourceCoframeModeCoefficient z))=
      -sourceCoframeModeCoefficient z := by
  unfold sourceCoframeModeCoefficient
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  simp only [map_smul,map_add,map_sub,fixed_colour_square,smul_neg]
  module

private theorem charge_ad (A : SourceMatrix) :
    ad primalCharge A=(-Complex.I) • ad (nativePrimal (colorGenerator 2)) A := by
  change ad (Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)) A=_
  rw [sourceCoframeCharge_primal]
  simp only [ad,LinearMap.coe_mk,AddHom.coe_mk,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
    one_mul,mul_one,smul_sub]
  module

/-- The complete original primal coframe matrix has source charge degree one. -/
theorem sourceCoframeCharge_matrix (z : SourceCoordinateSlice) :
    primalCharge*(primalCharge*sourceCoframeModeCoefficient z-sourceCoframeModeCoefficient z*primalCharge)-
      (primalCharge*sourceCoframeModeCoefficient z-sourceCoframeModeCoefficient z*primalCharge)*primalCharge=
        sourceCoframeModeCoefficient z := by
  change ad primalCharge (ad primalCharge (sourceCoframeModeCoefficient z))=_
  rw [charge_ad,charge_ad,map_smul,smul_smul,coefficient_colour_square]
  have ii : (-Complex.I)*(-Complex.I)=-(1:ℂ) := by rw [neg_mul_neg,Complex.I_mul_I]
  rw [ii,neg_smul,one_smul,neg_neg]

private theorem blocks_sub (A B C D : SourceMatrix) :
    Matrix.fromBlocks A 0 0 B-Matrix.fromBlocks C 0 0 D=Matrix.fromBlocks (A-C) 0 0 (B-D) := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks]

/-- Both independent branches are paid together; no selected prepared block replaces the full504 symbol. -/
theorem sourceCoframeCharge_symbol (z : SourceCoordinateSlice) :
    sourceActualGaussChargeMatrix*(sourceActualGaussChargeMatrix*sourceCoframeModeSymbol z-
      sourceCoframeModeSymbol z*sourceActualGaussChargeMatrix)-
      (sourceActualGaussChargeMatrix*sourceCoframeModeSymbol z-sourceCoframeModeSymbol z*sourceActualGaussChargeMatrix)*
        sourceActualGaussChargeMatrix=sourceCoframeModeSymbol z := by
  have primal:=sourceCoframeCharge_matrix z
  have dual:=congrArg (fun A : SourceMatrix=>A.map (starRingEnd ℂ)) primal
  simp only [Matrix.map_sub _ (fun a b=>map_sub (starRingEnd ℂ) a b),Matrix.map_mul] at dual
  rw [sourceCoframeSymbol_branches]
  change Matrix.fromBlocks primalCharge 0 0 (-(primalCharge.map (starRingEnd ℂ)))*
    (Matrix.fromBlocks primalCharge 0 0 (-(primalCharge.map (starRingEnd ℂ)))*
      Matrix.fromBlocks (sourceCoframeModeCoefficient z) 0 0 ((sourceCoframeModeCoefficient z).map (starRingEnd ℂ))-
    Matrix.fromBlocks (sourceCoframeModeCoefficient z) 0 0 ((sourceCoframeModeCoefficient z).map (starRingEnd ℂ))*
      Matrix.fromBlocks primalCharge 0 0 (-(primalCharge.map (starRingEnd ℂ))))-
    (Matrix.fromBlocks primalCharge 0 0 (-(primalCharge.map (starRingEnd ℂ)))*
      Matrix.fromBlocks (sourceCoframeModeCoefficient z) 0 0 ((sourceCoframeModeCoefficient z).map (starRingEnd ℂ))-
    Matrix.fromBlocks (sourceCoframeModeCoefficient z) 0 0 ((sourceCoframeModeCoefficient z).map (starRingEnd ℂ))*
      Matrix.fromBlocks primalCharge 0 0 (-(primalCharge.map (starRingEnd ℂ))))*
    Matrix.fromBlocks primalCharge 0 0 (-(primalCharge.map (starRingEnd ℂ)))=_
  simp only [Matrix.fromBlocks_multiply,zero_mul,mul_zero,add_zero,zero_add,blocks_sub,
    neg_mul,mul_neg,neg_zero]
  rw [primal]
  congr 1
  convert dual using 1
  noncomm_ring

open Lean Elab Term in
elab "paidCoframeQuantizerComm%" : term => do
  let wanted:=`LowEnergy.PreparationVacuumPhysicalGaussMaterialContact.quantizer_commutator
  let all:=(←getEnv).constants.toList
  let candidates:=all.filter fun (name,_)=>name.toString.startsWith
    "_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationActualQuantumMaterialWard." && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>throwError "Expected unique original ActualQuantumMaterialWard.quantizer_commutator; actual candidates: {all.filterMap (fun (name,_)=>if privateToUserName name==wanted then some name else none)}"

/-- The actual source charge selection law reaches complete full CAR, including every previously retained input complement. -/
theorem sourceCoframeCharge_fiber (z : SourceCoordinateSlice) :
    quantized sourceActualGaussChargeMatrix*(quantized sourceActualGaussChargeMatrix*sourceCoframeModeFiber z-
      sourceCoframeModeFiber z*quantized sourceActualGaussChargeMatrix)-
      (quantized sourceActualGaussChargeMatrix*sourceCoframeModeFiber z-sourceCoframeModeFiber z*quantized sourceActualGaussChargeMatrix)*
        quantized sourceActualGaussChargeMatrix=sourceCoframeModeFiber z := by
  have generated:=congrArg quantizer (sourceCoframeCharge_symbol z)
  simp only [paidCoframeQuantizerComm%] at generated
  exact generated

end LowEnergy.PreparationPhysicalCoframeChargeSelection
