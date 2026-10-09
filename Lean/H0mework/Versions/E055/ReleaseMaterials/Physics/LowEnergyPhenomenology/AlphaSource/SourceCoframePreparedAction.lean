import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCoframeConfigurationPotential

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCoframePreparedReturn
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
local instance CoframePreparedIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open StageNineFullDiracAdjointMaterial SU7MotherGaugeTheory SU7ExteriorMatterRepresentation
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
local instance : DecidableEq Mode:=Classical.decEq _

/-- The other member of the same actual two-edge preparation; the source side is retained. -/
def sourceCoframeOtherEdge (edge : Fin 2) : Fin 2 := if edge=0 then 1 else 0

/-- These signs are computed from the actual gamma/colour matrices, before the source action scale. -/
def sourceCoframeFixedFactor (k : Fin 3) (edge : Fin 2) : ℂ :=
  if k=1 then -(1/2:ℂ) else if edge=0 then -Complex.I/2 else Complex.I/2

private def sourceCoframeMother (k : Fin 3) : Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I • (diracMatrixMatterAction
    (diracAdjointSpinSwap*diracGamma (if k=2 then 2 else 1))).comp
      (diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator (if k=0 then 1 else 0))))

private theorem colour_matrix (a : Fin 3) : nativePrimal (colorGenerator a)=
    Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator a))) := by
  change Quantum.operatorMatrix (diracExteriorMotherLieAction
    (p286LieBlockEmbed (p286CoordinateEquiv.symm (p286CoordinateEquiv (sourceColorP286Generator a)))))=_
  rw [LinearEquiv.symm_apply_apply]

private theorem fixed_matrix_general (mu : Fin 4) (a : Fin 3) :
    densityActionMatrix*(sourceCoframeModeGamma mu*nativePrimal (colorGenerator a))=
      (ActionNormalization.phaseMomentum:ℂ) • Quantum.operatorMatrix
        (Complex.I • (diracMatrixMatterAction (diracAdjointSpinSwap*diracGamma mu)).comp
          (diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator a)))) := by
  have flip : flipMatter=diracMatrixMatterAction diracAdjointSpinSwap:=LinearMap.ext flipMatter_source
  rw [sourceDensityActionMatrix_momentum,flip,colour_matrix]
  change ((ActionNormalization.phaseMomentum:ℂ) • Quantum.operatorMatrix (diracMatrixMatterAction diracAdjointSpinSwap))*
    ((Complex.I • Quantum.operatorMatrix (diracMatrixMatterAction (diracGamma mu)))*
      Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator a))))=_
  simp only [map_smul,SU7ExteriorBreakingYukawa.diracMatrixMatterAction_mul,Quantum.matrix_composition,
    smul_mul_assoc,mul_smul_comm,mul_assoc]
  rw [smul_comm]

private theorem fixed_matrix (k : Fin 3) : sourceCoframeModeMatrix k=
    (ActionNormalization.phaseMomentum:ℂ) • Quantum.operatorMatrix (sourceCoframeMother k) := by
  fin_cases k
  · exact fixed_matrix_general 1 1
  · exact fixed_matrix_general 1 0
  · exact fixed_matrix_general 2 0

private theorem mother_embedding (k : Fin 3) (values : Source.Index→ℂ) :
    sourceCoframeMother k (Stage9DEF.Compatibility.embed values)=Stage9DEF.Compatibility.embed (fun index=>Complex.I*
      ∑spin : Fin 4,(diracAdjointSpinSwap*diracGamma (if k=2 then 2 else 1)) index.1 spin*
        ∑color : Fin 2,values (spin,color)*sourceColorPauli (if k=0 then 1 else 0) index.2 color) := by
  simp only [sourceCoframeMother,LinearMap.smul_apply,LinearMap.comp_apply]
  rw [generator_embed,spin_embed,←map_smul]
  rfl

private theorem spin_colour_single (A : Matrix (Fin 4) (Fin 4) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Source.Index) :
    (∑spin : Fin 4,A i.1 spin*∑color : Fin 2,(Pi.single j (1:ℂ):Source.Index→ℂ) (spin,color)*B i.2 color)=
      A i.1 j.1*B i.2 j.2 := by
  rcases j with ⟨spin,color⟩
  simp [Pi.single_apply,Prod.mk.injEq,ite_and]

private theorem mother_basis (k : Fin 3) (side edge : Fin 2) :
    sourceCoframeMother k (Stage9DEF.Compatibility.embed (Pi.single (sourceChargedBasisIndex side edge) 1))=
      sourceCoframeFixedFactor k edge •
        Stage9DEF.Compatibility.embed (Pi.single (sourceChargedBasisIndex side (sourceCoframeOtherEdge edge)) 1) := by
  rw [mother_embedding,←map_smul]
  apply congrArg Stage9DEF.Compatibility.embed
  funext index
  rw [spin_colour_single]
  rcases index with ⟨spin,color⟩
  fin_cases k <;> fin_cases side <;> fin_cases edge <;> fin_cases spin <;> fin_cases color <;>
    norm_num [sourceCoframeFixedFactor,sourceCoframeOtherEdge,sourceChargedBasisIndex,
      diracAdjointSpinSwap,diracGamma,diracGammaOne,diracGammaTwo,sourceColorPauli,
      Matrix.mul_apply,Fin.sum_univ_four,Fin.sum_univ_two,Pi.single_apply,Prod.mk.injEq,
      Pi.smul_apply,smul_eq_mul,Matrix.cons_val,Fin.ext_iff]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,Complex.I_pow_three]

/-- The full252 source matrix maps each actual prepared column to its actual opposite edge, with no omitted output coordinates. -/
theorem sourceCoframeFixedMatrix_prepared (k : Fin 3) (side edge : Fin 2) :
    sourceCoframeModeMatrix k*ᵥQuantum.coordinates (sourceChargedRestriction side edge)=
      ((ActionNormalization.phaseMomentum:ℂ)*sourceCoframeFixedFactor k edge) •
        Quantum.coordinates (sourceChargedRestriction side (sourceCoframeOtherEdge edge)) := by
  rw [fixed_matrix,Matrix.smul_mulVec,Quantum.matrix_action,sourceChargedRestriction_basis,
    sourceChargedRestriction_basis,map_smul,mother_basis,map_smul,map_smul]
  simp only [map_smul,smul_smul]
  congr 1
  ring

/-- The equal first/third fixed-matrix action leaves only actual coframe anisotropy and shear. -/
def sourceCoframePreparedCoefficient (z : SourceCoordinateSlice) (edge : Fin 2) : ℂ :=
  (2:ℂ)*(ActionNormalization.phaseMomentum:ℂ)*
    (((sourceCoframeModeWeight z 0-sourceCoframeModeWeight z 2:ℝ):ℂ)*sourceCoframeFixedFactor 0 edge-
      (sourceCoframeModeWeight z 1:ℂ)/2)

theorem sourceCoframeCoefficient_prepared (z : SourceCoordinateSlice) (side edge : Fin 2) :
    sourceCoframeModeCoefficient z*ᵥQuantum.coordinates (sourceChargedRestriction side edge)=
      sourceCoframePreparedCoefficient z edge •
        Quantum.coordinates (sourceChargedRestriction side (sourceCoframeOtherEdge edge)) := by
  unfold sourceCoframeModeCoefficient
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  simp only [Matrix.smul_mulVec,Matrix.add_mulVec,Matrix.sub_mulVec,sourceCoframeFixedMatrix_prepared,
    smul_add,smul_sub,smul_smul,←add_smul,←sub_smul]
  congr 1
  simp only [sourceCoframePreparedCoefficient,sourceCoframeFixedFactor,
    show (0:Fin 3)≠1 by decide,show (2:Fin 3)≠1 by decide,if_false,if_true,Complex.ofReal_sub,RCLike.ofReal_ofNat]
  ring

/-- Both independent full branches remain in the source symbol before restriction to the original primal preparation. -/
theorem sourceCoframeSymbol_branches (z : SourceCoordinateSlice) :
    sourceCoframeModeSymbol z=Matrix.fromBlocks (sourceCoframeModeCoefficient z) 0 0
      ((sourceCoframeModeCoefficient z).map (starRingEnd ℂ)) := by
  unfold sourceCoframeModeSymbol oppositeDual SourceRealScalarFock.branches
  rw [Matrix.fromBlocks_multiply]
  simp only [one_mul,zero_mul,mul_zero,add_zero,zero_add,neg_mul,neg_neg]
  rfl

theorem sourceCoframeSymbol_prepared (z : SourceCoordinateSlice) (side edge : Fin 2) :
    sourceCoframeModeSymbol z*ᵥsourceChargedCoordinates side edge=
      sourceCoframePreparedCoefficient z edge • sourceChargedCoordinates side (sourceCoframeOtherEdge edge) := by
  rw [sourceCoframeSymbol_branches]
  unfold sourceChargedCoordinates
  rw [Matrix.fromBlocks_mulVec]
  change Sum.elim
    (sourceCoframeModeCoefficient z*ᵥQuantum.coordinates (sourceChargedRestriction side edge)+(0:SourceMatrix)*ᵥ0)
    ((0:SourceMatrix)*ᵥQuantum.coordinates (sourceChargedRestriction side edge)+
      ((sourceCoframeModeCoefficient z).map (starRingEnd ℂ))*ᵥ0)=_
  rw [Matrix.zero_mulVec,Matrix.zero_mulVec,Matrix.mulVec_zero,add_zero,zero_add,sourceCoframeCoefficient_prepared]
  funext i
  cases i with
  | inl i=>rfl
  | inr i=>simp

/-- Full CAR quantization acts on the actual source fibre, not a replacement four-state matrix. -/
theorem sourceCoframeFiber_prepared (z : SourceCoordinateSlice) (side edge : Fin 2) :
    sourceCoframeModeFiber z (sourceChargedFiber side edge)=
      sourceCoframePreparedCoefficient z edge • sourceChargedFiber side (sourceCoframeOtherEdge edge) := by
  change quantized (sourceCoframeModeSymbol z) (oneParticleFiber (sourceChargedCoordinates side edge))=_
  rw [quantized_oneParticle,sourceCoframeSymbol_prepared]
  change fiberCoordinates.symm (Fermion.oneParticleLinear
    (sourceCoframePreparedCoefficient z edge • sourceChargedCoordinates side (sourceCoframeOtherEdge edge)))=_
  rw [map_smul,map_smul]
  rfl

end LowEnergy.PreparationPhysicalCoframePreparedReturn
