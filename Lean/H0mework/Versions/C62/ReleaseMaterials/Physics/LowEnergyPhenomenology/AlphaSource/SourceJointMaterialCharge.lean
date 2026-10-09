import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceRelativeChargeCore

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalMaterialChargeTorque
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
local instance MaterialChargeIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
open PreparationVacuumNativeFieldInjection
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

open PreparationPhysicalGaugeMomentumCoupling PreparationPhysicalActualLegNormalization
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
attribute [local irreducible] sourcePoleRead sourceProjection jointResolvent sourceEqualProjection
  sourceResonanceProjection frameVector frameTest finiteRiesz


open PreparationVacuumFieldConstraintResponse
open PreparationPhysicalCoframeChargeSelection GaussFockPair
open scoped ContDiff
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional


open PreparationPhysicalCoframeChargeExchange PreparationVacuumPhysicalGaussColorTorque
open GaussDiagonalHistory GaussCoframeSpin GaussLiveMomentum

open Lean Elab Term in
elab "paidRelativeCore%" member:ident : term => do
  let allowed := ["relative_blocks","relative_quantized"]
  unless allowed.contains member.getId.toString do throwError "Unapproved relative-core payer"
  let wanted:=Name.str `LowEnergy.PreparationPhysicalMaterialChargeTorque member.getId.toString
  let candidates:=(←getEnv).constants.toList.filter fun (name,_)=>
    name.toString.startsWith "_private.H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceRelativeChargeCore." && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>throwError "Expected unique already-FIRST relative-core member"

private abbrev End := QuantumTest→ₗ[ℂ]QuantumTest
local instance : Semiring End := Module.End.instSemiring (R:=ℂ) (M:=QuantumTest)

private theorem branch_multiply (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute sourceRelativeChargeCore (GaussNativeForm.multiply c smooth) :=
  (sourceRelativeCharge_multiply c smooth).symm

private theorem branch_sandwich (v w : Ambient) (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute sourceRelativeChargeCore (GaussNativeForm.sandwich v w c smooth) := by
  have adj : Commute (sourceRelativeChargeCore:End) (GaussMomentumAdjoint.adjoint v:End):=
    (sourceRelativeCharge_adjoint v).symm
  have middle : Commute (sourceRelativeChargeCore:End) (GaussNativeForm.multiply c smooth:End):=
    branch_multiply c smooth
  have cov : Commute (sourceRelativeChargeCore:End) (covariantMomentum w:End):=
    (sourceRelativeCharge_covariant w).symm
  change Commute (sourceRelativeChargeCore:End)
    ((GaussMomentumAdjoint.adjoint v:End)*((GaussNativeForm.multiply c smooth:End)*(covariantMomentum w:End)))
  let composition : Semigroup End := (Module.End.instMonoid (R:=ℂ) (M:=QuantumTest)).toSemigroup
  exact @_root_.Commute.mul_right End composition sourceRelativeChargeCore (GaussMomentumAdjoint.adjoint v)
    ((GaussNativeForm.multiply c smooth).comp (covariantMomentum w)) adj
    (@_root_.Commute.mul_right End composition sourceRelativeChargeCore (GaussNativeForm.multiply c smooth)
      (covariantMomentum w) middle cov)

/-- The relative phase commutes with the complete original scalar and gauge kinetic action. -/
theorem sourceRelativeCharge_nativeCore : Commute sourceRelativeChargeCore GaussNativeForm.nativeAction := by
  have each (v w : Ambient) (c : SourceCoordinateSlice→ℝ)
      (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f : QuantumTest) :
      sourceRelativeChargeCore (GaussNativeForm.sandwich v w c smooth f)=
        GaussNativeForm.sandwich v w c smooth (sourceRelativeChargeCore f) :=
    LinearMap.congr_fun (branch_sandwich v w c smooth).eq f
  have scalar (c : SourceCoordinateSlice→ℝ)
      (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f : QuantumTest) :
      sourceRelativeChargeCore (GaussNativeForm.multiply c smooth f)=
        GaussNativeForm.multiply c smooth (sourceRelativeChargeCore f) :=
    LinearMap.congr_fun (branch_multiply c smooth).eq f
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply,GaussNativeForm.nativeAction,GaussNativeForm.scalarKinetic,
    GaussNativeForm.gaugeKinetic,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sum_apply,
    map_add,map_smul,map_sum,each,scalar]


theorem sourceRelativeCharge_spinFiber (a : Fin 7) :
    Commute sourceRelativeChargeFiber (quantized (GaussCoframeSpin.full a)) :=
  (paidRelativeCore% relative_quantized) _ ((paidRelativeCore% relative_blocks) _ _)

theorem sourceRelativeCharge_spinCore (a : Fin 7) :
    Commute sourceRelativeChargeCore (GaussCoframeSpin.current a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A (f z)) (sourceRelativeCharge_spinFiber a).eq

theorem sourceRelativeCharge_numberCore : Commute sourceRelativeChargeCore GaussCoframeForm.number := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have each (g : QuantumTest) : GaussCoframeForm.number g z=SourceQuantumFockGauge.fiberNumber (g z) := by
    apply PiLp.ext
    intro word
    rw [GaussCoframeForm.number_apply,SourceQuantumFockGauge.fiberNumber_apply]
  change sourceRelativeChargeFiber (GaussCoframeForm.number f z)=
    GaussCoframeForm.number (sourceRelativeChargeCore f) z
  rw [each,each]
  exact congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A (f z))
    (GaussQuantumMultiplier.number_commute sourceRelativeChargeMatrix).symm.eq


theorem sourceRelativeCharge_coframeDerivative (v : SourceCoordinateSlice) (f : QuantumTest) :
    GaussCoframeCore.derivative v (sourceRelativeChargeCore f)=
      sourceRelativeChargeCore (GaussCoframeCore.derivative v f) := by
  apply DFunLike.ext
  intro z
  change (TestFunction.lineDerivCLM (n:=⊤) (k:=⊤) ℂ v (sourceRelativeChargeCore f)) z=
    sourceRelativeChargeFiber ((TestFunction.lineDerivCLM (n:=⊤) (k:=⊤) ℂ v f) z)
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp),TestFunction.lineDerivCLM_apply_of_le (by simp),
    (sourceRelativeChargeCore f).contDiff.differentiable (by simp) |>.differentiableAt.lineDeriv_eq_fderiv,
    f.contDiff.differentiable (by simp) |>.differentiableAt.lineDeriv_eq_fderiv]
  have derivative:=(sourceRelativeChargeFiber.restrictScalars ℝ).hasFDerivAt.comp z
    (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  change (fderiv ℝ ((sourceRelativeChargeFiber.restrictScalars ℝ) ∘ f) z) v=_
  rw [derivative.fderiv]
  rfl

theorem sourceRelativeCharge_coframeMomentum (i : Fin 6) :
    Commute sourceRelativeChargeCore (GaussCoframeCore.momentum i) := by
  apply Commute.symm
  apply LinearMap.ext
  intro f
  change (-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) (sourceRelativeChargeCore f)=
    sourceRelativeChargeCore ((-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f)
  rw [sourceRelativeCharge_coframeDerivative,map_smul]

theorem sourceRelativeCharge_coframeAdjoint (i : Fin 6) :
    Commute sourceRelativeChargeCore (GaussCoframeCore.adjoint i) := by
  apply Commute.symm
  apply LinearMap.ext
  intro g
  have pair (f : QuantumTest) :
      sourcePair f (GaussCoframeCore.adjoint i (sourceRelativeChargeCore g))=
        sourcePair f (sourceRelativeChargeCore (GaussCoframeCore.adjoint i g)) := by
    rw [GaussCoframeKinetic.adjoint_pair,sourceRelativeCharge_pair]
    have commute:=LinearMap.congr_fun (sourceRelativeCharge_coframeMomentum i).eq f
    change sourceRelativeChargeCore (GaussCoframeCore.momentum i f)=
      GaussCoframeCore.momentum i (sourceRelativeChargeCore f) at commute
    rw [commute,←GaussCoframeKinetic.adjoint_pair,←sourceRelativeCharge_pair]
  apply sub_eq_zero.mp
  apply embed_injective
  rw [map_zero]
  apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  let d:=GaussCoframeCore.adjoint i (sourceRelativeChargeCore g)-
    sourceRelativeChargeCore (GaussCoframeCore.adjoint i g)
  have paid:=pair d
  change sourcePair d d=0
  unfold d sourcePair
  rw [map_sub,inner_sub_right]
  simpa only [sourcePair,d,map_sub] using (sub_eq_zero.mpr paid)


private theorem branch_mixed (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute sourceRelativeChargeCore (GaussCoframeForm.mixed i a c smooth) := by
  apply LinearMap.ext
  intro f
  have spin (v : QuantumTest) := LinearMap.congr_fun (sourceRelativeCharge_spinCore a).eq v
  have scalar (v : QuantumTest) := LinearMap.congr_fun (branch_multiply c smooth).eq v
  have momentum (v : QuantumTest) := LinearMap.congr_fun (sourceRelativeCharge_coframeMomentum i).eq v
  have adjoint (v : QuantumTest) := LinearMap.congr_fun (sourceRelativeCharge_coframeAdjoint i).eq v
  simp only [Module.End.mul_apply] at spin scalar momentum adjoint
  simp only [Module.End.mul_apply,GaussCoframeForm.mixed,LinearMap.smul_apply,LinearMap.add_apply,
    LinearMap.comp_apply,map_smul,map_add,spin,scalar,momentum,adjoint]


/-- Every original coframe kinetic, spin/current, number and volume term consumes the same relative charge. -/
theorem sourceRelativeCharge_coframeCore : Commute sourceRelativeChargeCore GaussCoframeForm.coframeAction := by
  have spin (a : Fin 7) (v : QuantumTest) := LinearMap.congr_fun (sourceRelativeCharge_spinCore a).eq v
  have scalar (c : SourceCoordinateSlice→ℝ)
      (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (v : QuantumTest) :=
    LinearMap.congr_fun (branch_multiply c smooth).eq v
  have momentum (i : Fin 6) (v : QuantumTest) := LinearMap.congr_fun (sourceRelativeCharge_coframeMomentum i).eq v
  have adjoint (i : Fin 6) (v : QuantumTest) := LinearMap.congr_fun (sourceRelativeCharge_coframeAdjoint i).eq v
  have number (v : QuantumTest) := LinearMap.congr_fun sourceRelativeCharge_numberCore.eq v
  have mixed (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice→ℝ)
      (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (v : QuantumTest) :=
    LinearMap.congr_fun (branch_mixed i a c smooth).eq v
  simp only [Module.End.mul_apply] at spin scalar momentum adjoint number mixed
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply,GaussCoframeForm.coframeAction,GaussCoframeKinetic.kinetic,
    GaussCoframeKinetic.term,GaussCoframeForm.currentAction,GaussCoframeForm.spinSquare,
    GaussCoframeForm.numberShift,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearMap.comp_apply,map_add,map_smul,map_sum,spin,scalar,momentum,adjoint,number,mixed]


theorem sourceRelativeCharge_matterCore : Commute sourceRelativeChargeCore GaussMatterCore.matterAction := by
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply,GaussMatterCore.matterAction,LinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  apply DFunLike.ext
  intro z
  have matrix : sourceRelativeChargeMatrix*GaussMatterCore.localMatrix i b z=
      GaussMatterCore.localMatrix i b z*sourceRelativeChargeMatrix := by
    have spin : Commute sourceRelativeChargeMatrix (GaussCoframeSpin.full (Fin.castAdd 4 b)) :=
      (paidRelativeCore% relative_blocks) _ _
    have native : Commute sourceRelativeChargeMatrix (nativeFull (GaussNativePotential.connectionField z i)) :=
      sourceRelativeCharge_native _
    exact ((spin.smul_right Complex.I).mul_right native).smul_right _
  exact congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A (f z)) ((paidRelativeCore% relative_quantized) _ matrix)

theorem sourceRelativeCharge_diagonalCore : Commute sourceRelativeChargeCore GaussDiagonalHistory.diagonalAction :=
  (sourceRelativeCharge_nativeCore.add_right sourceRelativeCharge_coframeCore).add_right sourceRelativeCharge_matterCore

/-- The full actual core material torque reduces to the existing native covariant and matter torques, with its source-fixed sign. -/
theorem sourceActualCharge_diagonalTorque :
    GaussDiagonalHistory.diagonalAction.comp sourceCoframeChargeCore-
      sourceCoframeChargeCore.comp GaussDiagonalHistory.diagonalAction=
        -(CanonicalPhysicalWardCore.configurationTorque (colorGenerator 2)) := by
  rw [sourceActualCharge_coreDecomposition]
  simp only [LinearMap.comp_add,LinearMap.add_comp,LinearMap.comp_neg,LinearMap.neg_comp,
    LinearMap.comp_smul,LinearMap.smul_comp]
  have neutral : GaussDiagonalHistory.diagonalAction.comp sourceRelativeChargeCore=
      sourceRelativeChargeCore.comp GaussDiagonalHistory.diagonalAction := sourceRelativeCharge_diagonalCore.symm.eq
  rw [neutral]
  change -(GaussDiagonalHistory.diagonalAction.comp (chargeAction (colorGenerator 2)))+
    (1/2:ℂ) • (sourceRelativeChargeCore.comp GaussDiagonalHistory.diagonalAction)-
    (-(chargeAction (colorGenerator 2)).comp GaussDiagonalHistory.diagonalAction+
      (1/2:ℂ) • (sourceRelativeChargeCore.comp GaussDiagonalHistory.diagonalAction))=_
  simp only [CanonicalPhysicalWardCore.configurationTorque]
  abel

theorem sourceActualCharge_diagonalForm (f g : QuantumTest) :
    sourcePair f (GaussDiagonalHistory.diagonalAction (sourceCoframeChargeCore g)-
      sourceCoframeChargeCore (GaussDiagonalHistory.diagonalAction g))=
      -(sourceNativeTorque f g+sourcePair f (sourceColorWardOperator GaussMatterCore.matterAction g)) := by
  have generated:=congrArg (fun A : End=>sourcePair f (A g)) sourceActualCharge_diagonalTorque
  change sourcePair f (GaussDiagonalHistory.diagonalAction (sourceCoframeChargeCore g)-
    sourceCoframeChargeCore (GaussDiagonalHistory.diagonalAction g))=
      sourcePair f (-(CanonicalPhysicalWardCore.configurationTorque (colorGenerator 2) g)) at generated
  calc
    _=sourcePair f (-(CanonicalPhysicalWardCore.configurationTorque (colorGenerator 2) g)):=generated
    _= -sourcePair f (CanonicalPhysicalWardCore.configurationTorque (colorGenerator 2) g):=by
      simp only [sourcePair,map_neg,inner_neg_right]
    _=_:=congrArg Neg.neg (sourceConfigurationTorque_ward f g)


open PreparationVacuumUncutYukawa GaussNativePotential

/-- Actual signed source charges on both full branches, not a selected four-state table. -/
def sourceMaterialModeCharge : Mode→ℚ
  | .inl i=> -sourceWholeWeight i
  | .inr i=> sourceWholeWeight i

theorem sourceActualCharge_fullDiagonal :
    sourceActualGaussChargeMatrix=Matrix.diagonal (fun i=>(sourceMaterialModeCharge i:ℂ)) := by
  rw [sourceActualGaussChargeMatrix,sourcePhaseNoether_matrix]
  ext i j
  cases i <;> cases j <;>
    simp [sourceMaterialModeCharge,SourceRealScalarFock.branches,Matrix.fromBlocks,
      Matrix.diagonal_apply]

/-- Every scalar Yukawa charge transition is generated by the original full source spectrum. -/
def sourceMaterialYukawaTorqueMatrix (phi : SourceQuantumScalarChart.Scalar) : FullMatrix :=
  GaussYukawaCoefficient.fullMatrix phi*sourceActualGaussChargeMatrix-
    sourceActualGaussChargeMatrix*GaussYukawaCoefficient.fullMatrix phi

theorem sourceMaterialYukawaTorque_entries (phi : SourceQuantumScalarChart.Scalar) (i j : Mode) :
    sourceMaterialYukawaTorqueMatrix phi i j=
      ((sourceMaterialModeCharge j:ℂ)-(sourceMaterialModeCharge i:ℂ))*
        GaussYukawaCoefficient.fullMatrix phi i j := by
  simp only [sourceMaterialYukawaTorqueMatrix,sourceActualCharge_fullDiagonal,
    Matrix.sub_apply,Matrix.mul_diagonal,Matrix.diagonal_mul]
  ring

def sourceRetainedYukawaCore (phi : CanonicalGradedLocalCurrent.Localizer) : End :=
  localMultiplier (fun z=>compactFiber 0 phi (0,z))
    (fun _=>(uncutTest 0 phi 0).contDiff.contDiffAt)

def sourceMaterialYukawaTorqueCore (phi : CanonicalGradedLocalCurrent.Localizer) : End :=
  (sourceRetainedYukawaCore phi).comp sourceCoframeChargeCore-
    sourceCoframeChargeCore.comp (sourceRetainedYukawaCore phi)

theorem sourceMaterialYukawaTorque_generated (phi : CanonicalGradedLocalCurrent.Localizer) (f : QuantumTest) (z : SourceCoordinateSlice) :
    sourceMaterialYukawaTorqueCore phi f z=(phi z:ℂ) •
      quantized (sourceMaterialYukawaTorqueMatrix (scalarField z)) (f z) := by
  have original:=(paidCoframeQuantizerComm%) (GaussYukawaCoefficient.fullMatrix (scalarField z)) sourceActualGaussChargeMatrix
  have applied:=congrArg (fun A : FockFiber→L[ℂ]FockFiber=>(phi z:ℂ) • A (f z)) original
  change (phi z:ℂ) • (GaussYukawaCoefficient.sourceMap (scalarField (fieldCoordinateCurve 0 0 z))
    (quantized sourceActualGaussChargeMatrix (f z)))-
    quantized sourceActualGaussChargeMatrix ((phi z:ℂ) •
      GaussYukawaCoefficient.sourceMap (scalarField (fieldCoordinateCurve 0 0 z)) (f z))=_
  rw [PreparationVacuumGradedTransport.curve_zero,map_smul]
  have same : GaussYukawaCoefficient.sourceMap (scalarField z)=
      quantized (GaussYukawaCoefficient.fullMatrix (scalarField z)) := rfl
  rw [same]
  simpa only [sourceMaterialYukawaTorqueMatrix,GaussQuantumMultiplier.quantizer,
    LinearMap.coe_mk,AddHom.coe_mk,sub_apply,mul_apply_eq_comp,smul_sub] using applied.symm

/-- The same finiteRetainer operator consumes its original whole scalar/core torque. -/
theorem sourceMaterialYukawaTorque_return (phi : CanonicalGradedLocalCurrent.Localizer) (f : QuantumTest) :
    (uncutOperator 0 phi 0*sourceActualGaussCharge-sourceActualGaussCharge*uncutOperator 0 phi 0) (embed f)=
      embed (sourceMaterialYukawaTorqueCore phi f) := by
  simp only [sub_apply,mul_apply_eq_comp,sourceCoframeChargeCore_embed,uncutOperator_core]
  change embed (sourceRetainedYukawaCore phi (sourceCoframeChargeCore f))-
    embed (sourceCoframeChargeCore (sourceRetainedYukawaCore phi f))=_
  rw [←map_sub]
  rfl

theorem sourceRelativeCharge_retainedYukawaCore (phi : CanonicalGradedLocalCurrent.Localizer) :
    Commute sourceRelativeChargeCore (sourceRetainedYukawaCore phi) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change sourceRelativeChargeFiber ((phi z:ℂ) • GaussYukawaCoefficient.sourceMap
    (scalarField (fieldCoordinateCurve 0 0 z)) (f z))=
    (phi z:ℂ) • GaussYukawaCoefficient.sourceMap (scalarField (fieldCoordinateCurve 0 0 z))
      (sourceRelativeChargeFiber (f z))
  rw [map_smul]
  exact congrArg (fun A : FockFiber→L[ℂ]FockFiber=>(phi z:ℂ) • A (f z))
    (sourceRelativeCharge_scalarFiber _)

/-- The full scalar torque is the original color torque with the derived sign; the independent-dual relative phase contributes zero by its actual core action. -/
theorem sourceMaterialYukawaTorque_colour (phi : CanonicalGradedLocalCurrent.Localizer) :
    sourceMaterialYukawaTorqueCore phi= -sourceColorWardOperator (sourceRetainedYukawaCore phi) := by
  unfold sourceMaterialYukawaTorqueCore
  rw [sourceActualCharge_coreDecomposition]
  simp only [LinearMap.comp_add,LinearMap.add_comp,LinearMap.comp_neg,LinearMap.neg_comp,
    LinearMap.comp_smul,LinearMap.smul_comp]
  have neutral : (sourceRetainedYukawaCore phi).comp sourceRelativeChargeCore=
      sourceRelativeChargeCore.comp (sourceRetainedYukawaCore phi) :=
    (sourceRelativeCharge_retainedYukawaCore phi).symm.eq
  rw [neutral]
  unfold sourceColorWardOperator
  abel

end LowEnergy.PreparationPhysicalMaterialChargeTorque
