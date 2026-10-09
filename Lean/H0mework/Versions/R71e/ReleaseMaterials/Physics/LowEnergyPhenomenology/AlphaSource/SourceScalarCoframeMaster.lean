import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceLorentzRetainerNull

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalLorentzSeedReturn
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
local instance ScalarCoframeIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
attribute [local irreducible] sourceRetainerSeed sourceNonGaugeSeed sourceNativeReaderFirst sourcePoleRead slowFastFrame

theorem sourceLorentzSlot_range (j : Fin 289) :
    (121≤j.val ∧ j.val<145) ↔ ∃mu : Fin 4,∃a : Fin 6,lorentzSlot mu a=j := by
  constructor
  · intro h
    let mu : Fin 4:=⟨(j.val-121)/6,by omega⟩
    let a : Fin 6:=⟨(j.val-121)%6,by omega⟩
    refine ⟨mu,a,?_⟩
    apply Fin.ext
    dsimp [lorentzSlot,mu,a]
    omega
  · rintro ⟨mu,a,rfl⟩
    dsimp [lorentzSlot]
    omega

/-- This support is the original scalar9 and coframe16 coordinate set. -/
def sourceScalarCoframeSupport : Finset (Fin 289) :=
  Finset.univ.filter (fun j=>j.val<9 ∨ (57≤j.val ∧ j.val<73))

theorem sourceScalarCoframeSupport_card : sourceScalarCoframeSupport.card=25 := by decide

def sourceScalarCoframeSeed (q : PhysicalResponsePoint) (j : Fin 289) : SourceOp :=
  if j∈sourceScalarCoframeSupport then sourceRetainerSeed q j else 0

/-- The full source retainer has exactly the computed scalar/coframe support; original external state coordinates remain independent. -/
theorem sourceRetainerSeed_scalarCoframe (q : PhysicalResponsePoint) (left : q.z.im≠0) (right : q.w.im≠0)
    (j : Fin 289) : sourceRetainerSeed q j=sourceScalarCoframeSeed q j := by
  unfold sourceScalarCoframeSeed
  split_ifs with active
  · rfl
  · have outside : ¬(j.val<9 ∨ (57≤j.val ∧ j.val<73)) := by
      simpa only [sourceScalarCoframeSupport,Finset.mem_filter,Finset.mem_univ,true_and] using active
    by_cases gauge : 9≤j.val ∧ j.val<57
    · obtain ⟨mu,a,rfl⟩:=(sourceGaugeSlot_range j).mp gauge
      exact sourceRetainerSeed_gauge_zero q mu a left right
    · by_cases lorentz : 121≤j.val ∧ j.val<145
      · obtain ⟨mu,a,rfl⟩:=(sourceLorentzSlot_range j).mp lorentz
        exact sourceRetainerSeed_lorentz_zero q mu a left right
      · exact sourceRetainerSeed_unseen q j (by omega)

theorem sourceNonGaugeSeed_scalarCoframe (q : PhysicalResponsePoint) (left : q.z.im≠0) (right : q.w.im≠0)
    (j : Fin 289) : sourceNonGaugeSeed q j=sourceScalarCoframeSeed q j :=
  (sourceRetainerSeed_nongauge q left right j).symm.trans (sourceRetainerSeed_scalarCoframe q left right j)

/-- The original full effective reader contracts only the25 computed source action columns. -/
def sourceScalarCoframeNativeSeed (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ) (row : Fin 289) : SourceOp :=
  ∑j∈sourceScalarCoframeSupport,sourceNativeReaderFirst (fixedMomentum n zeta) row j • sourceRetainerSeed q j

def sourceScalarCoframeSlowSeed (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ) (i : Fin 3) : SourceOp :=
  ∑j∈sourceScalarCoframeSupport,(slowFastFrame.transpose*sourceNativeReaderFirst (fixedMomentum n zeta))
    (fiveIndex ⟨i.val,by omega⟩) j • sourceRetainerSeed q j

private theorem zero_source_smul (z : ℂ) : z • (0:SourceOp)=0 := by
  apply ContinuousLinearMap.ext
  intro x
  change z • (0:GaussCoreHilbert.H)=0
  exact smul_zero z

theorem sourceNonGaugeNativeSeed_scalarCoframe (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (left : q.z.im≠0) (right : q.w.im≠0) (row : Fin 289) :
    sourceNonGaugeNativeSeed q n zeta row=sourceScalarCoframeNativeSeed q n zeta row := by
  simp only [sourceNonGaugeNativeSeed,sourceNonGaugeSeed_scalarCoframe q left right,sourceScalarCoframeSeed,sourceScalarCoframeNativeSeed]
  simp only [smul_ite,zero_source_smul,Finset.sum_ite_mem,Finset.univ_inter]

theorem sourceNonGaugeSlowSeed_scalarCoframe (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3) :
    sourceNonGaugeSlowSeed q n zeta i=sourceScalarCoframeSlowSeed q n zeta i := by
  simp only [sourceNonGaugeSlowSeed,sourceNonGaugeSeed_scalarCoframe q left right,sourceScalarCoframeSeed,sourceScalarCoframeSlowSeed]
  simp only [smul_ite,zero_source_smul,Finset.sum_ite_mem,Finset.univ_inter]

/-- All full289 native field rows keep the complete source matrix and same pinned inverse. -/
theorem sourceMasterNative_scalarCoframe (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (left : q.z.im≠0) (right : q.w.im≠0) (row : Fin 289) :
    sourceMasterNative q n zeta l r row=-Complex.I*sourcePoleRead q.epsilon q.precision 0 0 l r
      (sourcePinnedResolvent q.F n zeta*sourceScalarCoframeNativeSeed q n zeta row) := by
  rw [sourceMasterNative_nongauge q n zeta l r left right row,sourceNonGaugeNativeSeed_scalarCoframe q n zeta left right row]

def sourceScalarCoframeMasterChannel (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (i : Fin 3) : ℂ :=
  (sourceChargedDenominator n zeta i)⁻¹*(-Complex.I)*sourcePoleRead q.epsilon q.precision 0 0 l r
    (sourcePinnedResolvent q.F n zeta*sourceScalarCoframeSlowSeed q n zeta i)

theorem sourceMasterChannel_scalarCoframe (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3) :
    sourceMasterChannel q n zeta l r i=sourceScalarCoframeMasterChannel q n zeta l r i := by
  rw [sourceMasterChannel_nongauge q n zeta l r left right i,sourceNonGaugeMasterChannel,
    sourceNonGaugeSlowSeed_scalarCoframe q n zeta left right i]
  rfl

/-- The original static double forcing retains every surviving scalar/coframe seed and exact P0 geometry. -/
theorem sourceStaticNative_scalarCoframe (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex)
    (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3) :
    sourceSlowRead (sourceStaticNative q n l r) ⟨i.val,by omega⟩=
      Complex.I*sourcePoleRead q.epsilon q.precision 0 0 l r
        (sourceResonanceProjection q.F n 0*sourceScalarCoframeSlowSeed q n 0 i) := by
  rw [sourceStaticNative_nongauge q n l r left right i,sourceNonGaugeSlowSeed_scalarCoframe q n 0 left right i]

theorem sourceScalarCoframeSlowSeed_split (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3) :
    sourceScalarCoframeSlowSeed q n zeta i=sourceScalarCoframeSlowSeed q n 0 i+zeta • sourceScalarCoframeSlowSeed q 0 1 i := by
  rw [←sourceNonGaugeSlowSeed_scalarCoframe q n zeta left right i,sourceNonGaugeSlowSeed_split,
    sourceNonGaugeSlowSeed_scalarCoframe q n 0 left right i,sourceNonGaugeSlowSeed_scalarCoframe q 0 1 left right i]


/-- Original physical Fourier phase and all remaining source columns define the same spatial master. -/
def sourceScalarCoframeSpatialChannel (q : PhysicalResponsePoint) (zeta : ℂ) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫n : PhysicalMomentum,sourceSpatialPhase n x*test n*
    sourceScalarCoframeMasterChannel q (sourceSpatialMomentum n) zeta l r i

theorem sourceMasterSpatialChannel_scalarCoframe (q : PhysicalResponsePoint) (zeta : ℂ) (l r : RestStateIndex)
    (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceMasterSpatialChannel q zeta l r i test x=sourceScalarCoframeSpatialChannel q zeta l r i test x := by
  unfold sourceMasterSpatialChannel sourceScalarCoframeSpatialChannel
  apply integral_congr_ae
  filter_upwards with n
  change sourceSpatialPhase n x*test n*sourceMasterChannel q (sourceSpatialMomentum n) zeta l r i=_
  rw [sourceMasterChannel_scalarCoframe q _ zeta l r left right i]

/-- The actual remaining seed is integrable in the original Schwartz observation on the same source causal side. -/
theorem sourceScalarCoframeSpatial_integrable (q : PhysicalResponsePoint) (c eta : ℝ) (frequency : c≠0)
    (causal : 0<eta) (l r : RestStateIndex) (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (fun n : PhysicalMomentum=>sourceSpatialPhase n x*test n*
      sourceScalarCoframeMasterChannel q (sourceSpatialMomentum n) (sourcePoleSide c eta) l r i) := by
  have paid:=(paidDilationMaster% master_integrable) q c eta frequency causal l r i test x
  apply paid.congr
  filter_upwards with n
  change sourceSpatialPhase n x*test n*sourceMasterChannel q (sourceSpatialMomentum n) (sourcePoleSide c eta) l r i=_
  rw [sourceMasterChannel_scalarCoframe q _ _ l r left right i]

/-- Gauge-seed cancellation preserves the already generated whole spatial master derivative, including every remaining source term. -/
theorem sourceScalarCoframeSpatial_derivative (q : PhysicalResponsePoint) (c eta : ℝ) (frequency : c≠0)
    (causal : 0<eta) (l r : RestStateIndex) (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    HasDerivAt (fun z : ℂ=>sourceScalarCoframeSpatialChannel q z l r i test x)
      (sourceMasterSpatialChannelDerivative q (sourcePoleSide c eta) l r i test x) (sourcePoleSide c eta) := by
  have paid:=sourceMasterSpatialChannel_derivative q c eta frequency causal l r i test x
  exact paid.congr_of_eventuallyEq (Eventually.of_forall (fun z=>
    (sourceMasterSpatialChannel_scalarCoframe q z l r left right i test x).symm))

def sourceScalarCoframeSpatialField (q : PhysicalResponsePoint) (zeta : ℂ) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑i : Fin 3,sourceScalarCoframeSpatialChannel q zeta l r i test x • sourceCommonOriginColumn i

theorem sourceMasterSpatialField_scalarCoframe (q : PhysicalResponsePoint) (zeta : ℂ) (l r : RestStateIndex)
    (left : q.z.im≠0) (right : q.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceMasterSpatialField q zeta l r test x=sourceScalarCoframeSpatialField q zeta l r test x := by
  simp only [sourceMasterSpatialField,sourceScalarCoframeSpatialField,sourceMasterSpatialChannel_scalarCoframe q zeta l r left right]

def sourceActualScalarCoframeSpatialField (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (zeta : ℂ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
    sourceScalarCoframeSpatialField q zeta l r test x

/-- All actual source64 weights consume the source-generated 25-column action seed, with every original external preparation unchanged. -/
theorem sourceActualMasterSpatialField_scalarCoframe (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (zeta : ℂ)
    (left : q.z.im≠0) (right : q.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualMasterSpatialField q sL eL sR eR zeta test x=
      sourceActualScalarCoframeSpatialField q sL eL sR eR zeta test x := by
  simp only [sourceActualMasterSpatialField,sourceActualScalarCoframeSpatialField,sourceMasterSpatialField_scalarCoframe q zeta _ _ left right]

open PreparationPhysicalActualLegNormalization

/-- The same independently normalized detector reads the original complete physical spatial response through the computed remaining master seed. -/
theorem sourceActualUnitScalarCoframe_derivative (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T c eta : ℝ) (frequency : c≠0) (causal : 0<eta)
    (sourceLeft : q.z.im≠0) (sourceRight : q.w.im≠0) (left : qd.z.im≠0) (right : qd.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    HasDerivAt (fun z : ℂ=>sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
      (sourceActualScalarCoframeSpatialField q sL eL sR eR z test x))
      (sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T (sourceActualSpatialField q sL eL sR eR c eta test x)-
        sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
          (sourceActualMasterSpatialCorrection q sL eL sR eR (sourcePoleSide c eta) test x)) (sourcePoleSide c eta) := by
  have paid:=sourceActualUnitMaster_derivative qd q dSL dEL dSR dER sL eL sR eR T c eta frequency causal left right test x
  apply paid.congr_of_eventuallyEq
  filter_upwards with z
  rw [sourceActualMasterSpatialField_scalarCoframe q sL eL sR eR z sourceLeft sourceRight test x]

/-- The original finite radial potential and complete correction are directly consumed after the actual192 action-reader and48 gauge and24 Lorentz seed cancellation. -/
theorem sourceActualUnitScalarCoframe_radialDerivative (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (causal : 0<eta) (d : ℝ) (radial : 0<d)
    (sourceLeft : q.z.im≠0) (sourceRight : q.w.im≠0) (left : qd.z.im≠0) (right : qd.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    HasDerivAt (fun s : ℝ=>sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
      (sourceActualScalarCoframeSpatialField q sL eL sR eR ((s:ℂ)*sourcePoleSide (sourceSignedSpeed branch negative) eta) test x))
      (sourcePoleSide (sourceSignedSpeed branch negative) eta*
        (sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x)-
          sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
            (sourceActualMasterSpatialCorrection q sL eL sR eR ((d:ℂ)*sourcePoleSide (sourceSignedSpeed branch negative) eta) test x))) d := by
  have paid:=sourceActualUnitMaster_radialDerivative qd q dSL dEL dSR dER sL eL sR eR T branch negative eta causal d radial left right test x
  apply paid.congr_of_eventuallyEq
  filter_upwards with s
  rw [sourceActualMasterSpatialField_scalarCoframe q sL eL sR eR _ sourceLeft sourceRight test x]

/-- The fixed-side dilation carrier also retains precisely the same original 25-column action remainder. -/
theorem sourceScalarCoframeSpatial_dilation (q : PhysicalResponsePoint) (c eta : ℝ) (frequency : c≠0)
    (causal : 0<eta) (s : ℝ) (positive : 0<s) (l r : RestStateIndex)
    (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceScalarCoframeSpatialChannel q (sourcePoleSide (s*c) (s*eta)) l r i test x=
      (s:ℂ)*sourceScalarCoframeSpatialChannel q (sourcePoleSide c eta) l r i (sourceDilatedTest s positive.ne' test) (s • x) := by
  rw [←sourceMasterSpatialChannel_scalarCoframe q _ l r left right,←sourceMasterSpatialChannel_scalarCoframe q _ l r left right]
  exact sourceMasterSpatialChannel_dilation q c eta frequency causal s positive l r i test x


end LowEnergy.PreparationPhysicalLorentzSeedReturn
