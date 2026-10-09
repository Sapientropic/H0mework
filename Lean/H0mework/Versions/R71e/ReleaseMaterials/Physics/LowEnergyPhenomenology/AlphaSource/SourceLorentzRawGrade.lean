import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActionSeedSpatialReturn

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
local instance LorentzSeedIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
open Lean Elab Term in
elab "paidLorentzGrade% " id:ident : term => do
  let member:=id.getId
  let allowed : List Name := [`primalPreserves,`primal_mother,`primal_smul,`primal_mul,`primal_densityAction,
    `primal_coefficient,`full_branches,`opposite_preserves,`sample_project,`frame_project,`frame_rank_left,`frame_rank_right,
    `bareResolvent_blocks]
  unless member∈allowed do throwError "Member is outside the original GaugeBand payer whitelist"
  let wanted:=`LowEnergy.PreparationVacuumPhysicalGradeZeroRead ++ member
  let all:=(←getEnv).constants.toList.filter fun (name,_)=>privateToUserName name==wanted
  let candidates:=all.filter fun (name,_)=>name.toString.startsWith "_private.H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationGaugeBand."
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>throwError "Expected unique original GaugeBand payer {wanted}; actual owners {all.map Prod.fst}"

attribute [local irreducible] sourceRetainerSeed sourceFullInitialUpper sourceNativeReaderFirst
  rawActionSymbol spinLinear densityVariation

/-- The actual Lorentz column changes precisely the original spin connection in ActionState. -/
theorem sourceLorentzActionDirection (mu : Fin 4) (a : Fin 6) :
    fieldDirection (fieldUnit (lorentzSlot mu a))=
      (0,(fun nu=>spinLinear nu (fieldLorentz (fieldUnit (lorentzSlot mu a)))),0) := by
  have scalar (j : Fin 9) : fieldUnit (lorentzSlot mu a) (scalarSlot j)=0 := by
    simp only [fieldUnit,Pi.single_apply]
    apply if_neg
    intro equal
    have h:=congrArg Fin.val equal
    dsimp [scalarSlot,lorentzSlot] at h
    omega
  have gauge (nu : Fin 4) (b : Fin 12) : fieldUnit (lorentzSlot mu a) (gaugeSlot nu b)=0 := by
    simp only [fieldUnit,Pi.single_apply]
    apply if_neg
    intro equal
    have h:=congrArg Fin.val equal
    dsimp [gaugeSlot,lorentzSlot] at h
    omega
  have coframe (b nu : Fin 4) : fieldUnit (lorentzSlot mu a) (coframeSlot b nu)=0 := by
    simp only [fieldUnit,Pi.single_apply]
    apply if_neg
    intro equal
    have h:=congrArg Fin.val equal
    dsimp [coframeSlot,lorentzSlot] at h
    omega
  rw [←stateDirection_source]
  change (fieldCoframe (fieldUnit (lorentzSlot mu a)),
    (fun nu=>spinLinear nu (fieldLorentz (fieldUnit (lorentzSlot mu a)))+
      nativePrimal (fieldGauge (fieldUnit (lorentzSlot mu a)) nu)),
    PreparationVacuumGaugeSourceInjection.scalarLinear (fieldScalar (fieldUnit (lorentzSlot mu a))))=_
  apply Prod.ext
  · funext b nu
    exact coframe b nu
  apply Prod.ext
  · funext nu
    simp only [fieldGauge,gauge,zero_smul,Finset.sum_const_zero,map_zero,add_zero]
  · simp only [fieldScalar,scalar,zero_smul,Finset.sum_const_zero,map_zero]

private theorem connection_density (f : Field289) (connection : Fin 4→SourceMatrix)
    (direction : fieldDirection f=(0,connection,0)) (s : ActionState) (nondegenerate : s.1.det≠0) (i : Fin 4) :
    densityVariation f s i=if i=0 then stateVolume s • (∑mu : Fin 4,coefficientMatrix mu s.1*connection mu) else 0 := by
  let L:=stateVolume s • (∑mu : Fin 4,coefficientMatrix mu s.1*connection mu)
  have coframe (t : ℝ) : (s+t • fieldDirection f).1=s.1 := by rw [direction];simp
  have scalar (t : ℝ) : (s+t • fieldDirection f).2.2=s.2.2 := by rw [direction];simp
  have connectionPath (t : ℝ) (mu : Fin 4) : (s+t • fieldDirection f).2.1 mu=s.2.1 mu+t • connection mu := by
    rw [direction]
    rfl
  have volume (t : ℝ) : stateVolume (s+t • fieldDirection f)=stateVolume s := by
    unfold stateVolume
    rw [coframe]
  have principal (t : ℝ) (mu : Fin 4) : statePrincipal mu (s+t • fieldDirection f)=statePrincipal mu s := by
    rw [statePrincipal,volume,coframe]
    rfl
  have lower (t : ℝ) : stateDensityLower (s+t • fieldDirection f)=stateDensityLower s+t • L := by
    rw [stateDensityLower,volume,stateLower,coframe,scalar]
    simp only [connectionPath,Matrix.mul_add,Matrix.mul_smul,Finset.sum_add_distrib,←Finset.smul_sum]
    change stateVolume s • ((∑mu : Fin 4,coefficientMatrix mu s.1*s.2.1 mu)+
      t • (∑mu : Fin 4,coefficientMatrix mu s.1*connection mu)+s.2.2)=
      stateVolume s • ((∑mu : Fin 4,coefficientMatrix mu s.1*s.2.1 mu)+s.2.2)+
        t • (stateVolume s • (∑mu : Fin 4,coefficientMatrix mu s.1*connection mu))
    simp only [smul_add,smul_comm (stateVolume s) t]
    abel
  have point (t : ℝ) : heldDensityCoefficient s (s+t • fieldDirection f) i=
      heldDensityCoefficient s s i+t • (if i=0 then L else 0) := by
    unfold heldDensityCoefficient
    rw [lower,principal]
    refine Fin.cases ?_ (fun j=>?_) i
    · simp only [Fin.cases_zero,ite_true]
      abel
    · simp only [Fin.cases_succ,principal,Fin.succ_ne_zero,ite_false,smul_zero,add_zero]
  have actual:=densityVariation_generated f s nondegenerate i
  have generated:=((hasDerivAt_id (0:ℝ)).smul_const (if i=0 then L else 0)).const_add (heldDensityCoefficient s s i)
  simp only [one_smul] at generated
  have same:=generated.congr_of_eventuallyEq (Eventually.of_forall point)
  exact actual.unique same

def sourceLorentzRawCoefficient (mu : Fin 4) (a : Fin 6) (s : ActionState) : SourceMatrix :=
  densityActionMatrix*(stateVolume s • (∑nu : Fin 4,coefficientMatrix nu s.1*
    spinLinear nu (fieldLorentz (fieldUnit (lorentzSlot mu a)))))

theorem sourceLorentzDensity (mu : Fin 4) (a : Fin 6) (s : ActionState) (nondegenerate : s.1.det≠0) (i : Fin 4) :
    densityVariation (fieldUnit (lorentzSlot mu a)) s i=
      if i=0 then stateVolume s • (∑nu : Fin 4,coefficientMatrix nu s.1*
        spinLinear nu (fieldLorentz (fieldUnit (lorentzSlot mu a)))) else 0 :=
  connection_density _ _ (sourceLorentzActionDirection mu a) s nondegenerate i

/-- The raw Lorentz field action is the actual volume/coefficient/spin expression, before its grade is evaluated. -/
theorem sourceLorentzRawSymbol (mu : Fin 4) (a : Fin 6) (p : PhysicalMomentum)
    (s : ActionState) (nondegenerate : s.1.det≠0) :
    rawActionSymbol (fieldUnit (lorentzSlot mu a)) p s=
      oppositeDual*SourceRealScalarFock.branches (sourceLorentzRawCoefficient mu a s) := by
  unfold rawActionSymbol rawFourier
  simp only [sourceLorentzDensity mu a s nondegenerate]
  change oppositeDual*realFourierMatrix (fun i=>densityActionMatrix*(if i=0 then stateVolume s •
    (∑nu : Fin 4,coefficientMatrix nu s.1*spinLinear nu (fieldLorentz (fieldUnit (lorentzSlot mu a)))) else 0)) p=_
  simp [realFourierMatrix,affineMatrix,sourceLorentzRawCoefficient,SourceRealScalarFock.branches]

private theorem spin_preserves (nu : Fin 4) (v : StageNineLorentzConnectionVariation.LorentzBivectorOneForm) :
    (paidLorentzGrade% primalPreserves) (spinLinear nu v) := by
  unfold spinLinear
  exact (paidLorentzGrade% primal_mother) _ (MixedSymbol.degreeSix_spin _)

private theorem sum_preserves (f : Fin 4→SourceMatrix)
    (paid : ∀nu,(paidLorentzGrade% primalPreserves) (f nu)) :
    (paidLorentzGrade% primalPreserves) (∑nu : Fin 4,f nu) := by
  intro i j
  simp only [Matrix.sum_apply,Finset.mul_sum]
  exact Finset.sum_eq_zero (fun nu _=>paid nu i j)

/-- The original spin degree-six identity generates the full real/complex-dual Fock grade of every Lorentz column. -/
theorem sourceLorentzRawMatrix_gradeZero (mu : Fin 4) (a : Fin 6) (p : PhysicalMomentum) (z : physicalChart) :
    Preserves (rawActionSymbol (fieldUnit (lorentzSlot mu a)) p (sourceState z.val)) := by
  rw [sourceLorentzRawSymbol mu a p (sourceState z.val) (coframe_nondegenerate z)]
  apply preserves_mul (paidLorentzGrade% opposite_preserves)
  apply (paidLorentzGrade% full_branches)
  unfold sourceLorentzRawCoefficient
  apply (paidLorentzGrade% primal_mul) _ _ (paidLorentzGrade% primal_densityAction)
  apply (paidLorentzGrade% primal_smul)
  apply sum_preserves
  intro nu
  exact (paidLorentzGrade% primal_mul) _ _ ((paidLorentzGrade% primal_coefficient) nu _)
    (spin_preserves nu _)

/-- Every original occupation/degree block consumes the generated raw Lorentz grade. -/
theorem sourceLorentzRawFiber_blocks (mu : Fin 4) (a : Fin 6) (p : PhysicalMomentum) (z : physicalChart) (g : Label) :
    Commute (fiberPiece g) (rawStateFiber (fieldUnit (lorentzSlot mu a)) p (sourceState z.val)) := by
  rw [←rawActionSymbol_actual]
  unfold fiberPiece
  exact blockWeight_quantized _ _ (sourceLorentzRawMatrix_gradeZero mu a p z)

end LowEnergy.PreparationPhysicalLorentzSeedReturn
