import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhaseConfigurationTime

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPhasePropagation
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField FullQuantum.StateGreen
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumOriginalDensity PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets PreparationVacuumPhysicalFeedback
open PreparationVacuumNoetherChart
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _

open PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction PreparationVacuumHalfDensityFiber
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
open ActualEMOriginWard Stage9C.Material.SpinPair PreparationVacuumPhysicalModeContact


open GaussLiveMomentum GaussNativeMatter SourceQuantumScalarChart SourceQuantumResidualGaugeSlice
open StageNineP286GaugeConnectionVariationDensity
open PreparationPhysicalPhaseGaugeRealization PreparationVacuumNativeFieldInjection
open PreparationVacuumActionDecomposition StageNineHolonomicField
open ActualEMCompleteOrbit

open PreparationVacuumFieldConstraintResponse SourceGraph
open ActualDressedPhaseWard ActualDressedNoether ActualDressedFullCoulomb ActualDressedSourcePreparation
open PreparationVacuumElectricConstraint PreparationVacuumFullElectricWard CanonicalPhysicalWardCore
open CanonicalGradedCharge GaussFockPair PreparationVacuumSourcePreparedResponse
attribute [local irreducible] sourceState sourceSymbol sourceActionWeight phaseHeldAction phaseHeldMixed
  sourceReferenceState sourceDressedUnit sourceProfile jointResolvent chargeReader dressedEulerObserver prepared


open ActualDressedPhaseConfiguration ActualDressedNonlinearHalf


open SourcePropagationNearFieldTime SourcePropagationNoetherTime SourcePropagationTimeDependentFeedback
open ActualDressedLockedWard ActualDressedConstraintRead
attribute [local irreducible] physicalTime phaseReader phaseReaderContact nativeWardHistory
  configurationWardReader configurationWardContact physicalBackgroundMap



open PreparationVacuumPhysicalHalfAxis PreparationVacuumPropagationPencil
open SourcePropagationResolvent SourcePropagationFieldFeedback ActualDressedSylvester ActualDressedStaticResponse
local instance : NormedAlgebra ℝ SourcePropagationResolvent.TransferOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedSpace ℝ SourcePropagationResolvent.TransferOp := ContinuousLinearMap.toNormedSpace
local instance : IsBoundedSMul ℝ SourcePropagationResolvent.TransferOp := by
  convert! (NormedSpace.toIsBoundedSMul (𝕜:=ℝ) (E:=SourcePropagationResolvent.TransferOp)) using 1
local instance : ContinuousSMul ℝ SourcePropagationResolvent.TransferOp := by
  convert! (IsBoundedSMul.continuousSMul (α:=ℝ) (β:=SourcePropagationResolvent.TransferOp)) using 1
local instance : ContinuousENorm SourcePropagationResolvent.TransferOp := by
  convert! (SeminormedAddGroup.toContinuousENorm (E:=SourcePropagationResolvent.TransferOp)) using 1
attribute [local irreducible] fieldInverse nearTimeHalf noetherBackgroundOperator dressedNoetherHalfSource
  dressedNoetherBackgroundSource dressedStaticPolarization staticQuantumCorrection staticInputNormalizer


/-- The actual nonlinear configuration insertion, not a state-dependent field label. -/
def configurationPhaseKernel (event : DressedEvent) (transfer : PhysicalMomentum) (age : ℝ)
    (h : Field289) : H→L[ℂ]H :=
  physicalTime (event.momentum-transfer) event.frame (-age) h*
    jointResolvent (event.momentum-transfer) event.frame event.energy h*
    phaseReader .deviation event.momentum event.frame h*
    jointResolvent event.momentum event.frame event.energy h*physicalTime event.momentum event.frame age h

/-- Both real time endpoints, both material inverse derivatives and the generated weighted configuration contact enter the actual variation. -/
theorem configuration_kernel_source_derivative (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ=>configurationPhaseKernel event transfer age (r • force))
      (configurationPhaseHistory event transfer (fun _=>⟨force,0,0⟩) age) 0 := by
  have tl:=physicalTime_direction force (event.momentum-transfer) event.frame (-age)
  have rl:=inverse_direction (event.momentum-transfer) event.frame event.energy event.nonreal force
  have reader:=configuration_reader_source_derivative force event.momentum event.frame
  have rr:=inverse_direction event.momentum event.frame event.energy event.nonreal force
  have tr:=physicalTime_direction force event.momentum event.frame age
  have generated:=(((tl.mul rl).mul reader).mul rr).mul tr
  simp only [Pi.mul_apply,zero_smul] at generated
  have source:=configuration_reader_original event.momentum event.frame
  rw [←source] at generated
  have corrected:=generated.congr_deriv (show _=configurationPhaseHistory event transfer (fun _=>⟨force,0,0⟩) age from by
    unfold configurationPhaseHistory
    change _=nativeWardHistory (dressedKinematicPoint event transfer)
      (configurationWardReader event.momentum event.frame)
      (fun f=>configurationWardContact f event.momentum event.frame) (fun _=>force) age
    simp only [nativeWardHistory,orderedDual_constant,orderedPrimal_constant,dressedKinematicPoint,sub_eq_add_neg]
    noncomm_ring)
  simpa only [configurationPhaseKernel,Pi.mul_apply] using! corrected

/-- Each branch uses its actual nonlinear reader and both material resolvents at the same h. -/
def phaseNonlinearInitial (part : PhasePart) (q : PhysicalResponsePoint) (h : Field289) : H→L[ℂ]H :=
  jointResolvent (q.p+q.k) q.F q.z h*phaseReader part q.p q.F h*jointResolvent q.p q.F q.w h

def phaseNonlinearHalf (part : PhasePart) (q : PhysicalResponsePoint) (lambda : ℂ) (h : Field289) : H→L[ℂ]H :=
  ∫t in Ioi (0:ℝ),laplaceWeight lambda t • physicalBackgroundMap q h t (phaseNonlinearInitial part q h)

attribute [local irreducible] phaseNonlinearInitial phaseNonlinearHalf

private theorem phase_half_integrable (part : PhasePart) (q : PhysicalResponsePoint) (lambda : ℂ)
    (positive : 0<lambda.re) (h : Field289) (inside : h∈timeDomain q lambda) :
    IntegrableOn (fun t=>laplaceWeight lambda t • physicalBackgroundMap q h t (phaseNonlinearInitial part q h)) (Ioi (0:ℝ)) := by
  have paid:=physicalBackgroundMap_integrable q lambda positive h inside
  unfold IntegrableOn at *
  with_reducible_and_instances
    have applied:=Integrable.apply_continuousLinearMap (𝕜:=ℂ) (𝕜':=ℂ) (σ:=RingHom.id ℂ)
      (H:=ResponseOp) (E:=ResponseOp) paid (phaseNonlinearInitial part q h)
    simpa only [smul_apply] using! applied

/-- The actual halfline is generated from the original damped physical-background map, at the same source h. -/
theorem phase_nonlinear_half_inverse (part : PhasePart) (q : PhysicalResponsePoint) (lambda : ℂ)
    (positive : 0<lambda.re) :
    phaseNonlinearHalf part q lambda=ᶠ[𝓝 0] fun h=>fieldInverse q lambda h (phaseNonlinearInitial part q h) := by
  filter_upwards [timeDomain_source_near q lambda positive,nearTimeHalf_inverse_generated q lambda positive]
    with h inside inverse
  have integral:=physicalBackgroundMap_integrable q lambda positive h inside
  have applied:=ContinuousLinearMap.integral_apply integral (phaseNonlinearInitial part q h)
  calc
    _=nearTimeHalf q lambda h (phaseNonlinearInitial part q h) := by
      unfold phaseNonlinearHalf nearTimeHalf
      simpa only [smul_apply] using! applied.symm
    _=_ := congrArg (fun A : SourcePropagationResolvent.TransferOp=>A (phaseNonlinearInitial part q h)) inverse

private def observedInverse (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ)
    (h : Field289) : (H→L[ℂ]H)→ₗ[ℂ]ℂ where
  toFun J:=dressedEulerObserver event (fieldInverse (dressedKinematicPoint event transfer) lambda h
    (jointResolvent (event.momentum-transfer) event.frame event.energy h*J*
      jointResolvent event.momentum event.frame event.energy h))
  map_add' A B:=by simp only [mul_add,add_mul,map_add]
  map_smul' c A:=by simp only [mul_smul_comm,smul_mul_assoc,map_smul,RingHom.id_apply]

def phaseNonlinearSource (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ) (h : Field289) : ℂ :=
  dressedEulerObserver event (phaseNonlinearHalf .ward (dressedKinematicPoint event transfer) lambda h)-
    dressedEulerObserver event (phaseNonlinearHalf .scalar (dressedKinematicPoint event transfer) lambda h)-
    dressedEulerObserver event (phaseNonlinearHalf .deviation (dressedKinematicPoint event transfer) lambda h)

attribute [local irreducible] phaseNonlinearSource observedInverse

/-- Full phase minus actual scalar/configuration branches consumes the genuine all289 nonlinear source current on one fixed source germ. -/
theorem phase_nonlinear_source_current (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ)
    (positive : 0<lambda.re) :
    phaseNonlinearSource event transfer lambda=ᶠ[𝓝 0] fun h=>
      ((gaugeScale/2:ℝ):ℂ)*(∑j : Fin 289,(sourceModeField j:ℂ)*dressedNoetherHalfSource event transfer lambda h j) := by
  filter_upwards [phase_nonlinear_half_inverse .ward (dressedKinematicPoint event transfer) lambda positive,
    phase_nonlinear_half_inverse .scalar (dressedKinematicPoint event transfer) lambda positive,
    phase_nonlinear_half_inverse .deviation (dressedKinematicPoint event transfer) lambda positive,
    phase_reader_germ event.momentum event.frame,
    source_reader_germ sourceModeField event.momentum event.frame,
    dressed_noether_half_background event transfer lambda positive]
    with h ward scalar deviation phase basis half
  have phaseRead:=congrArg (observedInverse event transfer lambda h) phase
  have basisRead:=congrArg (observedInverse event transfer lambda h) basis
  simp only [LinearMap.map_smul_of_tower,map_sub] at phaseRead
  simp only [map_sum,map_smul] at basisRead
  have pair:=congrArg₂ (fun A B : H→L[ℂ]H=>dressedEulerObserver event A-dressedEulerObserver event B) ward scalar
  have phases:=congrArg₂ (fun value : ℂ=>fun A : H→L[ℂ]H=>value-dressedEulerObserver event A) pair deviation
  have first : dressedEulerObserver event
      (fieldInverse (dressedKinematicPoint event transfer) lambda h
        (phaseNonlinearInitial .ward (dressedKinematicPoint event transfer) h))-
    dressedEulerObserver event
      (fieldInverse (dressedKinematicPoint event transfer) lambda h
        (phaseNonlinearInitial .scalar (dressedKinematicPoint event transfer) h))-
    dressedEulerObserver event
      (fieldInverse (dressedKinematicPoint event transfer) lambda h
        (phaseNonlinearInitial .deviation (dressedKinematicPoint event transfer) h))=
      ((gaugeScale/2:ℝ):ℂ)*observedInverse event transfer lambda h
        (noetherReader sourceModeField event.momentum event.frame h) := by
    simpa only [observedInverse,LinearMap.coe_mk,AddHom.coe_mk,phaseNonlinearInitial,
      dressedKinematicPoint,sub_eq_add_neg,Complex.real_smul] using! phaseRead.symm
  have leafSum : (∑j : Fin 289,(sourceModeField j:ℂ)*observedInverse event transfer lambda h
      (noetherReader (fieldUnit j) event.momentum event.frame h))=
      ∑j : Fin 289,(sourceModeField j:ℂ)*dressedNoetherHalfSource event transfer lambda h j := by
    apply Finset.sum_congr rfl
    intro j _
    apply congrArg (fun value : ℂ=>(sourceModeField j:ℂ)*value)
    have entry:=congrFun half j
    calc
      _=dressedNoetherBackgroundSource event transfer lambda h j := by
        simp only [observedInverse,LinearMap.coe_mk,AddHom.coe_mk,dressedNoetherBackgroundSource,
          noetherBackgroundOperator,noetherBackgroundInitial,dressedKinematicPoint,sub_eq_add_neg]
      _=_ := entry.symm
  unfold phaseNonlinearSource
  exact phases.trans (first.trans (congrArg (fun value : ℂ=>((gaugeScale/2:ℝ):ℂ)*value)
    (basisRead.trans leafSum)))

/-- The original nonlinear half's differential now directly pays the source phase row of the actual polarization matrix. -/
theorem phase_nonlinear_polarization (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ)
    (positive : 0<lambda.re) (force : Field289) :
    HasDerivAt (fun r : ℝ=>phaseNonlinearSource event transfer lambda (r • force))
      (((gaugeScale/2:ℝ):ℂ)*(∑j : Fin 289,(sourceModeField j:ℂ)*
        (dressedStaticPolarization event transfer lambda*ᵥ(fun k=>(force k:ℂ))) j)) 0 := by
  have full:=dressed_noether_half_full_derivative event transfer lambda positive force
  have each (j : Fin 289) := (ContinuousLinearMap.proj j : (Fin 289→ℂ)→L[ℝ]ℂ).hasFDerivAt.comp_hasDerivAt 0 full
  have sum:=HasDerivAt.fun_sum (fun j (_ : j∈Finset.univ)=>(each j).const_mul (sourceModeField j:ℂ))
  have original:=sum.const_mul ((gaugeScale/2:ℝ):ℂ)
  have ray : Tendsto (fun r : ℝ=>r • force) (𝓝 0) (𝓝 (0:Field289)) := by
    simpa only [zero_smul] using (fieldRay_derivative force 0).continuousAt.tendsto
  exact original.congr_of_eventuallyEq ((phase_nonlinear_source_current event transfer lambda positive).comp_tendsto ray)

/-- Constant-input normalization is applied once to the genuine phase current differential. -/
theorem phase_nonlinear_normalized_polarization (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ)
    (positive : 0<lambda.re) (force : Field289) :
    HasDerivAt (fun r : ℝ=>staticInputNormalizer lambda*phaseNonlinearSource event transfer lambda (r • force))
      (((gaugeScale/2:ℝ):ℂ)*(∑j : Fin 289,(sourceModeField j:ℂ)*
        (staticQuantumCorrection event transfer lambda*ᵥ(fun k=>(force k:ℂ))) j)) 0 := by
  have generated:=(phase_nonlinear_polarization event transfer lambda positive force).const_mul (staticInputNormalizer lambda)
  convert! generated using 1
  simp only [staticQuantumCorrection,Matrix.smul_mulVec,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end LowEnergy.GaussComposite.ActualDressedPhasePropagation
