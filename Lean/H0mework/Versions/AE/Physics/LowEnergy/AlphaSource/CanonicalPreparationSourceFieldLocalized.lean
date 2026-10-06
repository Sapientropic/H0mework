import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFieldJets

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceFieldFamily
open SaturationMonoid.PhysicsCore
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction
open StageNineDiracDualYukawaSpinJurisdiction Stage9C.Material.SpinPair
open StageNineDiracDualFormNativeConjugateMatterVariation
open SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullQuantum.StateGreen FullQuantum.CoframeResponse
open Electromagnetic.CanonicalCoframe
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open SourceQuantumFockGauge GaussHistoryHilbert GaussNativeEnergy GaussNativePotential
open GaussCoreDifferential GaussCoreHilbert GaussQuantumMultiplier
open PreparationVacuumMixedFieldReturn PreparationVacuumActualFieldQuantization
open CanonicalGradedSpatialSource
open scoped Matrix Matrix.Norms.L2Operator ContDiff BigOperators Distributions
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : DecidableEq Mode := Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
local instance : FiniteDimensional ℂ SourceMatrix := Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix := Matrix.finiteDimensional

private def scalarMatrix : Scalar →ₗ[ℂ] SourceMatrix where
  toFun s:=Quantum.operatorMatrix (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm s))
  map_add' a b:=by simp only [map_add,diracDualRightChiralYukawaAction_add]
  map_smul' c a:=by simp only [map_smul,diracDualRightChiralYukawaAction_smul,RingHom.id_apply]

theorem familyScalar_smooth : ContDiff ℝ ∞ familyScalar :=
  (scalarMatrix.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp scalarField_smooth

theorem familyConnection_smooth (mu : Fin 4) : ContDiff ℝ ∞ (fun z=>familyConnection z mu) := by
  refine Fin.cases ?_ (fun j=>?_) mu
  · change ContDiff ℝ ∞ (fun _ : SourceCoordinateSlice=>familyConnection GaussHistoryHilbert.sourcePoint.val 0)
    exact contDiff_const
  · have gauge := GaussNativeMatter.nativePrimal.toContinuousLinearMap.contDiff.comp (connectionField_smooth j)
    have generated := (contDiff_const (c:=Quantum.operatorMatrix (diracMatrixMatterAction
      (PointwiseDiracSpinConnectionLift.diracSpinConnectionLift (actual.gravityConnection 0) j.succ)))).add gauge
    convert! generated using 1
    funext z
    exact Quantum.operatorMatrix.map_add _ _

theorem sourceCoframe_smooth : ContDiff ℝ ∞ CanonicalGradedSpatialSource.sourceCoframe := by
  apply contDiff_pi.mpr
  intro a
  apply contDiff_pi.mpr
  intro mu
  fin_cases a <;> fin_cases mu
  · change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>sourceTime 0)
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>0)
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>0)
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>0)
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>sourceTime 1)
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>z.1 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>0)
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>0)
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>sourceTime 2)
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>z.1 1)
    fun_prop
  · change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>z.1 2)
    fun_prop
  · change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>0)
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>sourceTime 3)
    exact contDiff_const
  · change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>z.1 3)
    fun_prop
  · change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>z.1 4)
    fun_prop
  · change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>z.1 5)
    fun_prop

theorem sourceState_smooth : ContDiff ℝ ∞ sourceState :=
  sourceCoframe_smooth.prodMk ((contDiff_pi.mpr familyConnection_smooth).prodMk familyScalar_smooth)

theorem familyReader_smooth (f : Field289) (i : Fin 4) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w=>familyReader f w i) z.val :=
  ((statePhase_smooth (sourceState z.val) (coframe_nondegenerate z)
    (CanonicalGradedSpatialSource.temporal_noncharacteristic z)).comp z.val sourceState_smooth.contDiffAt).mul
      ((densityVariation_smooth f (sourceState z.val) (coframe_nondegenerate z)
        (CanonicalGradedSpatialSource.temporal_noncharacteristic z) i).comp z.val sourceState_smooth.contDiffAt)

def fullFamily (f : Field289) (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FullMatrix :=
  realFourierMatrix (familyReader f z) p

def fiberFamily (f : Field289) (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  quantized (fullFamily f p z)

theorem fullFamily_smooth (f : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fullFamily f p) z.val := by
  have coefficients : ContDiffAt ℝ ∞ (familyReader f) z.val :=
    contDiffAt_pi.mpr (fun i=>familyReader_smooth f i z)
  exact (fourierLinear p).toContinuousLinearMap.contDiff.contDiffAt.comp z.val coefficients

theorem fiberFamily_smooth (f : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fiberFamily f p) z.val :=
  (quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp z.val
    (fullFamily_smooth f p z)

def familyCore (f : Field289) (p : PhysicalMomentum) : QuantumTest →ₗ[ℂ] QuantumTest :=
  action (fullFamily f p) (fiberFamily_smooth f p)

theorem familyCore_value (f : Field289) (p : PhysicalMomentum) (test : QuantumTest)
    (z : SourceCoordinateSlice) : familyCore f p test z=fiberFamily f p z (test z) := rfl

abbrev Localizer := CanonicalGradedLocalCurrent.Localizer
abbrev FiberMap := FockFiber →L[ℂ] FockFiber

def localizedCoefficient (f : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (z : SourceCoordinateSlice) : FiberMap := (phi z:ℂ) • fiberFamily f p z

theorem localized_zero (f : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (z : SourceCoordinateSlice) (outside : z∉tsupport phi) : localizedCoefficient f p phi z=0 := by
  rw [localizedCoefficient,image_eq_zero_of_notMem_tsupport outside,Complex.ofReal_zero]
  apply ContinuousLinearMap.ext
  intro v
  exact zero_smul ℂ _

theorem localized_support (f : Field289) (p : PhysicalMomentum) (phi : Localizer) :
    tsupport (localizedCoefficient f p phi)⊆tsupport phi := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra outside
  exact hz (localized_zero f p phi z outside)

theorem localized_smooth (f : Field289) (p : PhysicalMomentum) (phi : Localizer) :
    ContDiff ℝ ∞ (localizedCoefficient f p phi) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases inside : z∈tsupport phi
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z phi.contDiff.contDiffAt).smul
      (fiberFamily_smooth f p ⟨z,phi.tsupport_subset inside⟩)
  · apply (contDiffAt_const (c:=(0:FiberMap))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport phi).isOpen_compl.mem_nhds inside] with w hw
    exact localized_zero f p phi w hw

def localizedTest (f : Field289) (p : PhysicalMomentum) (phi : Localizer) : 𝓓(physicalChart,FiberMap) where
  toFun:=localizedCoefficient f p phi
  contDiff':=localized_smooth f p phi
  hasCompactSupport':=phi.hasCompactSupport.of_isClosed_subset isClosed_closure (localized_support f p phi)
  tsupport_subset':=(localized_support f p phi).trans phi.tsupport_subset

def localBound (f : Field289) (p : PhysicalMomentum) (phi : Localizer) : ℝ :=
  ‖(localizedTest f p phi:BoundedContinuousFunction SourceCoordinateSlice FiberMap)‖

theorem localBound_nonnegative (f : Field289) (p : PhysicalMomentum) (phi : Localizer) :
    0≤localBound f p phi := norm_nonneg (localizedTest f p phi:BoundedContinuousFunction SourceCoordinateSlice FiberMap)

theorem local_bound (f : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (z : SourceCoordinateSlice) (v : FockFiber) :
    ‖localizedCoefficient f p phi z v‖≤localBound f p phi*‖v‖ :=
  ((localizedCoefficient f p phi z).le_opNorm v).trans (mul_le_mul_of_nonneg_right
    ((localizedTest f p phi:BoundedContinuousFunction SourceCoordinateSlice FiberMap).norm_coe_le_norm z) (norm_nonneg v))

theorem localized_weights (f : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (z : SourceCoordinateSlice) (w : ℕ→ℂ) :
    Commute (GaussFockWeights.weight w) (localizedCoefficient f p phi z) :=
  (weight_commute w (fullFamily f p z)).smul_right (phi z:ℂ)

def localizedCore (f : Field289) (p : PhysicalMomentum) (phi : Localizer) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (localizedCoefficient f p phi) (fun _=>(localized_smooth f p phi).contDiffAt)

def localizedGauss (f : Field289) (p : PhysicalMomentum) (phi : Localizer) : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (localizedCoefficient f p phi) (fun _=>(localized_smooth f p phi).contDiffAt)
    (fun z w=>localized_weights f p phi z w) (localBound f p phi) (localBound_nonnegative f p phi)
    (fun z=>local_bound f p phi z)

theorem localizedGauss_core (f : Field289) (p : PhysicalMomentum) (phi : Localizer) (test : QuantumTest) :
    localizedGauss f p phi (embed test)=embed (localizedCore f p phi test) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ test

theorem localizedCore_exact (f : Field289) (p : PhysicalMomentum) (phi : Localizer) (test : QuantumTest)
    (covers : ∀ z∈tsupport test,phi z=1) : localizedCore f p phi test=familyCore f p test := by
  apply DFunLike.ext
  intro z
  change (phi z:ℂ) • fiberFamily f p z (test z)=fiberFamily f p z (test z)
  by_cases inside : z∈tsupport test
  · rw [covers z inside,Complex.ofReal_one,one_smul]
  · rw [image_eq_zero_of_notMem_tsupport inside,map_zero,smul_zero]

theorem generated_core_localization (f : Field289) (p : PhysicalMomentum) (test : QuantumTest) :
    ∃ phi : Localizer,localizedGauss f p phi (embed test)=embed (familyCore f p test) := by
  obtain ⟨phi,covers,_⟩:=CanonicalGradedLocalCurrent.coreLocalizer_exists test
  exact ⟨phi,by rw [localizedGauss_core,localizedCore_exact f p phi test covers]⟩


theorem localizedGauss_norm (f : Field289) (p : PhysicalMomentum) (phi : Localizer) :
    ‖localizedGauss f p phi‖≤localBound f p phi :=
  GaussBoundedMultiplier.extension_norm (localizedCoefficient f p phi) (fun _=>(localized_smooth f p phi).contDiffAt)
    (fun z w=>localized_weights f p phi z w) (localBound f p phi) (localBound_nonnegative f p phi)
    (fun z=>local_bound f p phi z)

def familyHistory (f : Field289) (p : PhysicalMomentum) (phi : Localizer) :
    GaussUnitaryHistory.HistorySpace →L[ℂ] GaussUnitaryHistory.HistorySpace :=
  GaussUnitaryHistory.reader (localizedGauss f p phi)

theorem familyHistory_core (f : Field289) (p : PhysicalMomentum) (phi : Localizer) (test : QuantumTest) :
    familyHistory f p phi (GaussUnitaryHistory.inclusion (embed test))=
      GaussUnitaryHistory.inclusion (embed (localizedCore f p phi test)) := by
  rw [familyHistory,GaussUnitaryHistory.reader_inclusion,localizedGauss_core]

theorem familyHistory_bound (f : Field289) (p : PhysicalMomentum) (phi : Localizer) :
    ‖familyHistory f p phi‖≤localBound f p phi := by
  apply CanonicalGradedVariation.lift_bound GaussUnitaryHistory.sourceFilter
    (SourceFamilyOperator.constant (localizedGauss f p phi)) (localBound f p phi) (localBound_nonnegative f p phi)
  intro F
  exact localizedGauss_norm f p phi

open GaussComposite GaussComposite.SourceGraph

def preparedFamilyRead (f : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) : ℂ :=
  SourceGraph.response (familyHistory f p phi) left right lc ls rc rs u v

theorem preparedFamilyRead_bound (f : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) :
    ‖preparedFamilyRead f p phi left right lc ls rc rs u v‖≤legBound^2*localBound f p phi*‖u‖*‖v‖ := by
  apply (SourceGraph.response_bound _ left right lc ls rc rs u v).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (familyHistory_bound f p phi) (sq_nonneg _)) (norm_nonneg u)) (norm_nonneg v)

def familyMother (f : Field289) (p : PhysicalMomentum) (z : SourceCoordinateSlice) : YangMills.FullPairing.Mother :=
  Quantum.operatorMatrix.toLinearEquiv.symm (affineMatrix (familyReader f z) p)

theorem family_native_restriction (f : Field289) (p : PhysicalMomentum) (z : SourceCoordinateSlice)
    (v : DiracExteriorMatterCarrier) :
    fiberFamily f p z (CanonicalGradedCharge.oneParticleFiber (SourceRealScalarFock.plusWave (Quantum.coordinates v)))=
      CanonicalGradedCharge.oneParticleFiber (SourceRealScalarFock.plusWave (Quantum.coordinates (familyMother f p z v))) := by
  rw [fiberFamily,CanonicalGradedCharge.quantized_oneParticle,fullFamily,realFourierMatrix,Matrix.fromBlocks_mulVec]
  simp only [SourceRealScalarFock.plusWave,Function.comp_def,Sum.elim_inl,Sum.elim_inr,
    Matrix.zero_mulVec,Matrix.mulVec_zero,add_zero]
  have read:=Quantum.matrix_action (familyMother f p z) v
  have inverse : Quantum.operatorMatrix (familyMother f p z)=affineMatrix (familyReader f z) p :=
    Quantum.operatorMatrix.toLinearEquiv.apply_symm_apply _
  rw [inverse] at read
  exact congrArg (fun u:Quantum.Index→ℂ=>CanonicalGradedCharge.oneParticleFiber
    (Sum.elim u (0:Quantum.Index→ℂ))) read

theorem sourceState_event : sourceState GaussHistoryHilbert.sourcePoint.val=
    (actual.coframe 0,Electromagnetic.CanonicalCoframe.sourceConnection,Electromagnetic.CanonicalCoframe.sourceScalar) := by
  apply Prod.ext
  · exact emitted_source_coframe
  · apply Prod.ext
    · funext mu
      exact familyConnection_source mu
    · exact familyScalar_source


private theorem statePrincipal_event_path (f : Field289) (mu : Fin 4) (t : ℝ) :
    statePrincipal mu (sourceState GaussHistoryHilbert.sourcePoint.val+t • fieldDirection f)=
      densityPrincipalAt mu (coframePath 0 (fieldCoframe f) t) := by
  rw [sourceState_event]
  rfl

theorem principalVariation_event (f : Field289) (mu : Fin 4) :
    principalVariation f mu (sourceState GaussHistoryHilbert.sourcePoint.val)=
      densityPrincipalJet (sourceField f) mu := by
  have generated:=principalVariation_generated f mu (sourceState GaussHistoryHilbert.sourcePoint.val)
    (coframe_nondegenerate GaussHistoryHilbert.sourcePoint)
  have same : (fun t : ℝ=>statePrincipal mu (sourceState GaussHistoryHilbert.sourcePoint.val+t • fieldDirection f))=
      (fun t : ℝ=>densityPrincipalAt mu (coframePath 0 (fieldCoframe f) t)) :=
    funext (statePrincipal_event_path f mu)
  rw [same] at generated
  exact generated.unique (densityPrincipal_parameter (sourceField f) mu)

private theorem stateLower_event_path (f : Field289) (t : ℝ) :
    stateDensityLower (sourceState GaussHistoryHilbert.sourcePoint.val+t • fieldDirection f)=
      (∑ mu : Fin 4,densityPrincipalAt mu (coframePath 0 (fieldCoframe f) t)*connectionPath (sourceField f) mu t)+
        ((|(coframePath 0 (fieldCoframe f) t).det|:ℝ):ℂ) • scalarPath (sourceField f) t := by
  rw [sourceState_event]
  let e:=coframePath 0 (fieldCoframe f) t
  change ((|e.det|:ℝ):ℂ) • ((∑ mu : Fin 4,coefficientMatrix mu e*
    (sourceConnection mu+t • connectionDirection (sourceField f) mu))+
    (sourceScalar+t • scalarDirection (sourceField f)))=_
  simp only [densityPrincipalAt,connectionPath,scalarPath,smul_add,Finset.smul_sum,smul_mul_assoc]
  rfl

theorem lowerVariation_event (f : Field289) :
    lowerVariation f (sourceState GaussHistoryHilbert.sourcePoint.val)=
      lowerFirstPath (sourceField f) (sourceField f) 0 := by
  have generated:=lowerVariation_generated f (sourceState GaussHistoryHilbert.sourcePoint.val)
    (coframe_nondegenerate GaussHistoryHilbert.sourcePoint)
  have same := funext (stateLower_event_path f)
  rw [same] at generated
  have terms (mu : Fin 4):=(densityPrincipal_parameter (sourceField f) mu).mul
    (connectionPath_derivative (sourceField f) mu)
  have scalar := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
    (volume_parameter 0 (fieldCoframe f))).smul (scalarPath_derivative (sourceField f))
  have old := (HasDerivAt.fun_sum (fun mu (_ : mu∈(Finset.univ:Finset (Fin 4)))=>terms mu)).add scalar
  apply generated.unique
  convert! old using 1
  simp only [lowerFirstPath,connectionPath,scalarPath,zero_smul,add_zero,coframePath_zero,
    firstPrincipal_at_source,densityPrincipalAt,Function.comp_apply,Complex.ofRealCLM_apply,
    volumeJetAt,volumeDirection]
  simp only [Finset.sum_add_distrib]
  dsimp only [sourceField]
  abel


private theorem source_lower_coefficients (e : LorentzianCoframe) :
    (∑ mu : Fin 4,coefficientMatrix mu e*sourceConnection mu)+sourceScalar=lowerMatrix 0 0 e := by
  rw [lowerMatrix_coefficients,Fin.sum_univ_succ]
  simp only [Pi.zero_apply,Complex.ofReal_zero,mul_zero,zero_smul,zero_add,
    sourceConnection,sourceScalar]
  abel

theorem stateHamiltonian_event (i : Fin 4) :
    stateHamiltonian (sourceState GaussHistoryHilbert.sourcePoint.val) i=sourceHamiltonianCoefficients i := by
  rw [sourceState_event]
  unfold stateHamiltonian stateLower sourceHamiltonianCoefficients
  rw [source_lower_coefficients]
  rfl

theorem densityVariation_event (f : Field289) (i : Fin 4) :
    familyDensity f GaussHistoryHilbert.sourcePoint.val i=densityFirstPath (sourceField f) (sourceField f) i 0 := by
  simp only [familyDensity,densityVariation,lowerVariation_event,principalVariation_event,stateHamiltonian_event,
    densityFirstPath,coframePath_zero,firstPrincipal_at_source]

private theorem original_lower_density_jet (f : Field289) :
    densitizedLowerDirection 0 0 (fieldCoframe f)=
      (∑ mu : Fin 4,densityPrincipalJet (sourceField f) mu*sourceConnection mu)+
        (volumeDirection 0 (fieldCoframe f):ℂ) • sourceScalar := by
  have original:=densitizedLower_parameter 0 0 (fieldCoframe f)
  have same : (fun t : ℝ=>((|(coframePath 0 (fieldCoframe f) t).det|:ℝ):ℂ) • lowerMatrix 0 0 (coframePath 0 (fieldCoframe f) t))=
      (fun t : ℝ=>(∑ mu : Fin 4,densityPrincipalAt mu (coframePath 0 (fieldCoframe f) t)*sourceConnection mu)+
        ((|(coframePath 0 (fieldCoframe f) t).det|:ℝ):ℂ) • sourceScalar) := by
    funext t
    rw [←source_lower_coefficients]
    simp only [smul_add,Finset.smul_sum,smul_mul_assoc,densityPrincipalAt]
  rw [same] at original
  have generated := (HasDerivAt.fun_sum (fun mu (_ : mu∈(Finset.univ:Finset (Fin 4)))=>
    (densityPrincipal_parameter (sourceField f) mu).mul_const (sourceConnection mu))).add
      ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (volume_parameter 0 (fieldCoframe f))).smul_const sourceScalar)
  apply original.unique
  convert! generated using 1

private theorem original_principal_density_jet (f : Field289) :
    densityPrincipalJet (sourceField f) 0=densitizedPrincipalDirection 0 (fieldCoframe f) := by
  have generated:=densityPrincipal_parameter (sourceField f) 0
  have same : (fun t : ℝ=>densityPrincipalAt 0 (coframePath 0 (fieldCoframe f) t))=
      (fun t : ℝ=>((|(coframePath 0 (fieldCoframe f) t).det|:ℝ):ℂ) • CoframeResponse.principalMatrix (coframePath 0 (fieldCoframe f) t)) := by
    simp only [densityPrincipalAt,principalMatrix_coefficient]
  change HasDerivAt (fun t : ℝ=>densityPrincipalAt 0 (coframePath 0 (fieldCoframe f) t)) _ 0 at generated
  rw [same] at generated
  exact generated.unique (densitizedPrincipal_parameter 0 (fieldCoframe f))

theorem familyDensity_event_native (f : Field289) (i : Fin 4) :
    familyDensity f GaussHistoryHilbert.sourcePoint.val i=fieldDensityCoefficients (sourceField f) i := by
  rw [densityVariation_event]
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [densityFirstPath,Fin.cases_zero,coframePath_zero,firstPrincipal_at_source,
      fieldDensityCoefficients,coframeDensityCoefficients,ite_true,sourceHamiltonianCoefficients]
    rw [original_principal_density_jet,show (sourceField f).coframe=fieldCoframe f from rfl,original_lower_density_jet f]
    simp only [lowerFirstPath,connectionPath,scalarPath,zero_smul,add_zero,coframePath_zero,
      firstPrincipal_at_source,densityPrincipalAt,Finset.sum_add_distrib,smul_add,Finset.smul_sum,smul_mul_assoc]
    dsimp only [sourceField,sourceVolume,volumeJetAt,volumeDirection]
    abel
  · simp only [densityFirstPath,Fin.cases_succ,coframePath_zero,firstPrincipal_at_source,
      fieldDensityCoefficients,coframeDensityCoefficients,Fin.succ_ne_zero,if_false,add_zero,
      sourceHamiltonianCoefficients]
    rw [original_principal_density_jet]
    rfl

theorem familyReader_event_native (f : Field289) (i : Fin 4) :
    familyReader f GaussHistoryHilbert.sourcePoint.val i=readerCoefficient f i := by
  rw [familyReader,familyPhase_source,familyDensity_event_native]
  rfl

theorem fullFamily_event (f : Field289) (p : PhysicalMomentum) :
    fullFamily f p GaussHistoryHilbert.sourcePoint.val=fullFieldSymbol f p := by
  unfold fullFamily fullFieldSymbol
  exact congrArg (fun A=>realFourierMatrix A p) (funext (familyReader_event_native f))


def stateFiber (f : Field289) (p : PhysicalMomentum) (s : ActionState) : FiberMap :=
  quantizer (fourierLinear p (fun i=>statePhase s*densityVariation f s i))

theorem stateFiber_smooth (f : Field289) (p : PhysicalMomentum) (s : ActionState)
    (nondegenerate : s.1.det≠0) (regular : StageNineCurrentCoframeMatterTemporalPrincipal.coframeTemporalPrincipalScalar s.1≠0) :
    ContDiffAt ℝ ∞ (stateFiber f p) s := by
  have coefficients : ContDiffAt ℝ ∞ (fun w=>fun i : Fin 4=>statePhase w*densityVariation f w i) s :=
    contDiffAt_pi.mpr (fun i=>(statePhase_smooth s nondegenerate regular).mul (densityVariation_smooth f s nondegenerate regular i))
  exact (quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp s
    ((fourierLinear p).toContinuousLinearMap.contDiff.contDiffAt.comp s coefficients)

def contactFiber (f g : Field289) (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FiberMap :=
  fderiv ℝ (stateFiber f p) (sourceState z) (fieldDirection g)

theorem actual_fock_contact_derivative (f g : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (fun t : ℝ=>stateFiber f p (sourceState z.val+t • fieldDirection g))
      (quantizer (fourierLinear p (fun i=>phaseVariation g (sourceState z.val)*familyDensity f z.val i+
        familyPhase z.val*(densitySecond f g (sourceState z.val) i+shellSecond f g (sourceState z.val) i)))) 0 := by
  have h : HasDerivAt (fun t : ℝ=>fun i : Fin 4=>statePhase (sourceState z.val+t • fieldDirection g)*
      densityVariation f (sourceState z.val+t • fieldDirection g) i)
      (fun i=>phaseVariation g (sourceState z.val)*familyDensity f z.val i+
        familyPhase z.val*(densitySecond f g (sourceState z.val) i+shellSecond f g (sourceState z.val) i)) 0 :=
    hasDerivAt_pi.mpr (fun i=>actual_normalized_family_derivative f g z i)
  let Q : (Fin 4 → SourceMatrix) →L[ℝ] FiberMap :=
    (quantizer.toContinuousLinearMap.restrictScalars ℝ).comp (fourierLinear p).toContinuousLinearMap
  convert! Q.hasFDerivAt.comp_hasDerivAt 0 h using 1

theorem contactFiber_smooth (f g : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    ContDiffAt ℝ ∞ (contactFiber f g p) z.val :=
  (((stateFiber_smooth f p (sourceState z.val) (coframe_nondegenerate z)
    (CanonicalGradedSpatialSource.temporal_noncharacteristic z)).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const).comp
      z.val sourceState_smooth.contDiffAt

def familyContactCore (f g : Field289) (p : PhysicalMomentum) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (contactFiber f g p) (contactFiber_smooth f g p)

theorem familyContactCore_value (f g : Field289) (p : PhysicalMomentum) (test : QuantumTest)
    (z : SourceCoordinateSlice) : familyContactCore f g p test z=contactFiber f g p z (test z) := rfl

end LowEnergy.PreparationVacuumSourceFieldFamily
