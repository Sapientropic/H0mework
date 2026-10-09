import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstGaugePrimitive

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFirstGaugeBackgroundReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalNormalizedFullField
open PreparationVacuumNativeFieldInjection PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumActualFieldQuantization PreparationVacuumOriginalGreenFeedback
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussNativeMatter GaussHistoryHilbert GaussQuantumMultiplier
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction DiracCliffordRepresentation
open Stage9C.Material.SpinPair FullQuantum.CoframeResponse FullQuantum.StateGreen
open PointwiseLorentzianCoframeJet PointwiseDiracSpinConnectionLift
open Filter Set
open scoped BigOperators Matrix Topology ContDiff Matrix.Norms.L2Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

/-- The generator is the actual first-pole Gt, with its full scalar orbit. -/
def sourceFirstBackgroundAd : SourceMatrix→ₗ[ℂ]SourceMatrix where
  toFun A:=nativePrimal sourceFirstTemporalLie*A-A*nativePrimal sourceFirstTemporalLie
  map_add' A B:=by simp only [mul_add,add_mul];abel
  map_smul' c A:=by simp only [mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

private theorem coefficient_commute (e : LorentzianCoframe) (mu : Fin 4) :
    Commute (nativePrimal sourceFirstTemporalLie) (coefficientMatrix mu e) := by
  change _*(Complex.I • spinCoordinates (inverseCoframeDiracGamma {coframe:=e,derivative:=0} mu))=
    (Complex.I • spinCoordinates (inverseCoframeDiracGamma {coframe:=e,derivative:=0} mu))*_
  rw [mul_smul_comm,smul_mul_assoc,originalSpin_internal_commute]

private theorem inverse_commute (s : ActionState) (valid : s∈validStates) :
    Commute (nativePrimal sourceFirstTemporalLie) (Ring.inverse (principalMatrix s.1)) := by
  let unit:=principalMatrix_regular s.1 valid.2
  have base : Commute (nativePrimal sourceFirstTemporalLie) (↑unit.unit : SourceMatrix) := by
    rw [unit.unit_spec,principalMatrix_coefficient]
    exact coefficient_commute s.1 0
  have inverse:=base.units_inv_right
  rw [←Ring.inverse_unit,unit.unit_spec] at inverse
  exact inverse

private theorem ad_factor (B A : SourceMatrix) (commute : Commute (nativePrimal sourceFirstTemporalLie) B) :
    sourceFirstBackgroundAd (B*A)=B*sourceFirstBackgroundAd A := by
  change _*(B*A)-(B*A)*_=B*(_*A-A*_)
  rw [←mul_assoc _ B,commute.eq]
  noncomm_ring

private theorem lower_jet (s : ActionState) :
    sourceLowerJet s (sourceFirstGaugeState s)=sourceFirstBackgroundAd (stateLower s) := by
  simp only [sourceLowerJet,sourceFirstGaugeState,LinearMap.coe_mk,AddHom.coe_mk,
    sourceCoframeCoefficientJet,mul_zero,zero_mul,neg_zero,map_zero,zero_add]
  change (∑mu : Fin 4,coefficientMatrix mu s.1*sourceFirstBackgroundAd (s.2.1 mu))+
    sourceFirstBackgroundAd s.2.2=sourceFirstBackgroundAd (stateLower s)
  simp only [stateLower,map_add,map_sum,ad_factor _ _ (coefficient_commute _ _)]

/-- The source inverse-principal jet and scalar Yukawa supplement generate the complete Hamiltonian commutator on all four Fourier coefficients. -/
theorem sourceFirstBackgroundHamiltonian (s : ActionState) (valid : s∈validStates) (k : Fin 4) :
    sourceHamiltonianJetMatrix s (sourceFirstGaugeState s) k=sourceFirstBackgroundAd (stateHamiltonian s k) := by
  have inverseZero : sourcePrincipalInverseJet s (sourceFirstGaugeState s)=0 := by
    simp [sourcePrincipalInverseJet,sourceFirstGaugeState,sourceCoframeCoefficientJet]
  cases k using Fin.cases with
  | zero=>
    simp only [sourceHamiltonianJetMatrix,Fin.cases_zero,inverseZero,zero_mul,zero_add,lower_jet,
      stateHamiltonian,timeSymbol,map_smul,ad_factor _ _ (inverse_commute s valid)]
  | succ j=>
    simp only [sourceHamiltonianJetMatrix,Fin.cases_succ]
    rw [inverseZero]
    simp only [zero_mul,sourceFirstGaugeState,LinearMap.coe_mk,AddHom.coe_mk,sourceCoframeCoefficientJet,
      mul_zero,neg_zero,map_zero,add_zero,stateHamiltonian]
    simp only [Fin.cases_succ,ad_factor _ _ (inverse_commute s valid)]
    change 0=Ring.inverse (principalMatrix s.1)*
      (nativePrimal sourceFirstTemporalLie*coefficientMatrix j.succ s.1-
        coefficientMatrix j.succ s.1*nativePrimal sourceFirstTemporalLie)
    rw [(coefficient_commute s.1 j.succ).eq,sub_self,mul_zero]

/-- Independent conjugate matter uses the original opposite branch of the Lie generator. -/
def sourceFirstBackgroundFullGenerator : FullMatrix :=
  Matrix.fromBlocks (nativePrimal sourceFirstTemporalLie) 0 0
    ((nativePrimal sourceFirstTemporalLie).map (starRingEnd ℂ))

/-- The conjugate branch is the actual inverse action on an independent dual endpoint, generated by the full source spectrum. -/
theorem sourceFirstBackground_dual (chi : Module.Dual ℂ DiracExteriorMatterCarrier) :
    Quantum.dualCoordinates (-chi.comp sourceFirstTemporalGenerator)=
      ((nativePrimal sourceFirstTemporalLie).map (starRingEnd ℂ))*ᵥQuantum.dualCoordinates chi := by
  have diagonal : (nativePrimal sourceFirstTemporalLie).map (starRingEnd ℂ)=
      Matrix.diagonal (fun i=> -(sourceFirstWholeWeight i:ℂ)*Complex.I) := by
    rw [←sourceFirstTemporal_native,sourceFirstTemporal_matrix]
    ext i j
    by_cases same : i=j
    · subst j
      simp [Matrix.map_apply]
    · simp [Matrix.map_apply,same]
  rw [diagonal]
  funext i
  rw [Matrix.mulVec_diagonal]
  simp only [Quantum.dualCoordinates,LinearMap.neg_apply,LinearMap.comp_apply,
    sourceFirstTemporal_basis,map_smul,smul_eq_mul,neg_mul]

def sourceFirstBackgroundFullAd : FullMatrix→ₗ[ℂ]FullMatrix where
  toFun A:=sourceFirstBackgroundFullGenerator*A-A*sourceFirstBackgroundFullGenerator
  map_add' A B:=by simp only [mul_add,add_mul];abel
  map_smul' c A:=by simp only [mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

private theorem affine_ad (A : Fin 4→SourceMatrix) (p : CanonicalGradedSpatialSource.PhysicalMomentum) :
    affineMatrix (fun k=>sourceFirstBackgroundAd (A k)) p=sourceFirstBackgroundAd (affineMatrix A p) := by
  simp only [affineMatrix,map_add,map_sum,map_smul]

private theorem blocks_sub (A B C D : SourceMatrix) :
    Matrix.fromBlocks A 0 0 B-Matrix.fromBlocks C 0 0 D=Matrix.fromBlocks (A-C) 0 0 (B-D) := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks]

private theorem fourier_ad (A : Fin 4→SourceMatrix) (p : CanonicalGradedSpatialSource.PhysicalMomentum) :
    fourierLinear p (fun k=>sourceFirstBackgroundAd (A k))=
      sourceFirstBackgroundFullAd (fourierLinear p A) := by
  change Matrix.fromBlocks (affineMatrix (fun k=>sourceFirstBackgroundAd (A k)) p) 0 0
    (-((affineMatrix (fun k=>sourceFirstBackgroundAd (A k)) (-p)).map (starRingEnd ℂ)))=_
  rw [affine_ad,affine_ad]
  simp only [sourceFirstBackgroundAd,sourceFirstBackgroundFullAd,sourceFirstBackgroundFullGenerator,
    LinearMap.coe_mk,AddHom.coe_mk,fourierLinear,realFourierMatrix,Matrix.fromBlocks_multiply,
    mul_zero,zero_mul,add_zero,zero_add,mul_neg,neg_mul,neg_zero,blocks_sub,
    Matrix.map_sub _ (fun a b=>map_sub (starRingEnd ℂ) a b),Matrix.map_mul]
  change Matrix.fromBlocks _ 0 0
    (-((nativePrimal sourceFirstTemporalLie).map (starRingEnd ℂ)*
      (affineMatrix A (-p)).map (starRingEnd ℂ)-(affineMatrix A (-p)).map (starRingEnd ℂ)*
        (nativePrimal sourceFirstTemporalLie).map (starRingEnd ℂ)))=_
  congr 1
  abel

/-- The original action normalization and Fourier negative-momentum branch are consumed, rather than replaced by a new response. -/
theorem sourceFirstBackgroundSymbol (p : CanonicalGradedSpatialSource.PhysicalMomentum)
    (s : ActionState) (valid : s∈validStates) :
    symbolFirst p s (sourceFirstGaugeState s)=sourceFirstBackgroundFullAd (sourceSymbol p s) := by
  rw [←sourceNormalizedEnergySymbol_original p s _ valid,sourceNormalizedEnergySymbol_matrix p s _ valid]
  rw [show sourceHamiltonianJetMatrix s (sourceFirstGaugeState s)=
    (fun k=>sourceFirstBackgroundAd (stateHamiltonian s k)) from funext (sourceFirstBackgroundHamiltonian s valid)]
  exact fourier_ad (stateHamiltonian s) p

/-- This derivative is the restriction of the actual full nine-field configuration ray. -/
theorem sourceFirstBackground_curve (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>sourceSymbol p (configurationState
      (configurationRay (emitter z.val) (sourceFirstGaugePrimitive (emitter z.val)) r) 0))
      (sourceFirstBackgroundFullAd (sourceSymbol p (sourceState z.val))) 0 := by
  have valid : sourceState z.val∈validStates:=⟨coframe_nondegenerate z,CanonicalGradedSpatialSource.temporal_noncharacteristic z⟩
  have generated:=symbol_first_generated p (sourceState z.val) (sourceFirstGaugeState (sourceState z.val)) valid
  simpa only [sourceFirstGaugePrimitive_ray,configurationState_emitter,sourceFirstBackgroundSymbol p _ valid] using generated

/-- The contact differentiates the actual field-dependent gauge tangent; it is not discarded from the Hessian. -/
def sourceFirstBackgroundMixed (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s : ActionState) (f : Field289) : FullMatrix :=
  symbolSecond p s (sourceFirstGaugeState s) (fieldDirection f)+
    symbolFirst p s (sourceFirstGaugeState (fieldDirection f))

private theorem mixed_derivative (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) (f : Field289) :
    HasDerivAt (fun r : ℝ=>symbolFirst p (s+r • fieldDirection f)
      (sourceFirstGaugeState (s+r • fieldDirection f))) (sourceFirstBackgroundMixed p s f) 0 := by
  have outer:=((sourceSymbol_smooth p s valid).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have D:=outer.hasFDerivAt.comp_hasDerivAt_of_eq 0 (state_line s (fieldDirection f)) (by simp)
  have native:=sourceFirstGaugeState.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    (state_line s (fieldDirection f))
  have generated:=D.clm_apply native
  convert! generated using 1
  simp only [sourceFirstBackgroundMixed,symbolSecond,symbolFirst,Function.comp_apply,zero_smul,add_zero,
    LinearMap.coe_toContinuousLinearMap']

/-- The original all289 current Hessian retains both the second variation and its actual gauge contact. -/
theorem sourceFirstBackgroundMixed_return (p : CanonicalGradedSpatialSource.PhysicalMomentum)
    (s : ActionState) (valid : s∈validStates) (f : Field289) :
    sourceFirstBackgroundMixed p s f=sourceFirstBackgroundFullAd (symbolFirst p s (fieldDirection f)) := by
  have left:=mixed_derivative p s valid f
  have right:=(sourceFirstBackgroundFullAd.restrictScalars ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    (symbol_first_generated p s (fieldDirection f) valid)
  have near : ∀ᶠr in 𝓝 (0:ℝ),s+r • fieldDirection f∈validStates :=
    (state_line s (fieldDirection f)).continuousAt.preimage_mem_nhds (by simpa using validStates_open.mem_nhds valid)
  have same : (fun r : ℝ=>symbolFirst p (s+r • fieldDirection f) (sourceFirstGaugeState (s+r • fieldDirection f)))=ᶠ[𝓝 (0:ℝ)]
      (fun r=>sourceFirstBackgroundFullAd (sourceSymbol p (s+r • fieldDirection f))) :=
    near.mono fun r hr=>sourceFirstBackgroundSymbol p _ hr
  exact left.unique (right.congr_of_eventuallyEq same)

/-- Complete CAR and the original current fiber consume this full-background Ward identity, including the computed scalar orbit and mixed contact. -/
theorem sourceFirstBackgroundCurrent_return (p : CanonicalGradedSpatialSource.PhysicalMomentum)
    (z : physicalChart) (f : Field289) :
    quantizer (sourceFirstBackgroundMixed p (sourceState z.val) f)=
      -(quantized sourceFirstBackgroundFullGenerator*fiberFamily f p z.val-
        fiberFamily f p z.val*quantized sourceFirstBackgroundFullGenerator) := by
  have valid : sourceState z.val∈validStates:=⟨coframe_nondegenerate z,CanonicalGradedSpatialSource.temporal_noncharacteristic z⟩
  rw [sourceFirstBackgroundMixed_return p _ valid]
  change quantizer (sourceFirstBackgroundFullGenerator*symbolFirst p (sourceState z.val) (fieldDirection f)-
    symbolFirst p (sourceState z.val) (fieldDirection f)*sourceFirstBackgroundFullGenerator)=_
  rw [paidCoframeQuantizerComm%,symbolFirst_actual]
  change quantized sourceFirstBackgroundFullGenerator*(-fiberFamily f p z.val)-
    (-fiberFamily f p z.val)*quantized sourceFirstBackgroundFullGenerator=_
  ext v
  simp only [mul_apply_eq_comp,neg_apply,
    sub_apply,map_neg]
  abel

end LowEnergy.PreparationPhysicalFirstGaugeBackgroundReturn
