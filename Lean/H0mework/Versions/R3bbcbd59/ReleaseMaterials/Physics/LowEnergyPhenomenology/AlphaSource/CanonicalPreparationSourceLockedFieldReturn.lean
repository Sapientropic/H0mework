import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedPoleCurrent
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceActualCurrentResidues

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalElectromagneticDirection
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineLorentzConnectionVariation PointwiseDiracSpinConnectionLift
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open SourceQuantumScalarChart SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates
open PreparationCoordinates PreparationVacuumLowerClassical PreparationVacuumMixedFieldReturn
open PreparationVacuumSourceFieldFamily PreparationVacuumGaugeSourceInjection
open PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumSourceActionJets PreparationVacuumRawJointFeedback
open PreparationVacuumQuantumSlowResidue PreparationVacuumPhysicalFeedback
open GaussHistoryHilbert GaussQuantumMultiplier GaussCoreDifferential GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumFullFieldRiesz PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumIndependentMomentumReturn
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumElectromagneticIdentity PreparationVacuumFixedMomentumActionReturn
open PreparationVacuumCausalPoleResponse PreparationVacuumOriginalGreenFeedback
open MeasureTheory Set Filter
attribute [local instance] SourceRealScalarFock.branchOrder
open Electromagnetic.CanonicalCoframe DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineDiracDualYukawaSpinJurisdiction SU7ExteriorYukawaMassSpectrum SU7ExteriorBreakingYukawa
open StageNineCoframeLocalDifferentiability StageNineLorentzConnectionVariationDensity
open StageNineDiracDualFormNativeConjugateMatterVariation FullQuantum.StateGreen FullQuantum.CoframeResponse
open scoped BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace Topology
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] sourceMatterActionOperator sourcePoleIndependentDual sourcePolePreparedPrimal
  sourcePoleRead rawForm rawReader finiteRiesz frameTest sourceLockedAction

def sourceSpinSlot (i : Fin 3) : Fin 6 := ⟨3+i.val,by omega⟩

def sourceLockedField (mu : Fin 4) (i : Fin 3) : Field289 :=
  (∑a : Fin 12,rawCoordinates (colorGenerator i) a • gaugeField mu a)+
    fieldUnit (lorentzSlot mu (sourceSpinSlot i))

theorem sourceLockedField_gauge (mu nu : Fin 4) (i : Fin 3) :
    fieldGauge (sourceLockedField mu i) nu=if nu=mu then colorGenerator i else 0 := by
  classical
  have noLorentz (a : Fin 12) : gaugeSlot nu a≠lorentzSlot mu (sourceSpinSlot i) := by
    intro same
    have h:=congrArg Fin.val same
    simp only [gaugeSlot,lorentzSlot,sourceSpinSlot] at h
    omega
  unfold fieldGauge sourceLockedField
  simp only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,gauge_gauge_slot,
    fieldUnit,Pi.single_apply,if_neg (noLorentz _),add_zero]
  by_cases same : nu=mu
  · rw [if_pos same]
    simpa [same] using (raw_original_expansion (colorGenerator i)).symm
  · simp [same]

theorem sourceLockedField_lorentz (mu nu : Fin 4) (i : Fin 3) (a : Fin 6) :
    fieldLorentz (sourceLockedField mu i) nu a=
      if nu=mu ∧ a=sourceSpinSlot i then 1 else 0 := by
  classical
  have noGauge (b : Fin 12) : lorentzSlot nu a≠gaugeSlot mu b := by
    intro same
    have h:=congrArg Fin.val same
    simp only [gaugeSlot,lorentzSlot] at h
    omega
  have sameSlot : lorentzSlot nu a=lorentzSlot mu (sourceSpinSlot i) ↔
      nu=mu ∧ a=sourceSpinSlot i := by
    constructor
    · intro same
      have h:=congrArg Fin.val same
      simp only [lorentzSlot] at h
      constructor <;> apply Fin.ext <;> omega
    · rintro ⟨rfl,rfl⟩
      rfl
  simp only [fieldLorentz,sourceLockedField,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,gaugeField,Pi.single_apply,if_neg (noGauge _),mul_zero,
    Finset.sum_const_zero,zero_add,fieldUnit,sameSlot]

theorem sourceLockedField_coframe (mu : Fin 4) (i : Fin 3) :
    fieldCoframe (sourceLockedField mu i)=0 := by
  ext a nu
  have noGauge (b : Fin 12) : coframeSlot a nu≠gaugeSlot mu b := by
    intro same
    have h:=congrArg Fin.val same
    simp only [coframeSlot,gaugeSlot] at h
    omega
  have noLorentz : coframeSlot a nu≠lorentzSlot mu (sourceSpinSlot i) := by
    intro same
    have h:=congrArg Fin.val same
    simp only [coframeSlot,lorentzSlot] at h
    omega
  simp only [fieldCoframe,sourceLockedField,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,gaugeField,Pi.single_apply,if_neg (noGauge _),mul_zero,
    Finset.sum_const_zero,fieldUnit,if_neg noLorentz,zero_add]
  rfl

theorem sourceLockedField_scalar (mu : Fin 4) (i : Fin 3) :
    fieldScalar (sourceLockedField mu i)=0 := by
  have noGauge (j : Fin 9) (b : Fin 12) : scalarSlot j≠gaugeSlot mu b := by
    intro same
    have h:=congrArg Fin.val same
    simp only [scalarSlot,gaugeSlot] at h
    omega
  have noLorentz (j : Fin 9) : scalarSlot j≠lorentzSlot mu (sourceSpinSlot i) := by
    intro same
    have h:=congrArg Fin.val same
    simp only [scalarSlot,lorentzSlot] at h
    omega
  simp only [fieldScalar,sourceLockedField,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,gaugeField,Pi.single_apply,if_neg (noGauge _ _),mul_zero,
    Finset.sum_const_zero,fieldUnit,if_neg (noLorentz _),zero_add,zero_smul]

theorem sourceLockedField_spinLift (mu nu : Fin 4) (i : Fin 3) :
    diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm
      (fieldLorentz (sourceLockedField mu i))) nu=
      if nu=mu then (1/2 : ℂ) • spinRotation i else 0 := by
  classical
  simp only [diracSpinConnectionLift,loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    sourceLockedField_lorentz]
  by_cases same : nu=mu
  · rw [if_pos same]
    fin_cases i <;>
      simp [same,sourceSpinSlot,spinRotation,lorentzBivectorFirst,lorentzBivectorSecond,
        Fin.sum_univ_six]
  · simp [same]

theorem sourceLockedField_connection (mu nu : Fin 4) (i : Fin 3) :
    connectionDirection (PreparationVacuumMixedFieldReturn.sourceField (sourceLockedField mu i)) nu=
      if nu=mu then Quantum.operatorMatrix (sourceLockedAction i) else 0 := by
  classical
  simp only [connectionDirection,PreparationVacuumMixedFieldReturn.sourceField,sourceLockedField_spinLift,sourceLockedField_gauge]
  by_cases same : nu=mu
  · rw [if_pos same,if_pos same,if_pos same]
    simp only [colorGenerator,p286CoordinateEquiv.symm_apply_apply]
    have scale : diracMatrixMatterAction ((1/2 : ℂ) • spinRotation i)=
        (1/2 : ℂ) • diracMatrixMatterAction (spinRotation i) := by
      apply LinearMap.ext
      intro v
      exact coframeDiracMatrixMatterAction_smul_matrix _ _ v
    rw [scale]
    congr 1
    unfold sourceLockedAction
    abel
  · rw [if_neg same,if_neg same,if_neg same]
    change Quantum.operatorMatrix (diracMatrixMatterAction (0 : DiracMatrix)+
      diracExteriorMotherLieAction (SU7MotherLieAlgebra.p286LieBlockEmbed
        (p286CoordinateEquiv.symm (0 : P286CoordinateCarrier))))=0
    rw [p286CoordinateEquiv.symm.map_zero,SU7MotherGaugeTheory.p286LieBlockEmbed_zero]
    have spin : diracMatrixMatterAction (0 : DiracMatrix)=0 := by
      apply LinearMap.ext
      intro v
      exact diracMatrixMatterAction_zero_matrix v
    have color : diracExteriorMotherLieAction 0=0 := by
      apply LinearMap.ext
      intro v
      exact StageNineP286GaugeConnectionVariationDensity.diracExteriorMotherLieAction_zero_matrix v
    rw [spin,color,zero_add]
    exact Quantum.operatorMatrix.map_zero

theorem sourceLockedField_direction (mu : Fin 4) (i : Fin 3) :
    fieldDirection (sourceLockedField mu i)=
      (0,(fun nu=>if nu=mu then Quantum.operatorMatrix (sourceLockedAction i) else 0),0) := by
  unfold fieldDirection
  rw [sourceLockedField_coframe]
  have scalar : scalarDirection (PreparationVacuumMixedFieldReturn.sourceField (sourceLockedField mu i))=0 := by
    unfold scalarDirection PreparationVacuumMixedFieldReturn.sourceField
    rw [sourceLockedField_scalar,map_zero]
    have zero:=diracDualRightChiralYukawaAction_smul (0 : ℂ) (0 : ExteriorBreakingScalarCarrier)
    simp only [zero_smul] at zero
    rw [zero]
    exact Quantum.operatorMatrix.map_zero
  rw [scalar]
  exact Prod.ext rfl (Prod.ext (funext (fun nu=>sourceLockedField_connection mu nu i)) rfl)

theorem sourceLockedField_density (mu : Fin 4) (i : Fin 3) (s : ActionState)
    (nondegenerate : s.1.det≠0) (k : Fin 4) :
    densityVariation (sourceLockedField mu i) s k=
      if k=0 then stateVolume s •
        (FullQuantum.CoframeResponse.coefficientMatrix mu s.1*Quantum.operatorMatrix (sourceLockedAction i)) else 0 := by
  let A:=Quantum.operatorMatrix (sourceLockedAction i)
  let curve (r : ℝ) : ActionState:=s+r • fieldDirection (sourceLockedField mu i)
  have coframe (r : ℝ) : (curve r).1=s.1 := by
    dsimp only [curve]
    rw [sourceLockedField_direction]
    change s.1+r • 0=s.1
    simp only [smul_zero,add_zero]
  have scalar (r : ℝ) : (curve r).2.2=s.2.2 := by
    dsimp only [curve]
    rw [sourceLockedField_direction]
    change s.2.2+r • 0=s.2.2
    simp only [smul_zero,add_zero]
  have connection (r : ℝ) (nu : Fin 4) : (curve r).2.1 nu=s.2.1 nu+
      if nu=mu then r • A else 0 := by
    dsimp only [curve]
    rw [sourceLockedField_direction]
    change s.2.1 nu+r • (if nu=mu then A else 0)=_
    rw [smul_ite,smul_zero]
  have volume (r : ℝ) : stateVolume (curve r)=stateVolume s := by
    unfold stateVolume
    rw [coframe]
  have lower (r : ℝ) : stateLower (curve r)=stateLower s+
      r • (FullQuantum.CoframeResponse.coefficientMatrix mu s.1*A) := by
    unfold stateLower
    simp only [coframe,scalar,connection,mul_add,mul_ite,mul_zero,
      Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,mul_smul_comm]
    abel
  have principal (r : ℝ) (nu : Fin 4) : statePrincipal nu (curve r)=statePrincipal nu s := by
    unfold statePrincipal
    rw [volume,coframe]
  let D : SourceMatrix:=if k=0 then stateVolume s •
    (FullQuantum.CoframeResponse.coefficientMatrix mu s.1*A) else 0
  have held (r : ℝ) : heldDensityCoefficient s (curve r) k=heldDensityCoefficient s s k+r • D := by
    unfold heldDensityCoefficient stateDensityLower D
    rw [volume,lower]
    simp only [principal,smul_add]
    refine Fin.cases ?_ (fun j=>?_) k
    · simp only [Fin.cases_zero,if_true]
      rw [smul_comm (stateVolume s) r]
      abel
    · simp
  have affine:=((hasDerivAt_id (0 : ℝ)).smul_const D).const_add (heldDensityCoefficient s s k)
  have generated : HasDerivAt (fun r : ℝ=>heldDensityCoefficient s (curve r) k) D 0 := by
    simpa only [held,one_smul,id_eq] using affine
  exact (densityVariation_generated (sourceLockedField mu i) s nondegenerate k).unique generated

def sourceLockedCoefficient (mu : Fin 4) (i : Fin 3) (s : ActionState) : SourceMatrix :=
  densityActionMatrix*(stateVolume s •
    (coefficientMatrix mu s.1*Quantum.operatorMatrix (sourceLockedAction i)))

def sourceLockedSymbol (mu : Fin 4) (i : Fin 3) (s : ActionState) : FullMatrix :=
  oppositeDual*SourceRealScalarFock.branches (sourceLockedCoefficient mu i s)

theorem sourceLockedSymbol_generated (mu : Fin 4) (i : Fin 3) (p : CanonicalGradedSpatialSource.PhysicalMomentum)
    (s : ActionState) (nondegenerate : s.1.det≠0) :
    rawActionSymbol (sourceLockedField mu i) p s=sourceLockedSymbol mu i s := by
  unfold rawActionSymbol rawFourier
  simp only [sourceLockedField_density mu i s nondegenerate]
  change oppositeDual*realFourierMatrix
    (fun k=>densityActionMatrix*(if k=0 then stateVolume s •
      (coefficientMatrix mu s.1*Quantum.operatorMatrix (sourceLockedAction i)) else 0)) p=_
  simp [realFourierMatrix,affineMatrix,
    sourceLockedCoefficient,sourceLockedSymbol,SourceRealScalarFock.branches]

def sourceLockedFiber (mu : Fin 4) (i : Fin 3) (z : SourceCoordinateSlice) :=
  quantizer (sourceLockedSymbol mu i (sourceState z))

theorem sourceLockedFiber_generated (mu : Fin 4) (i : Fin 3)
    (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : physicalChart) :
    rawStateFiber (sourceLockedField mu i) p (sourceState z.val)=sourceLockedFiber mu i z.val := by
  rw [←rawActionSymbol_actual,sourceLockedSymbol_generated mu i p (sourceState z.val)
    (coframe_nondegenerate z)]
  rfl



def sourceLockedForm (mu : Fin 4) (i : Fin 3) (a b : QuantumTest) : ℂ :=
  ∫z,pairSample z (a z) (sourceLockedFiber mu i z (b z)) ∂configurationMeasure

theorem sourceLockedForm_generated (mu : Fin 4) (i : Fin 3) (p : PhysicalMomentum)
    (a b : QuantumTest) :
    rawForm (sourceLockedField mu i) p a b 0=sourceLockedForm mu i a b := by
  rw [rawForm_original]
  unfold sourceLockedForm
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  by_cases inside : z∈tsupport a
  · dsimp only
    rw [sourceLockedFiber_generated mu i p ⟨z,a.tsupport_subset inside⟩]
  · simp only [image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]

def sourceLockedReader (mu : Fin 4) (i : Fin 3) (F : GaussUnitaryHistory.Index) : H→L[ℂ] H :=
  finiteRiesz F (fun a b=>sourceLockedForm mu i (frameTest F a) (frameTest F b))

theorem sourceLockedReader_generated (mu : Fin 4) (i : Fin 3) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) :
    rawReader (sourceLockedField mu i) p F 0=sourceLockedReader mu i F := by
  unfold rawReader sourceLockedReader
  congr 1
  funext a b
  exact sourceLockedForm_generated mu i p _ _

def sourceLockedKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (i : Fin 3) (t : ℝ) : H→L[ℂ] H :=
  physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0*
    sourceLockedReader mu i q.F*jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0

theorem sourceLockedKernel_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (i : Fin 3) (t : ℝ) :
    fiveKernel (sourceLockedField mu i) pR (pL-pR) q.F q.z q.w t 0=
      sourceLockedKernel q pL pR mu i t := by
  unfold fiveKernel sourceLockedKernel
  rw [add_sub_cancel,sourceLockedReader_generated]

private theorem real_field_basis (f : Field289) : f=∑j : Fin 289,f j • fieldUnit j := by
  funext k
  simp [fieldUnit,Finset.sum_apply,Pi.single_apply]

/-- The joint direction is evaluated by the original real action derivative and independent dual. -/
theorem sourceLockedEuler_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (mu : Fin 4) (i : Fin 3) (t : ℝ) :
    ∑j : Fin 289,(sourceLockedField mu i j:ℂ)*sourcePoleActionEuler q pL pR l r 0 t j=
      -sourcePoleRead q.epsilon q.precision pL pR l r
        (sourceLockedKernel q pL pR mu i t) := by
  have basis:=real_field_basis (sourceLockedField mu i)
  have coordinates : sourcePoleActionInsertion q pL pR l r (sourceLockedField mu i) 0 t=
      ∑j : Fin 289,(sourceLockedField mu i j:ℂ)*
        sourcePoleActionInsertion q pL pR l r (fieldUnit j) 0 t := by
    let v:=sourcePolePreparedPrimal q.epsilon q.precision pR r (sourcePhysicalMaterialPoint q pL pR) 0 t
    let dual: H→L[ℝ] ℂ:=(sourcePoleIndependentDual q.epsilon q.precision pL l
      (sourcePhysicalMaterialPoint q pL pR) 0 t).restrictScalars ℝ
    let evaluation: (H→L[ℂ] H)→L[ℝ] H:=(ContinuousLinearMap.apply ℂ H v).restrictScalars ℝ
    let action: Field289→L[ℝ] ℂ:=
      dual.comp (evaluation.comp (fderiv ℝ (sourceMatterActionOperator pR q.F) 0))
    have generated:=congrArg action basis
    rw [map_sum] at generated
    simp only [map_smul,Complex.real_smul] at generated
    exact generated
  have actual:=(sourcePoleActionInsertion_near q pL pR l r (sourceLockedField mu i) t).self_of_nhds
  dsimp only at actual
  rw [sourcePolePreparedDensity_source] at actual
  change sourcePoleActionInsertion q pL pR l r (sourceLockedField mu i) 0 t=
    sourcePoleRead q.epsilon q.precision pL pR l r
      (fiveKernel (sourceLockedField mu i) pR (pL-pR) q.F q.z q.w t 0) at actual
  rw [sourceLockedKernel_generated] at actual
  simp only [sourcePoleActionEuler,mul_neg,Finset.sum_neg_distrib]
  exact congrArg Neg.neg (coordinates.symm.trans actual)

/-- This linear reader keeps the original Lorentz slot in addition to all gauge coordinates. -/
def sourceLockedCovector (mu : Fin 4) (i : Fin 3) : (Fin 289→ℂ)→L[ℂ] ℂ :=
  ∑j : Fin 289,(ContinuousLinearMap.proj j : (Fin 289→ℂ)→L[ℂ] ℂ).smulRight
    (sourceLockedField mu i j:ℂ)

theorem sourceLockedCovector_apply (mu : Fin 4) (i : Fin 3) (J : Fin 289→ℂ) :
    sourceLockedCovector mu i J=∑j : Fin 289,(sourceLockedField mu i j:ℂ)*J j := by
  simp only [sourceLockedCovector,sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,mul_comm]

theorem sourceLockedHalf_residue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (l r : RestStateIndex) (mu : Fin 4) (i : Fin 3)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun d : ℝ=>((d:ℂ)^2)*sourceLockedCovector mu i
      (returnedHalfCurrent q (-(d • n)) 0 l r ((d:ℂ)*zeta)))
      (𝓝[>] 0) (𝓝 (sourceLockedCovector mu i (sourceFullCurrentResidue q n zeta l r))) := by
  have limit:=(sourceLockedCovector mu i).continuous.tendsto _ |>.comp
    (sourceFullCurrent_residue q n zeta positive l r nonrealL nonrealR)
  simpa only [Function.comp_def,map_smul,smul_eq_mul] using limit

end LowEnergy.PreparationVacuumPhysicalElectromagneticDirection
