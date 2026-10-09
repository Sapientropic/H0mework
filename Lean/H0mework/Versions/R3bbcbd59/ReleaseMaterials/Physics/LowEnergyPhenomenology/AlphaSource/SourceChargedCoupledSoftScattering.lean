import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedSoftCurrentReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedSoftScatteringReturn
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
local instance chargedSoftPairQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic PreparationVacuumWholeOrigin

open PreparationPhysicalScatteringFrequencyWard

attribute [local irreducible] PreparationVacuumMixedFieldReturn.sourceField originalComplexDirection originalTransferPair
  complexCoefficients complexFrequencyCoefficients complexMixedCoefficients realReaderCoefficients realMixedCoefficients

abbrev SourceFieldParameters := FourFields × PhysicalMomentum

private theorem density_row_continuous :
    Continuous (fun v : Fin 289→ℂ=>complexCoefficients (originalComplexDirection v)) := by
  apply continuous_pi
  intro i
  have identity : (fun v : Fin 289→ℂ=>complexCoefficients (originalComplexDirection v) i)=
      fun v=>realDensityCoefficients i (fun j=>(v j).re)+
        Complex.I • realDensityCoefficients i (fun j=>(v j).im) := by
    funext v
    simp only [complexCoefficients,originalComplexDirection,realDensityCoefficients_source]
  rw [identity]
  exact ((LinearMap.continuous_of_finiteDimensional (realDensityCoefficients i)).comp
    (continuous_pi fun j=>Complex.continuous_re.comp (continuous_apply j))).add
    (((LinearMap.continuous_of_finiteDimensional (realDensityCoefficients i)).comp
      (continuous_pi fun j=>Complex.continuous_im.comp (continuous_apply j))).const_smul Complex.I)

private theorem frequency_row_continuous :
    Continuous (fun v : Fin 289→ℂ=>complexFrequencyCoefficients (originalComplexDirection v)) := by
  apply continuous_pi
  intro k
  simp_rw [sourceScatteringFrequency_complex]
  exact continuous_finsetSum _ fun j _=>(continuous_apply j).smul continuous_const

private theorem shifted_row_continuous :
    Continuous (fun x : (Fin 4→FiberOperators) × PhysicalMomentum=>shiftCoefficients x.1 x.2) := by
  apply continuous_pi
  intro i
  induction i using Fin.cases with
  | zero =>
    simp only [shiftCoefficients,Fin.cases_zero]
    exact ((continuous_apply 0).comp continuous_fst).add
      (continuous_finsetSum _ fun j _=>
        (Complex.continuous_ofReal.comp ((continuous_apply j).comp continuous_snd)).smul
          ((continuous_apply j.succ).comp continuous_fst))
  | succ j =>
    simp only [shiftCoefficients,Fin.cases_succ]
    exact (continuous_apply _).comp continuous_fst

private theorem adjoint_row_continuous : Continuous (fun A : Fin 4→FiberOperators=>adjointCoefficients A) :=
  continuous_pi fun i=>ContinuousLinearMap.adjoint.continuous.comp (continuous_apply i)

/-- All four full fields and the physical transfer vary together in the original prepared scattering pair. -/
theorem sourcePreparedScatteringPair_joint_continuous (sideL edgeL sideR edgeR : Fin 2) (time age : ℝ) :
    Continuous (fun x : SourceFieldParameters=>sourcePreparedScatteringPair sideL edgeL sideR edgeR
      (originalTransferPair x.1.1.1 x.1.1.2) (originalTransferPair x.1.2.1 x.1.2.2) x.2 time age) := by
  let reader:=fun x : SourceFieldParameters=>realReaderCoefficients (originalTransferPair x.1.1.1 x.1.1.2) x.2
  let backward:=fun x : SourceFieldParameters=>
    shiftCoefficients (adjointCoefficients (complexFrequencyCoefficients (originalComplexDirection x.1.2.2))) x.2
  have sourceAp : Continuous (fun x : SourceFieldParameters=>x.1.1.1) := continuous_fst.fst.fst
  have sourceAn : Continuous (fun x : SourceFieldParameters=>x.1.1.2) := continuous_fst.fst.snd
  have sourceBp : Continuous (fun x : SourceFieldParameters=>x.1.2.1) := continuous_fst.snd.fst
  have sourceBn : Continuous (fun x : SourceFieldParameters=>x.1.2.2) := continuous_fst.snd.snd
  have transfer : Continuous (fun x : SourceFieldParameters=>x.2) := continuous_snd
  have fieldsContinuous : Continuous (fun x : SourceFieldParameters=>x.1) := continuous_fst
  have readerContinuous : Continuous reader := by
    have identity : reader=(fun x : SourceFieldParameters=>(2:ℂ)⁻¹ •
      (complexCoefficients (originalComplexDirection x.1.1.2)+
        adjointCoefficients (shiftCoefficients (complexCoefficients (originalComplexDirection x.1.1.1)) (-x.2)))) := by
      funext x i
      simp only [reader,realReaderCoefficients,originalTransferPair,Pi.smul_apply,Pi.add_apply]
    rw [identity]
    exact ((density_row_continuous.comp sourceAn).add
      (adjoint_row_continuous.comp (shifted_row_continuous.comp
        ((density_row_continuous.comp sourceAp).prodMk transfer.neg)))).const_smul ((2:ℂ)⁻¹)
  have backwardContinuous : Continuous backward :=
    shifted_row_continuous.comp ((adjoint_row_continuous.comp
      (frequency_row_continuous.comp sourceBn)).prodMk transfer)
  have first := continuous_finsetSum Finset.univ fun i _=>continuous_finsetSum Finset.univ fun j _=>
    (sourcePreparedOrderedCAR_joint_continuous sideL edgeL sideR edgeR age time i j).comp
      (backwardContinuous.prodMk (readerContinuous.prodMk transfer.neg))
  have second := continuous_finsetSum Finset.univ fun i _=>continuous_finsetSum Finset.univ fun j _=>
    (sourcePreparedOrderedCAR_joint_continuous sideL edgeL sideR edgeR time age i j).comp
      (readerContinuous.prodMk ((frequency_row_continuous.comp sourceBp).prodMk transfer))
  have contact : Continuous (fun x : SourceFieldParameters=>inner ℂ (sourceActualScatteringInput sideL edgeL)
      (fieldMixedContact (originalTransferPair x.1.1.1 x.1.1.2) (originalTransferPair x.1.2.1 x.1.2.2) time
        (sourceActualScatteringInput sideR edgeR))) :=
    continuous_const.inner (((fieldMixedContact_joint_cts time).comp fieldsContinuous).clm_apply continuous_const)
  simpa only [sourcePreparedScatteringPair_fullCAR,reader,backward,originalTransferPair,
    Function.comp_def,Pi.mul_apply,Pi.sub_apply,Pi.neg_apply] using
    ((continuous_const (y:=Complex.I)).mul (first.sub second)).prodMk contact

def sourceChargedSoftFields (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (e : scaleDomain) : FourFields :=
  ((sourceChargedSoftField (legs 0) branch n unit e,sourceChargedSoftField (legs 1) branch n unit e),
    (sourceChargedSoftField (legs 2) branch n unit e,sourceChargedSoftField (legs 3) branch n unit e))

def sourceChargedSoftFieldsLimit (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) : FourFields :=
  ((sourceChargedSoftFieldLimit (legs 0) branch,sourceChargedSoftFieldLimit (legs 1) branch),
    (sourceChargedSoftFieldLimit (legs 2) branch,sourceChargedSoftFieldLimit (legs 3) branch))

def sourceChargedCoupledScattering (sideL edgeL sideR edgeR : Fin 2) (legs : Fin 4→SourceChargedSoftLeg)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (time age : ℝ) (e : scaleDomain) : ℂ × ℂ :=
  let fields:=sourceChargedSoftFields legs branch n unit e
  sourcePreparedScatteringPair sideL edgeL sideR edgeR
    (originalTransferPair fields.1.1 fields.1.2) (originalTransferPair fields.2.1 fields.2.2) (e.val^2 • n) time age

attribute [local irreducible] sourceChargedSoftField sourceChargedSoftFieldLimit
  sourcePreparedScatteringPair sourceChargedSoftFields sourceChargedSoftFieldsLimit

/-- The actual (2ω)-normalized source fields and physical transfer approach their joint limit in the same full ordered/contact pair. -/
theorem sourceChargedCoupledScattering_tendsto (sideL edgeL sideR edgeR : Fin 2) (legs : Fin 4→SourceChargedSoftLeg)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (time age : ℝ)
    (nonrealL : ∀i,(legs i).q.z.im≠0) (nonrealR : ∀i,(legs i).q.w.im≠0) :
    Tendsto (sourceChargedCoupledScattering sideL edgeL sideR edgeR legs branch n unit time age) scaleApproach
      (𝓝 (sourcePreparedScatteringPair sideL edgeL sideR edgeR
        (originalTransferPair (sourceChargedSoftFieldsLimit legs branch).1.1 (sourceChargedSoftFieldsLimit legs branch).1.2)
        (originalTransferPair (sourceChargedSoftFieldsLimit legs branch).2.1 (sourceChargedSoftFieldsLimit legs branch).2.2)
        0 time age)) := by
  have leg (i : Fin 4) :
      Tendsto (sourceChargedSoftField (legs i) branch n unit) scaleApproach
        (𝓝 (sourceChargedSoftFieldLimit (legs i) branch)) :=
    sourceChargedSoftField_tendsto (legs i) branch n unit (nonrealL i) (nonrealR i)
  have fields : Tendsto (sourceChargedSoftFields legs branch n unit) scaleApproach
      (𝓝 (sourceChargedSoftFieldsLimit legs branch)) := by
    unfold sourceChargedSoftFields sourceChargedSoftFieldsLimit
    exact (leg 0 |>.prodMk_nhds (leg 1)).prodMk_nhds (leg 2 |>.prodMk_nhds (leg 3))
  have transfer : Tendsto (fun e : scaleDomain=>e.val^2 • n) scaleApproach (𝓝 (0:PhysicalMomentum)) := by
    simpa only [zero_pow (by decide : 2≠0),zero_smul] using (scaleVal_tendsto.pow 2).smul (tendsto_const_nhds (x:=n))
  have generated := (sourcePreparedScatteringPair_joint_continuous sideL edgeL sideR edgeR time age).tendsto
    (sourceChargedSoftFieldsLimit legs branch,0) |>.comp (fields.prodMk_nhds transfer)
  exact generated.congr' (Eventually.of_forall fun e=>by rfl)

/-- These are the actual physical-frequency residues before the original frequency-to-mode normalization. -/
def sourceChargedPhysicalResidueScattering (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (time age : ℝ) (e : scaleDomain) : ℂ × ℂ :=
  let field:=fun i : Fin 4=>actualSoftResidue (legs i).q branch n unit
    (sourceChargedRestIndex (legs i).sideL (legs i).edgeL)
    (sourceChargedRestIndex (legs i).sideR (legs i).edgeR) (legs i).window e
  sourcePreparedScatteringPair sideL edgeL sideR edgeR
    (originalTransferPair (field 0) (field 1)) (originalTransferPair (field 2) (field 3)) (e.val^2 • n) time age

/-- The same real source factor 2ω appears once at each vertex, including the original mixed contact. -/
theorem sourceChargedCoupledScattering_normalization (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (time age : ℝ) (e : scaleDomain) :
    sourceChargedCoupledScattering sideL edgeL sideR edgeR legs branch n unit time age e=
      (2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ))^2 •
        sourceChargedPhysicalResidueScattering sideL edgeL sideR edgeR legs branch n unit time age e := by
  have scalar : (2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ))=
      ((2*sourceFrequency e.val (sourceSheet branch n unit e.val):ℝ):ℂ) := (Complex.ofReal_mul (2:ℝ) _).symm
  simp only [sourceChargedCoupledScattering,sourceChargedSoftFields,sourceChargedSoftField,
    sourceChargedPhysicalResidueScattering,scalar]
  simp only [sourcePreparedScatteringPair,fieldTwoTimeKernel_smul,fieldMixedContact_smul,
    sourceActualScatteringRead_source,Prod.smul_mk,smul_apply,inner_smul_right,smul_eq_mul]

/-- The two original source poles approach their full ordered/contact response together with epsilon-squared physical transfer. -/
theorem sourceChargedPhysicalResidueScattering_soft (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (time age : ℝ)
    (nonrealL : ∀i,(legs i).q.z.im≠0) (nonrealR : ∀i,(legs i).q.w.im≠0) :
    Tendsto (fun e : scaleDomain=>(2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ))^2 •
      sourceChargedPhysicalResidueScattering sideL edgeL sideR edgeR legs branch n unit time age e) scaleApproach
      (𝓝 (sourcePreparedScatteringPair sideL edgeL sideR edgeR
        (originalTransferPair (sourceChargedSoftFieldsLimit legs branch).1.1 (sourceChargedSoftFieldsLimit legs branch).1.2)
        (originalTransferPair (sourceChargedSoftFieldsLimit legs branch).2.1 (sourceChargedSoftFieldsLimit legs branch).2.2)
        0 time age)) :=
  (sourceChargedCoupledScattering_tendsto sideL edgeL sideR edgeR legs branch n unit time age nonrealL nonrealR).congr'
    (Eventually.of_forall fun e=>sourceChargedCoupledScattering_normalization sideL edgeL sideR edgeR legs branch n unit time age e)

end LowEnergy.PreparationPhysicalChargedSoftScatteringReturn
