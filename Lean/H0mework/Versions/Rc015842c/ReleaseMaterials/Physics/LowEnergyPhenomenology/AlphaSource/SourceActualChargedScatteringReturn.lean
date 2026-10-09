import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalFullFieldResidue
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualChargedScatteringPreparation

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalJointGeneratorEnergyReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace FullQuantum.PerturbedGreen Electromagnetic.CanonicalCoframe
open GaussComposite.PhysicalFullFieldScattering PreparationVacuumFullSlowFieldResponse
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalFilteredChargeVoltage
open MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators

/-- The original scattering coordinate legs return the same already generated current observable. -/
theorem sourceActualScatteringRead_inserted (sideL edgeL sideR edgeR : Fin 2) (A : SpatialOperators) :
    sourceActualScatteringRead sideL edgeL sideR edgeR
      ((coordinateLeg 0).adjoint * A * coordinateLeg 0)=
        sourceChargedQuantumRead sideL edgeL sideR edgeR A := by
  rw [sourceActualScatteringRead_source,sourceChargedQuantumRead_generated]
  simp only [mul_apply_eq_comp,ContinuousLinearMap.adjoint_inner_right,sourceActualScatteringInput_return]

/-- Each actual normalized scattering external leg carries the original canonical current charge. -/
theorem sourceActualScatteringRead_charge (side edge : Fin 2) :
    sourceActualScatteringRead side edge side edge
      ((coordinateLeg 0).adjoint * sourceFilteredChargeOperator * coordinateLeg 0)=
        -(Stage10.ActionNormalization.phaseMomentum:ℂ) := by
  rw [sourceActualScatteringRead_inserted,sourceFilteredCurrent_quantum,sourceFilteredCurrent_total]

/-- Both original operator components consume the same four generated causal source legs. -/
def sourceActualScatteringKernel (Ap An Bp Bn : CausalFieldLeg) (shift : Fin 3→ℝ) (time age d : ℝ) :
    SpatialOperators × SpatialOperators :=
  (fieldTwoTimeKernel (causalTransfer Ap An d) (causalTransfer Bp Bn d) shift time age,
    fieldMixedContact (causalTransfer Ap An d) (causalTransfer Bp Bn d) time)

def sourceActualScatteringKernelResidue (Ap An Bp Bn : CausalFieldLeg) (shift : Fin 3→ℝ) (time age : ℝ) :
    SpatialOperators × SpatialOperators :=
  (fieldTwoTimeKernel (residueTransfer Ap An) (residueTransfer Bp Bn) shift time age,
    fieldMixedContact (residueTransfer Ap An) (residueTransfer Bp Bn) time)

/-- The existing source leg limits and existing operator continuity generate the complete operator residue. -/
theorem sourceActualScatteringKernel_residue (Ap An Bp Bn : CausalFieldLeg)
    (shift : Fin 3→ℝ) (time age : ℝ) :
    Tendsto (fun d : ℝ=>(d:ℂ)^6 • sourceActualScatteringKernel Ap An Bp Bn shift time age d)
      (𝓝[>] 0) (𝓝 (sourceActualScatteringKernelResidue Ap An Bp Bn shift time age)) := by
  have leg (a : CausalFieldLeg) :
      Tendsto (fun d : ℝ=>(d:ℂ)^3 • causalField a d) (𝓝[>] 0) (𝓝 (residueField a)) :=
    sourceJointCausalField_residue a.q a.wave a.frequency a.left a.right a.nonrealL a.nonrealR
  have fields : Tendsto (fun d : ℝ=>
      (((d:ℂ)^3 • causalField Ap d,(d:ℂ)^3 • causalField An d),
        ((d:ℂ)^3 • causalField Bp d,(d:ℂ)^3 • causalField Bn d)))
      (𝓝[>] 0) (𝓝 ((residueField Ap,residueField An),(residueField Bp,residueField Bn))) :=
    ((leg Ap).prodMk_nhds (leg An)).prodMk_nhds ((leg Bp).prodMk_nhds (leg Bn))
  have continuous : Continuous (fun p : FourFields=>
      (fieldTwoTimeKernel (originalTransferPair p.1.1 p.1.2) (originalTransferPair p.2.1 p.2.2) shift time age,
        fieldMixedContact (originalTransferPair p.1.1 p.1.2) (originalTransferPair p.2.1 p.2.2) time)) :=
    (fieldTwoTimeKernel_joint_cts shift time age).prodMk (fieldMixedContact_joint_cts time)
  have composed:=continuous.tendsto ((residueField Ap,residueField An),(residueField Bp,residueField Bn)) |>.comp fields
  have kernel (d : ℝ) :
      fieldTwoTimeKernel (originalTransferPair ((d:ℂ)^3 • causalField Ap d) ((d:ℂ)^3 • causalField An d))
        (originalTransferPair ((d:ℂ)^3 • causalField Bp d) ((d:ℂ)^3 • causalField Bn d)) shift time age=
          (d:ℂ)^6 • fieldTwoTimeKernel (causalTransfer Ap An d) (causalTransfer Bp Bn d) shift time age := by
    have scaled:=fieldTwoTimeKernel_smul (d^3) (causalField Ap d) (causalField An d) (causalField Bp d) (causalField Bn d) shift time age
    rw [Complex.ofReal_pow,←pow_mul] at scaled
    exact scaled
  have contact (d : ℝ) :
      fieldMixedContact (originalTransferPair ((d:ℂ)^3 • causalField Ap d) ((d:ℂ)^3 • causalField An d))
        (originalTransferPair ((d:ℂ)^3 • causalField Bp d) ((d:ℂ)^3 • causalField Bn d)) time=
          (d:ℂ)^6 • fieldMixedContact (causalTransfer Ap An d) (causalTransfer Bp Bn d) time := by
    have scaled:=fieldMixedContact_smul (d^3) (causalField Ap d) (causalField An d) (causalField Bp d) (causalField Bn d) time
    rw [Complex.ofReal_pow,←pow_mul] at scaled
    exact scaled
  simpa only [Function.comp_def,kernel,contact,sourceActualScatteringKernel,
    sourceActualScatteringKernelResidue,residueTransfer,Prod.smul_mk] using composed

/-- The external preparation uses each actual charged maker and its own proved Dirac normalization. -/
def sourceActualChargedScatteringPair (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : CausalFieldLeg) (shift : Fin 3→ℝ) (time age d : ℝ) : ℂ × ℂ :=
  sourcePreparedScatteringPair sideL edgeL sideR edgeR (causalTransfer Ap An d) (causalTransfer Bp Bn d) shift time age

def sourceActualChargedScatteringResidue (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : CausalFieldLeg) (shift : Fin 3→ℝ) (time age : ℝ) : ℂ × ℂ :=
  sourcePreparedScatteringPair sideL edgeL sideR edgeR (residueTransfer Ap An) (residueTransfer Bp Bn) shift time age

/-- Same actual quantum state, two independent charged preparations, full ordered vertex and separate direct contact. -/
theorem sourceActualChargedScattering_residue (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : CausalFieldLeg) (shift : Fin 3→ℝ) (time age : ℝ) :
    Tendsto (fun d : ℝ=>(d:ℂ)^6 • sourceActualChargedScatteringPair sideL edgeL sideR edgeR
      Ap An Bp Bn shift time age d) (𝓝[>] 0)
      (𝓝 (sourceActualChargedScatteringResidue sideL edgeL sideR edgeR Ap An Bp Bn shift time age)) := by
  have continuous : Continuous (fun pair : SpatialOperators × SpatialOperators=>
      (sourceActualScatteringRead sideL edgeL sideR edgeR pair.1,
        sourceActualScatteringRead sideL edgeL sideR edgeR pair.2)) := by
    simp only [sourceActualScatteringRead_source]
    exact (continuous_const.inner (continuous_fst.clm_apply continuous_const)).prodMk
      (continuous_const.inner (continuous_snd.clm_apply continuous_const))
  have returned:=continuous.tendsto (sourceActualScatteringKernelResidue Ap An Bp Bn shift time age) |>.comp
    (sourceActualScatteringKernel_residue Ap An Bp Bn shift time age)
  simpa only [Function.comp_def,sourceActualChargedScatteringPair,sourceActualChargedScatteringResidue,
    sourcePreparedScatteringPair,sourceActualScatteringKernel,sourceActualScatteringKernelResidue,
    sourceActualScatteringRead_source,Prod.smul_mk,smul_apply,inner_smul_right,smul_eq_mul] using returned

/-- The resulting residue has the original complete CAR expansion and the independent full mixed contact. -/
theorem sourceActualChargedScatteringResidue_fullCAR (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : CausalFieldLeg) (shift : Fin 3→ℝ) (time age : ℝ) :
    sourceActualChargedScatteringResidue sideL edgeL sideR edgeR Ap An Bp Bn shift time age=
      (Complex.I*((∑i : Fin 4,∑j : Fin 4,sourcePreparedOrderedCAR sideL edgeL sideR edgeR
        (shiftCoefficients (adjointCoefficients (complexFrequencyCoefficients (residueTransfer Bp Bn).negative)) shift)
        (realReaderCoefficients (residueTransfer Ap An) shift) (-shift) age time i j)-
        ∑i : Fin 4,∑j : Fin 4,sourcePreparedOrderedCAR sideL edgeL sideR edgeR
          (realReaderCoefficients (residueTransfer Ap An) shift)
          (complexFrequencyCoefficients (residueTransfer Bp Bn).positive) shift time age i j),
        inner ℂ (sourceActualScatteringInput sideL edgeL)
          (fieldMixedContact (residueTransfer Ap An) (residueTransfer Bp Bn) time
            (sourceActualScatteringInput sideR edgeR))) :=
  sourcePreparedScatteringPair_fullCAR sideL edgeL sideR edgeR (residueTransfer Ap An) (residueTransfer Bp Bn) shift time age

end LowEnergy.PreparationPhysicalJointGeneratorEnergyReturn
