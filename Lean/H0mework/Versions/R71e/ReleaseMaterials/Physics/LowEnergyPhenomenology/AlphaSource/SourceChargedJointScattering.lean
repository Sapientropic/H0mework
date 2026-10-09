import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativePhotonTensorPrice

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
local instance chargedSoftJointQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

local instance jointFiberComplete : CompleteSpace FiberOperators := ContinuousLinearMap.instCompleteSpace
local instance jointFiberRationalAlgebra : NormedAlgebra ℚ FiberOperators := NormedAlgebra.restrictScalars ℚ ℂ _
local instance jointFiberRealAlgebra : NormedAlgebra ℝ FiberOperators := NormedAlgebra.restrictScalars ℝ ℂ _

abbrev SourceOrderedParameters := (Fin 4→FiberOperators) × (Fin 4→FiberOperators) × PhysicalMomentum

private theorem shifted_row_joint (i : Fin 4) :
    Continuous (fun x : (Fin 4→FiberOperators) × PhysicalMomentum=>shiftCoefficients x.1 x.2 i) := by
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

private theorem evolution_momentum_joint (time : ℝ) :
    Continuous (fun p : PhysicalMomentum=>evolution actual 0 p time) :=
  NormedSpace.exp_continuous.comp ((continuous_const (y:=time)).smul (original_drift_continuous 0))

private theorem evolution_bound (p : PhysicalMomentum) (time : ℝ) :
    ‖evolution actual 0 p time‖ ≤ sourceScatteringGrowth time :=
  complete_evolution_bound actual 0 p (original_freeHamiltonian_selfAdjoint 0 p) time

private theorem ordered_fiber_bound (A B : Fin 4→FiberOperators) (shift : PhysicalMomentum)
    (time age : ℝ) (i j : Fin 4) (p : PhysicalMomentum) :
    ‖sourceOrderedFiber A B shift time age i j p‖ ≤ sourceOrderedInteriorPrice A B shift time age i j := by
  have first : ‖evolution actual 0 p (-time)‖ ≤ sourceScatteringGrowth time := by
    simpa only [sourceScatteringGrowth,abs_neg] using evolution_bound p (-time)
  have step1:=norm_mul_le_of_le first (le_refl ‖shiftCoefficients A shift i‖)
  have step2:=norm_mul_le_of_le step1 (evolution_bound (fun axis=>p axis+shift axis) (time-age))
  have step3:=norm_mul_le_of_le step2 (le_refl ‖B j‖)
  exact norm_mul_le_of_le step3 (evolution_bound p age)

/-- The actual full252 ordered multiplier varies jointly in both vertices and the physical momentum transfer. -/
theorem sourceOrderedIntegral_joint_continuous (u v : FullMatterL2) (time age : ℝ) (i j : Fin 4) :
    Continuous (fun x : SourceOrderedParameters=>∫k : Position,inner ℂ (u k)
      (sourceOrderedFiber x.1 x.2.1 x.2.2 time age i j (physicalMomentum k) (v k))) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  let M:=sourceScatteringGrowth time*(‖shiftCoefficients x₀.1 x₀.2.2 i‖+1)*
    sourceScatteringGrowth (time-age)*(‖x₀.2.1 j‖+1)*sourceScatteringGrowth age
  have nonnegative : 0 ≤ M := by
    dsimp [M,sourceScatteringGrowth,sourceRate]
    positivity
  have matrixContinuous (x : SourceOrderedParameters) :
      Continuous (fun k=>sourceOrderedFiber x.1 x.2.1 x.2.2 time age i j (physicalMomentum k)) := by
    unfold sourceOrderedFiber
    exact (((((evolution_momentum_joint (-time)).comp physicalMomentum_continuous).mul continuous_const).mul
      ((evolution_momentum_joint (time-age)).comp (physicalMomentum_continuous.add continuous_const))).mul
        continuous_const).mul ((evolution_momentum_joint age).comp physicalMomentum_continuous)
  have measurable (x : SourceOrderedParameters) : AEStronglyMeasurable (fun k=>inner ℂ (u k)
      (sourceOrderedFiber x.1 x.2.1 x.2.2 time age i j (physicalMomentum k) (v k))) volume :=
    (Lp.aestronglyMeasurable u).inner (multiplier_measurable _ (matrixContinuous x) v)
  have boundIntegrable : Integrable (fun k=>M*(‖u k‖^2+‖v k‖^2)) volume :=
    (((memLp_two_iff_integrable_sq_norm (Lp.memLp u).aestronglyMeasurable).mp (Lp.memLp u)).add
      ((memLp_two_iff_integrable_sq_norm (Lp.memLp v).aestronglyMeasurable).mp (Lp.memLp v))).const_mul M
  have rowContinuous : Continuous (fun x : SourceOrderedParameters=>shiftCoefficients x.1 x.2.2 i) :=
    (shifted_row_joint i).comp (continuous_fst.prodMk continuous_snd.snd)
  have nearA : ∀ᶠ x : SourceOrderedParameters in 𝓝 x₀,
      ‖shiftCoefficients x.1 x.2.2 i‖ ≤ ‖shiftCoefficients x₀.1 x₀.2.2 i‖+1 :=
    ((rowContinuous.norm.tendsto x₀).eventually
      (eventually_lt_nhds (lt_add_one ‖shiftCoefficients x₀.1 x₀.2.2 i‖))).mono fun _ h=>h.le
  have nearB : ∀ᶠ x : SourceOrderedParameters in 𝓝 x₀,‖x.2.1 j‖ ≤ ‖x₀.2.1 j‖+1 :=
    ((((continuous_apply j).comp continuous_snd.fst).norm.tendsto x₀).eventually
      (eventually_lt_nhds (lt_add_one ‖x₀.2.1 j‖))).mono fun _ h=>h.le
  have dominated : ∀ᶠ x : SourceOrderedParameters in 𝓝 x₀,∀ᵐ k ∂volume,
      ‖inner ℂ (u k) (sourceOrderedFiber x.1 x.2.1 x.2.2 time age i j (physicalMomentum k) (v k))‖ ≤
        M*(‖u k‖^2+‖v k‖^2) := by
    filter_upwards [nearA,nearB] with x a b
    apply ae_of_all
    intro k
    have op : ‖sourceOrderedFiber x.1 x.2.1 x.2.2 time age i j (physicalMomentum k)‖ ≤ M :=
      (ordered_fiber_bound _ _ _ _ _ _ _ _).trans (by
        have h1 : 0 ≤ sourceScatteringGrowth time := by unfold sourceScatteringGrowth sourceRate; positivity
        have h2 : 0 ≤ sourceScatteringGrowth (time-age) := by unfold sourceScatteringGrowth sourceRate; positivity
        have h3 : 0 ≤ sourceScatteringGrowth age := by unfold sourceScatteringGrowth sourceRate; positivity
        dsimp [M,sourceOrderedInteriorPrice]
        gcongr)
    calc
      _ ≤ ‖u k‖*(‖sourceOrderedFiber x.1 x.2.1 x.2.2 time age i j (physicalMomentum k)‖*‖v k‖) :=
        (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
          ((sourceOrderedFiber x.1 x.2.1 x.2.2 time age i j (physicalMomentum k)).le_opNorm _) (norm_nonneg _))
      _ ≤ ‖u k‖*(M*‖v k‖) := by gcongr
      _ = M*(‖u k‖*‖v k‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by nlinarith [sq_nonneg (‖u k‖-‖v k‖),sq_nonneg ‖u k‖,sq_nonneg ‖v k‖]) nonnegative
  have pointwise (k : Position) : Tendsto (fun x : SourceOrderedParameters=>inner ℂ (u k)
      (sourceOrderedFiber x.1 x.2.1 x.2.2 time age i j (physicalMomentum k) (v k))) (𝓝 x₀)
      (𝓝 (inner ℂ (u k) (sourceOrderedFiber x₀.1 x₀.2.1 x₀.2.2 time age i j (physicalMomentum k) (v k)))) := by
    have matrix : Continuous (fun x : SourceOrderedParameters=>
        sourceOrderedFiber x.1 x.2.1 x.2.2 time age i j (physicalMomentum k)) := by
      unfold sourceOrderedFiber
      exact ((((continuous_const.mul rowContinuous).mul
        ((evolution_momentum_joint (time-age)).comp (continuous_const.add continuous_snd.snd))).mul
          ((continuous_apply j).comp continuous_snd.fst)).mul continuous_const)
    exact (continuous_const.inner (matrix.clm_apply continuous_const)).tendsto x₀
  exact tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall measurable) dominated boundIntegrable
    (ae_of_all _ pointwise)

/-- Joint continuity is consumed by the same four-CAR word on the two original charged preparations. -/
theorem sourcePreparedOrderedCAR_joint_continuous (sideL edgeL sideR edgeR : Fin 2)
    (time age : ℝ) (i j : Fin 4) :
    Continuous (fun x : SourceOrderedParameters=>
      sourcePreparedOrderedCAR sideL edgeL sideR edgeR x.1 x.2.1 x.2.2 time age i j) := by
  have original (x : SourceOrderedParameters) :
      sourcePreparedOrderedCAR sideL edgeL sideR edgeR x.1 x.2.1 x.2.2 time age i j=
        ∫k : Position,inner ℂ (fourier (coordinateLeg i (sourceActualScatteringInput sideL edgeL)) k)
          (sourceOrderedFiber x.1 x.2.1 x.2.2 time age i j (physicalMomentum k)
            (fourier (coordinateLeg j (sourceActualScatteringInput sideR edgeR)) k)) := by
    rw [sourcePreparedOrderedCAR_source]
    change inner ℂ (sourceActualScatteringInput sideL edgeL)
      ((coordinateLeg i).adjoint (sourceOrderedInterior x.1 x.2.1 x.2.2 time age i j
        (coordinateLeg j (sourceActualScatteringInput sideR edgeR))))=_
    rw [ContinuousLinearMap.adjoint_inner_right,←fourier.inner_map_map,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [sourceOrderedInterior_fourier x.1 x.2.1 x.2.2 time age i j
      (coordinateLeg j (sourceActualScatteringInput sideR edgeR))] with k read
    rw [read]
  simp_rw [original]
  exact sourceOrderedIntegral_joint_continuous _ _ time age i j

end LowEnergy.PreparationPhysicalChargedSoftScatteringReturn
