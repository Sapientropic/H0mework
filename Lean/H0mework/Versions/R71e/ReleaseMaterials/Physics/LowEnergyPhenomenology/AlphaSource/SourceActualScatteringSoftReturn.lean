import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualContactScatteringFourier

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedScatteringFourierReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Stage10 Stage9DEF.Compatibility
open YangMills.FullPairing FullQuantum FullSpace FullQuantum.PerturbedGreen FullQuantum.Triangular
open PreparationPhysicalJointGeneratorEnergyReturn PreparationPhysicalChargedScatteringPoleReturn
open PreparationPhysicalChargedPacketQuantumReturn PreparationVacuumElectromagneticIdentity
open GaussComposite.PhysicalFullFieldScattering Electromagnetic.CanonicalCoframe MeasureTheory Filter
open scoped InnerProductSpace BigOperators Matrix Topology
attribute [local irreducible] complexCoefficients complexFrequencyCoefficients complexMixedCoefficients
  realReaderCoefficients realMixedCoefficients sourcePreparedScatteringPair sourcePreparedOrderedCAR
local instance softFiberRationalAlgebra : NormedAlgebra ℚ FiberOperators := NormedAlgebra.restrictScalars ℚ ℂ _
local instance softFiberRealAlgebra : NormedAlgebra ℝ FiberOperators := NormedAlgebra.restrictScalars ℝ ℂ _

private theorem shifted_coefficient_continuous (A : ℝ→Fin 4→FiberOperators) (continuousA : Continuous A)
    (shift : Fin 3→ℝ) (i : Fin 4) : Continuous (fun d=>shiftCoefficients (A d) (d • shift) i) := by
  induction i using Fin.cases with
  | zero =>
    simp only [shiftCoefficients,Fin.cases_zero]
    exact ((continuous_apply 0).comp continuousA).add
      (continuous_finsetSum _ fun j _=>
        (Complex.continuous_ofReal.comp ((continuous_apply j).comp (continuous_id.smul continuous_const))).smul
          ((continuous_apply j.succ).comp continuousA))
  | succ j =>
    simp only [shiftCoefficients,Fin.cases_succ]
    exact (continuous_apply j.succ).comp continuousA

private theorem evolution_momentum_continuous (time : ℝ) :
    Continuous (fun p : Fin 3→ℝ=>evolution actual 0 p time) :=
  NormedSpace.exp_continuous.comp ((continuous_const (y:=time)).smul (original_drift_continuous 0))

private def evolutionBound (time : ℝ) : ℝ:=1+|time| * sourceRate 0
private theorem evolutionBound_nonnegative (time : ℝ) : 0≤evolutionBound time := by
  unfold evolutionBound sourceRate
  positivity
private theorem evolution_bound (p : Fin 3→ℝ) (time : ℝ) :
    ‖evolution actual 0 p time‖≤evolutionBound time :=
  complete_evolution_bound actual 0 p (original_freeHamiltonian_selfAdjoint 0 p) time

private theorem ordered_fiber_bound (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ)
    (i j : Fin 4) (p : Fin 3→ℝ) :
    ‖sourceOrderedFiber A B shift time age i j p‖≤
      evolutionBound (-time)*‖shiftCoefficients A shift i‖*evolutionBound (time-age)*‖B j‖*evolutionBound age := by
  unfold sourceOrderedFiber
  calc
    _≤‖evolution actual 0 p (-time)*shiftCoefficients A shift i*
      evolution actual 0 (fun axis=>p axis+shift axis) (time-age)*B j‖*‖evolution actual 0 p age‖ := norm_mul_le _ _
    _≤(‖evolution actual 0 p (-time)*shiftCoefficients A shift i*
      evolution actual 0 (fun axis=>p axis+shift axis) (time-age)‖*‖B j‖)*‖evolution actual 0 p age‖ := by
      gcongr; exact norm_mul_le _ _
    _≤((‖evolution actual 0 p (-time)*shiftCoefficients A shift i‖*
      ‖evolution actual 0 (fun axis=>p axis+shift axis) (time-age)‖)*‖B j‖)*‖evolution actual 0 p age‖ := by
      gcongr; exact norm_mul_le _ _
    _≤(((‖evolution actual 0 p (-time)‖*‖shiftCoefficients A shift i‖)*
      ‖evolution actual 0 (fun axis=>p axis+shift axis) (time-age)‖)*‖B j‖)*‖evolution actual 0 p age‖ := by
      gcongr; exact norm_mul_le _ _
    _≤_ := by
      have h1:=evolutionBound_nonnegative (-time)
      have h2:=evolutionBound_nonnegative (time-age)
      have h3:=evolutionBound_nonnegative age
      gcongr
      all_goals first | positivity | exact evolution_bound _ _

/-- Dominated convergence uses the actual two L2 legs and the source's full evolution bound. -/
private theorem ordered_integral_soft (u v : FullMatterL2)
    (A B : ℝ→Fin 4→FiberOperators) (continuousA : Continuous A) (continuousB : Continuous B)
    (shift : Fin 3→ℝ) (time age : ℝ) (i j : Fin 4) :
    Tendsto (fun d : ℝ=>∫k,inner ℂ (u k)
      (sourceOrderedFiber (A d) (B d) (d • shift) time age i j (physicalMomentum k) (v k))) (𝓝 0)
      (𝓝 (∫k,inner ℂ (u k) (sourceOrderedFiber (A 0) (B 0) 0 time age i j (physicalMomentum k) (v k)))) := by
  let M:=evolutionBound (-time)*(‖shiftCoefficients (A 0) 0 i‖+1)*
    evolutionBound (time-age)*(‖B 0 j‖+1)*evolutionBound age
  have nonnegative : 0≤M := by
    dsimp [M]
    have h1:=evolutionBound_nonnegative (-time)
    have h2:=evolutionBound_nonnegative (time-age)
    have h3:=evolutionBound_nonnegative age
    positivity
  have matrixContinuous (d : ℝ) : Continuous (fun k=>sourceOrderedFiber (A d) (B d) (d • shift) time age i j (physicalMomentum k)) := by
    unfold sourceOrderedFiber
    exact (((((evolution_momentum_continuous (-time)).comp physicalMomentum_continuous).mul continuous_const).mul
      ((evolution_momentum_continuous (time-age)).comp (physicalMomentum_continuous.add continuous_const))).mul
        continuous_const).mul ((evolution_momentum_continuous age).comp physicalMomentum_continuous)
  have measurable (d : ℝ) : AEStronglyMeasurable (fun k=>inner ℂ (u k)
      (sourceOrderedFiber (A d) (B d) (d • shift) time age i j (physicalMomentum k) (v k))) volume :=
    (Lp.aestronglyMeasurable u).inner (multiplier_measurable _ (matrixContinuous d) v)
  have boundIntegrable : Integrable (fun k=>M*(‖u k‖^2+‖v k‖^2)) volume :=
    (((memLp_two_iff_integrable_sq_norm (Lp.memLp u).aestronglyMeasurable).mp (Lp.memLp u)).add
      ((memLp_two_iff_integrable_sq_norm (Lp.memLp v).aestronglyMeasurable).mp (Lp.memLp v))).const_mul M
  have nearA : ∀ᶠ d : ℝ in 𝓝 0,‖shiftCoefficients (A d) (d • shift) i‖≤‖shiftCoefficients (A 0) 0 i‖+1 := by
    have converges : Tendsto (fun d : ℝ=>‖shiftCoefficients (A d) (d • shift) i‖) (𝓝 0)
        (𝓝 ‖shiftCoefficients (A 0) 0 i‖) := by
      simpa only [zero_smul] using (shifted_coefficient_continuous A continuousA shift i).norm.tendsto 0
    exact (converges.eventually (eventually_lt_nhds (lt_add_one ‖shiftCoefficients (A 0) 0 i‖))).mono fun _ h=>h.le
  have nearB : ∀ᶠ d : ℝ in 𝓝 0,‖B d j‖≤‖B 0 j‖+1 :=
    ((((continuous_apply j).comp continuousB).norm.tendsto 0).eventually
      (eventually_lt_nhds (lt_add_one ‖B 0 j‖))).mono fun _ h=>h.le
  have dominated : ∀ᶠ d : ℝ in 𝓝 0,∀ᵐ k ∂volume,
      ‖inner ℂ (u k) (sourceOrderedFiber (A d) (B d) (d • shift) time age i j (physicalMomentum k) (v k))‖≤
        M*(‖u k‖^2+‖v k‖^2) := by
    filter_upwards [nearA,nearB] with d a b
    apply ae_of_all
    intro k
    have op : ‖sourceOrderedFiber (A d) (B d) (d • shift) time age i j (physicalMomentum k)‖≤M :=
      (ordered_fiber_bound _ _ _ _ _ _ _ _).trans (by
        have h1:=evolutionBound_nonnegative (-time)
        have h2:=evolutionBound_nonnegative (time-age)
        have h3:=evolutionBound_nonnegative age
        dsimp [M]
        gcongr)
    calc
      _≤‖u k‖*(‖sourceOrderedFiber (A d) (B d) (d • shift) time age i j (physicalMomentum k)‖*‖v k‖) :=
        (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
          ((sourceOrderedFiber (A d) (B d) (d • shift) time age i j (physicalMomentum k)).le_opNorm _) (norm_nonneg _))
      _≤‖u k‖*(M*‖v k‖) := by gcongr
      _=M*(‖u k‖*‖v k‖) := by ring
      _≤_ := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (‖u k‖-‖v k‖),sq_nonneg ‖u k‖,sq_nonneg ‖v k‖]) nonnegative
  have pointwise (k : Position) : Tendsto (fun d : ℝ=>inner ℂ (u k)
      (sourceOrderedFiber (A d) (B d) (d • shift) time age i j (physicalMomentum k) (v k))) (𝓝 0)
      (𝓝 (inner ℂ (u k) (sourceOrderedFiber (A 0) (B 0) 0 time age i j (physicalMomentum k) (v k)))) := by
    have matrix : Continuous (fun d : ℝ=>sourceOrderedFiber (A d) (B d) (d • shift) time age i j (physicalMomentum k)) := by
      unfold sourceOrderedFiber
      exact ((((continuous_const.mul (shifted_coefficient_continuous A continuousA shift i)).mul
        ((evolution_momentum_continuous (time-age)).comp (continuous_const.add (continuous_id.smul continuous_const)))).mul
          ((continuous_apply j).comp continuousB)).mul continuous_const)
    simpa only [zero_smul] using (continuous_const.inner (matrix.clm_apply continuous_const)).tendsto 0
  exact tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall measurable) dominated boundIntegrable
    (ae_of_all _ pointwise)

private theorem orderedCAR_soft (sideL edgeL sideR edgeR : Fin 2)
    (A B : ℝ→Fin 4→FiberOperators) (continuousA : Continuous A) (continuousB : Continuous B)
    (shift : Fin 3→ℝ) (time age : ℝ) (i j : Fin 4) :
    Tendsto (fun d : ℝ=>sourcePreparedOrderedCAR sideL edgeL sideR edgeR (A d) (B d) (d • shift) time age i j)
      (𝓝 0) (𝓝 (sourcePreparedOrderedCAR sideL edgeL sideR edgeR (A 0) (B 0) 0 time age i j)) := by
  have original (d : ℝ) : sourcePreparedOrderedCAR sideL edgeL sideR edgeR (A d) (B d) (d • shift) time age i j=
      ∫k,inner ℂ (fourier (coordinateLeg i (sourceActualScatteringInput sideL edgeL)) k)
        (sourceOrderedFiber (A d) (B d) (d • shift) time age i j (physicalMomentum k)
          (fourier (coordinateLeg j (sourceActualScatteringInput sideR edgeR)) k)) := by
    rw [sourcePreparedOrderedCAR_source]
    change inner ℂ (sourceActualScatteringInput sideL edgeL)
      ((coordinateLeg i).adjoint (sourceOrderedInterior (A d) (B d) (d • shift) time age i j
        (coordinateLeg j (sourceActualScatteringInput sideR edgeR))))=_
    rw [ContinuousLinearMap.adjoint_inner_right,←fourier.inner_map_map,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [sourceOrderedInterior_fourier (A d) (B d) (d • shift) time age i j
      (coordinateLeg j (sourceActualScatteringInput sideR edgeR))] with k read
    rw [read]
  have generated:=ordered_integral_soft (fourier (coordinateLeg i (sourceActualScatteringInput sideL edgeL)))
    (fourier (coordinateLeg j (sourceActualScatteringInput sideR edgeR))) A B continuousA continuousB shift time age i j
  have target:=original 0
  simp only [zero_smul] at target
  rw [←target] at generated
  exact generated.congr' (Eventually.of_forall fun d=>(original d).symm)

private theorem reader_ray_continuous (A : TransferPair) (shift : Fin 3→ℝ) :
    Continuous (fun d : ℝ=>realReaderCoefficients A (d • shift)) := by
  apply continuous_pi
  intro i
  have changed:=shifted_coefficient_continuous (fun _ : ℝ=>complexCoefficients A.positive) continuous_const (-shift) i
  have equal : (fun d : ℝ=>realReaderCoefficients A (d • shift) i)=
      (2:ℂ)⁻¹ • (fun d : ℝ=>complexCoefficients A.negative i+
        (shiftCoefficients (complexCoefficients A.positive) (d • (-shift)) i).adjoint) := by
    funext d
    simp only [realReaderCoefficients,adjointCoefficients,smul_neg,Pi.smul_apply]
  rw [equal]
  exact (continuous_const.add (ContinuousLinearMap.adjoint.continuous.comp changed)).const_smul ((2:ℂ)⁻¹)

/-- The physical transfer tends to zero in the original fixed-packet scattering pair; causal scale and age stay fixed. -/
theorem sourcePreparedScatteringPair_soft (sideL edgeL sideR edgeR : Fin 2)
    (A B : TransferPair) (shift : Fin 3→ℝ) (time age : ℝ) :
    Tendsto (fun d : ℝ=>sourcePreparedScatteringPair sideL edgeL sideR edgeR A B (d • shift) time age)
      (𝓝 0) (𝓝 (sourcePreparedScatteringPair sideL edgeL sideR edgeR A B 0 time age)) := by
  let reader:=fun d : ℝ=>realReaderCoefficients A (d • shift)
  let backward:=fun d : ℝ=>shiftCoefficients (adjointCoefficients (complexFrequencyCoefficients B.negative)) (d • shift)
  have readerContinuous : Continuous reader:=reader_ray_continuous A shift
  have backwardContinuous : Continuous backward:=continuous_pi fun i=>
    shifted_coefficient_continuous (fun _ : ℝ=>adjointCoefficients (complexFrequencyCoefficients B.negative)) continuous_const shift i
  have first:=tendsto_finsetSum Finset.univ fun i _=>tendsto_finsetSum Finset.univ fun j _=>
    orderedCAR_soft sideL edgeL sideR edgeR backward reader backwardContinuous readerContinuous (-shift) age time i j
  have second:=tendsto_finsetSum Finset.univ fun i _=>tendsto_finsetSum Finset.univ fun j _=>
    orderedCAR_soft sideL edgeL sideR edgeR reader (fun _=>complexFrequencyCoefficients B.positive)
      readerContinuous continuous_const shift time age i j
  have paired:=((tendsto_const_nhds (x:=Complex.I)).mul (first.sub second)).prodMk_nhds
    (tendsto_const_nhds (x:=inner ℂ (sourceActualScatteringInput sideL edgeL)
      (fieldMixedContact A B time (sourceActualScatteringInput sideR edgeR))))
  simpa only [sourcePreparedScatteringPair_fullCAR,reader,backward,zero_smul,smul_neg,neg_zero] using paired

/-- The original generated causal fields enter the same physical soft read, with no new external preparation. -/
theorem sourceActualChargedScattering_soft (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : CausalFieldLeg) (shift : Fin 3→ℝ) (time age causalScale : ℝ) :
    Tendsto (fun d : ℝ=>sourceActualChargedScatteringPair sideL edgeL sideR edgeR Ap An Bp Bn (d • shift) time age causalScale)
      (𝓝 0) (𝓝 (sourceActualChargedScatteringPair sideL edgeL sideR edgeR Ap An Bp Bn 0 time age causalScale)) :=
  sourcePreparedScatteringPair_soft sideL edgeL sideR edgeR (causalTransfer Ap An causalScale)
    (causalTransfer Bp Bn causalScale) shift time age

/-- The complete causal residue has its own physical zero-transfer read; the two limits are not interchanged. -/
theorem sourceActualChargedScatteringResidue_soft (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : CausalFieldLeg) (shift : Fin 3→ℝ) (time age : ℝ) :
    Tendsto (fun d : ℝ=>sourceActualChargedScatteringResidue sideL edgeL sideR edgeR Ap An Bp Bn (d • shift) time age)
      (𝓝 0) (𝓝 (sourceActualChargedScatteringResidue sideL edgeL sideR edgeR Ap An Bp Bn 0 time age)) :=
  sourcePreparedScatteringPair_soft sideL edgeL sideR edgeR (residueTransfer Ap An) (residueTransfer Bp Bn) shift time age

end LowEnergy.PreparationPhysicalChargedScatteringFourierReturn
