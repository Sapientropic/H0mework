import H0mework.NavierStokes.FullOrder.RecoveryTimeCanonical
import H0mework.NavierStokes.FullOrder.RecoveryTimeGramWrite

set_option autoImplicit false
open scoped BigOperators Matrix Topology

namespace SaturationMonoid.NavierStokes.NativeRecoveryTimeCanonicalWrite

open Set Filter MeasureTheory
open PhysicsCore.DiracCliffordRepresentation
open PhysicsCore.StageNineFullDiracAdjointMaterial (diracAdjointSpinSwap)
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeRecoveryTimeGramAction NativeRecoveryTimeGramWrite NativeRecoveryTimeCanonical
open NativePhysicalFourier

noncomputable section

section Algebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def matterMatrix : Fin 4 → Fin 2 → Coordinate → ℂ :=
  !![![0, 0, 0], ![0, 0, 0]; ![0, 0, 0], ![0, 0, 0];
    ![0, 0, 1 / 4], ![1 / 4, -Complex.I / 4, 0];
    ![1 / 4, Complex.I / 4, 0], ![0, 0, -(1 / 4)]]

def matterCLM : (Coordinate → H) →L[ℂ] Spinor H :=
  ContinuousLinearMap.pi fun spin => ContinuousLinearMap.pi fun color =>
    ∑ coordinate : Coordinate, matterMatrix spin color coordinate • ContinuousLinearMap.proj coordinate

theorem matterCLM_apply (component : Coordinate → H) (spin : Fin 4) (color : Fin 2) :
    matterCLM component spin color = ∑ coordinate : Coordinate,
      matterMatrix spin color coordinate • component coordinate := by
  simp [matterCLM]

theorem matterCLM_eq (component : Coordinate → H) :
    matterCLM component = matterProgram (fun _ => 0) (fun _ => component) 0 := by
  funext spin color
  fin_cases spin <;> fin_cases color <;>
    simp [matterCLM_apply, matterMatrix, matterProgram, Fin.sum_univ_three,
      smul_add, smul_sub, smul_smul] <;> module

theorem matter_difference (background : IntegerWavevector → H)
    (first last : IntegerWavevector → Coordinate → H) (wave : IntegerWavevector) :
    matterProgram background last wave - matterProgram background first wave =
      matterCLM (fun coordinate => last wave coordinate - first wave coordinate) := by
  rw [matterCLM_eq]
  funext spin color
  change matterProgram background last wave spin color - matterProgram background first wave spin color = _
  fin_cases spin <;> fin_cases color <;> simp [matterProgram, smul_sub] <;> module

local instance : ContinuousSMul ℝ (Spinor H →L[ℂ] ℂ) := IsScalarTower.continuousSMul ℂ

def rieszRealCLM : H →L[ℝ] (H →L[ℂ] ℂ) where
  toFun := innerSL ℂ
  map_add' first second := by
    apply ContinuousLinearMap.ext
    intro candidate
    change inner ℂ (first + second) candidate = inner ℂ first candidate + inner ℂ second candidate
    exact inner_add_left _ _ _
  map_smul' scalar value := by
    apply ContinuousLinearMap.ext
    intro candidate
    change inner ℂ (scalar • value) candidate = scalar • inner ℂ value candidate
    exact (congrArg (fun value : H => inner ℂ value candidate)
      (IsScalarTower.algebraMap_smul ℂ scalar value).symm).trans (inner_smul_real_left value candidate scalar)
  cont := (innerSL ℂ).continuous

def coordinateCLM (spin : Fin 4) (color : Fin 2) : Spinor H →L[ℂ] H :=
  (ContinuousLinearMap.proj color : (Fin 2 → H) →L[ℂ] H).comp
    (ContinuousLinearMap.proj spin : Spinor H →L[ℂ] (Fin 2 → H))

def gammaRowCLM (matrix : DiracMatrix) (spin : Fin 4) (color : Fin 2) : Spinor H →L[ℝ] H :=
  ∑ other : Fin 4, matrix spin other •
    (ContinuousLinearMap.proj color : (Fin 2 → H) →L[ℝ] H).comp
      (ContinuousLinearMap.proj other : Spinor H →L[ℝ] (Fin 2 → H))

theorem gammaRowCLM_apply (matrix : DiracMatrix) (spin : Fin 4) (color : Fin 2) (value : Spinor H) :
    gammaRowCLM matrix spin color value = gamma matrix value spin color := by
  simp only [gammaRowCLM, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  rfl

def dualCLM : Spinor H →L[ℝ] (Spinor H →L[ℂ] ℂ) :=
  ∑ spin : Fin 4, ∑ color : Fin 2,
    ((((ContinuousLinearMap.compL ℂ (Spinor H) H ℂ).flip (coordinateCLM spin color)).restrictScalars ℝ).comp
      rieszRealCLM).comp (gammaRowCLM diracAdjointSpinSwap spin color)

theorem dualCLM_apply (value candidate : Spinor H) :
    dualCLM (H := H) value candidate = canonicalDual value candidate := by
  simp only [dualCLM, sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, gammaRowCLM_apply]
  rfl

theorem current_increment (firstWave firstZero stepWave stepZero : Spinor H) (direction : Fin 4) :
    dualCLM (H := H) (firstWave + stepWave) (gamma (diracGamma direction) (firstZero + stepZero)) -
      dualCLM (H := H) firstWave (gamma (diracGamma direction) firstZero) =
        dualCLM (H := H) stepWave (gamma (diracGamma direction) firstZero) +
          dualCLM (H := H) firstWave (gamma (diracGamma direction) stepZero) +
            dualCLM (H := H) stepWave (gamma (diracGamma direction) stepZero) := by
  simp only [map_add, add_apply]
  ring

end Algebra

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def primalAction (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) : Spinor (Space stress pointLe) :=
  matterCLM (NativeRecoveryTimeGramWrite.action stress pointLe first last wave)

def sourceDual (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) : Spinor (Space stress pointLe) →L[ℂ] ℂ :=
  dualCLM (H := Space stress pointLe) (matter stress pointLe node wave)

def dualAction (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) : Spinor (Space stress pointLe) →L[ℂ] ℂ :=
  dualCLM (H := Space stress pointLe) (primalAction stress pointLe first last wave)

theorem primalAction_eq (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) : primalAction stress pointLe first last wave =
      matter stress pointLe last wave - matter stress pointLe first wave := by
  exact (matter_difference (background stress pointLe) (component stress pointLe first)
    (component stress pointLe last) wave).symm

theorem source_primal_write (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) : matter stress pointLe first wave + primalAction stress pointLe first last wave =
      matter stress pointLe last wave := by rw [primalAction_eq]; abel

theorem source_dual_canonical (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) : (sourceDual stress pointLe node wave).toLinearMap =
      canonicalDual (matter stress pointLe node wave) := by
  apply LinearMap.ext
  intro candidate
  exact dualCLM_apply _ candidate

theorem source_dual_write (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) : sourceDual stress pointLe first wave + dualAction stress pointLe first last wave =
      sourceDual stress pointLe last wave := by
  change dualCLM (H := Space stress pointLe) _ + dualCLM (H := Space stress pointLe) _ = dualCLM (H := Space stress pointLe) _
  rw [← map_add, source_primal_write]

def rawPrimalRate (escape : SourceActionEscape receipt point) (index : ℕ) (wave : IntegerWavevector)
    (actual : ℝ) : Spinor ScalarSequence :=
  matterCLM (fun coordinate => rate escape index wave coordinate actual)

def rawPrimalWork (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (wave : IntegerWavevector) : Spinor ScalarSequence :=
  ∫ actual in (timeAt escape pointLe index first).1..(timeAt escape pointLe index last).1,
    rawPrimalRate escape index wave actual

theorem rawPrimalWork_eq (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (wave : IntegerWavevector) : rawPrimalWork escape pointLe index first last wave =
      matterCLM (rawWork escape pointLe index first last wave) := by
  have included : uIcc (timeAt escape pointLe index first).1 (timeAt escape pointLe index last).1 ⊆ Icc (0 : ℝ) 1 :=
    uIcc_subset_Icc (timeAt escape pointLe index first).2 (timeAt escape pointLe index last).2
  have paid : IntervalIntegrable (fun actual coordinate => rate escape index wave coordinate actual) volume
      (timeAt escape pointLe index first).1 (timeAt escape pointLe index last).1 :=
    ((continuousOn_pi.mpr (fun coordinate => rate_continuousOn escape index wave coordinate)).mono included).intervalIntegrable
  change (∫ actual in (timeAt escape pointLe index first).1..(timeAt escape pointLe index last).1,
    matterCLM (fun coordinate => rate escape index wave coordinate actual)) = _
  rw [ContinuousLinearMap.intervalIntegral_comp_comm _ paid]
  congr 1
  funext coordinate
  exact (ContinuousLinearMap.intervalIntegral_comp_comm
    (ContinuousLinearMap.proj coordinate : (Coordinate → ScalarSequence) →L[ℂ] ScalarSequence) paid).symm

def rawDualWork (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (wave : IntegerWavevector) : Spinor ScalarSequence →L[ℂ] ℂ :=
  ∫ actual in (timeAt escape pointLe index first).1..(timeAt escape pointLe index last).1,
    dualCLM (H := ScalarSequence) (rawPrimalRate escape index wave actual)

theorem rawDualWork_eq (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (wave : IntegerWavevector) : rawDualWork escape pointLe index first last wave =
      dualCLM (H := ScalarSequence) (rawPrimalWork escape pointLe index first last wave) := by
  have included : uIcc (timeAt escape pointLe index first).1 (timeAt escape pointLe index last).1 ⊆ Icc (0 : ℝ) 1 :=
    uIcc_subset_Icc (timeAt escape pointLe index first).2 (timeAt escape pointLe index last).2
  have paid : IntervalIntegrable (rawPrimalRate escape index wave) volume
      (timeAt escape pointLe index first).1 (timeAt escape pointLe index last).1 :=
    ((matterCLM.continuous.comp_continuousOn
      (continuousOn_pi.mpr (fun coordinate => rate_continuousOn escape index wave coordinate))).mono included).intervalIntegrable
  exact ContinuousLinearMap.intervalIntegral_comp_comm _ paid


def rawMatter (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (node : TimeNode) (wave : IntegerWavevector) : Spinor ScalarSequence :=
  matterProgram (fun frequency => NativeRecoveryTimeGramRaw.vector escape pointLe index (.inl frequency))
    (fun frequency coordinate => NativeRecoveryTimeGramRaw.vector escape pointLe index (.inr (node, frequency, coordinate))) wave

theorem raw_primal_write (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (wave : IntegerWavevector) :
    rawMatter escape pointLe index first wave + rawPrimalWork escape pointLe index first last wave =
      rawMatter escape pointLe index last wave := by
  have read : rawWork escape pointLe index first last wave = fun coordinate =>
      NativeRecoveryTimeGramRaw.vector escape pointLe index (.inr (last, wave, coordinate)) -
        NativeRecoveryTimeGramRaw.vector escape pointLe index (.inr (first, wave, coordinate)) := by
    funext coordinate
    exact rawWork_eq escape pointLe index first last wave coordinate
  have write := matter_difference
    (fun frequency => NativeRecoveryTimeGramRaw.vector escape pointLe index (.inl frequency))
    (fun frequency coordinate => NativeRecoveryTimeGramRaw.vector escape pointLe index (.inr (first, frequency, coordinate)))
    (fun frequency coordinate => NativeRecoveryTimeGramRaw.vector escape pointLe index (.inr (last, frequency, coordinate))) wave
  rw [rawPrimalWork_eq, read, ← write]
  change rawMatter escape pointLe index first wave +
    (rawMatter escape pointLe index last wave - rawMatter escape pointLe index first wave) = _
  abel

theorem raw_dual_write (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (wave : IntegerWavevector) :
    dualCLM (H := ScalarSequence) (rawMatter escape pointLe index first wave) +
      rawDualWork escape pointLe index first last wave =
        dualCLM (H := ScalarSequence) (rawMatter escape pointLe index last wave) := by
  rw [rawDualWork_eq, ← map_add, raw_primal_write]

theorem source_primal_work_test (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) (spin : Fin 4) (color : Fin 2) (test : Index →₀ ℂ) :
    Tendsto (fun index => inner ℂ (rawPrimalWork escape pointLe (stress.refinement index) first last wave spin color)
      (rawTest escape pointLe (stress.refinement index) test))
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (inner ℂ (primalAction stress pointLe first last wave spin color) (testVector stress pointLe test))) := by
  simpa only [rawPrimalWork_eq, primalAction, matterCLM_apply, sum_inner, inner_smul_left] using
    tendsto_finsetSum Finset.univ (fun coordinate _ =>
      (source_work_test stress pointLe first last wave coordinate test).const_mul
        (starRingEnd ℂ (matterMatrix spin color coordinate)))

theorem source_primal_work_inner (stress : StressAt escape) (pointLe : point ≤ 1)
    (first last start finish : TimeNode) (left right : IntegerWavevector)
    (spin other : Fin 4) (color otherColor : Fin 2) :
    Tendsto (fun index => inner ℂ
      (rawPrimalWork escape pointLe (stress.refinement index) first last left spin color)
      (rawPrimalWork escape pointLe (stress.refinement index) start finish right other otherColor))
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (inner ℂ (primalAction stress pointLe first last left spin color)
          (primalAction stress pointLe start finish right other otherColor))) := by
  simp only [rawPrimalWork_eq, primalAction, matterCLM_apply, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right]
  exact tendsto_finsetSum Finset.univ (fun partner _ =>
    (tendsto_finsetSum Finset.univ (fun coordinate _ =>
      (source_work_inner stress pointLe first last start finish (left, coordinate) (right, partner)).const_mul
        (starRingEnd ℂ (matterMatrix spin color coordinate)))).const_mul (matterMatrix other otherColor partner))

private theorem pi_norms_norm {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E] (value : ι → E) :
    ‖fun index => ‖value index‖‖ = ‖value‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun index => by
      simpa only [norm_norm] using norm_le_pi_norm value index
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun index => by
      simpa only [norm_norm] using norm_le_pi_norm (fun index => ‖value index‖) index

theorem source_primal_work_norm_sq (stress : StressAt escape) (pointLe : point ≤ 1)
    (first last : TimeNode) (wave : IntegerWavevector) :
    Tendsto (fun index => ‖rawPrimalWork escape pointLe (stress.refinement index) first last wave‖ ^ 2)
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (‖primalAction stress pointLe first last wave‖ ^ 2)) := by
  have rows (spin : Fin 4) (color : Fin 2) :
      Tendsto (fun index => ‖rawPrimalWork escape pointLe (stress.refinement index) first last wave spin color‖)
        ((generated stress pointLe).refinement : Filter ℕ)
          (𝓝 (‖primalAction stress pointLe first last wave spin color‖)) := by
    have squared : Tendsto (fun index =>
        ‖rawPrimalWork escape pointLe (stress.refinement index) first last wave spin color‖ ^ 2)
        ((generated stress pointLe).refinement : Filter ℕ)
          (𝓝 (‖primalAction stress pointLe first last wave spin color‖ ^ 2)) := by
      simp_rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
      exact (Complex.continuous_re.tendsto _).comp
        (source_primal_work_inner stress pointLe first last first last wave wave spin spin color color)
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm] using
      (Real.continuous_sqrt.tendsto _).comp squared
  have columns (spin : Fin 4) := (tendsto_pi_nhds.mpr (rows spin)).norm
  simp only [pi_norms_norm] at columns
  have all := (tendsto_pi_nhds.mpr columns).norm
  simpa only [pi_norms_norm] using all.pow 2

theorem primalAction_unique (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) (candidate : Spinor (Space stress pointLe))
    (actual : ∀ spin color (test : Index →₀ ℂ), Tendsto (fun index =>
      inner ℂ (rawPrimalWork escape pointLe (stress.refinement index) first last wave spin color)
        (rawTest escape pointLe (stress.refinement index) test))
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (inner ℂ (candidate spin color) (testVector stress pointLe test)))) :
    candidate = primalAction stress pointLe first last wave := by
  funext spin color
  apply ext_inner_right ℂ
  intro target
  refine UniformSpace.Completion.induction_on target ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  intro test
  have same := tendsto_nhds_unique (actual spin color (NativePositiveKernelCarrier.ofPreSpace _ test))
    (source_primal_work_test stress pointLe first last wave spin color (NativePositiveKernelCarrier.ofPreSpace _ test))
  simpa only [testVector_coe] using same

def rawSpinorTest (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (test : Fin 4 → Fin 2 → Index →₀ ℂ) : Spinor ScalarSequence :=
  fun spin color => rawTest escape pointLe index (test spin color)

def spinorTest (stress : StressAt escape) (pointLe : point ≤ 1)
    (test : Fin 4 → Fin 2 → Index →₀ ℂ) : Spinor (Space stress pointLe) :=
  fun spin color => testVector stress pointLe (test spin color)

theorem source_dual_work_test (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) (test : Fin 4 → Fin 2 → Index →₀ ℂ) :
    Tendsto (fun index => rawDualWork escape pointLe (stress.refinement index) first last wave
      (rawSpinorTest escape pointLe (stress.refinement index) test))
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (dualAction stress pointLe first last wave (spinorTest stress pointLe test))) := by
  simpa only [rawDualWork_eq, dualAction, dualCLM_apply, canonicalDual, gamma, LinearMap.coe_mk, AddHom.coe_mk,
    sum_inner, inner_smul_left, rawSpinorTest, spinorTest] using
    tendsto_finsetSum Finset.univ (fun spin _ => tendsto_finsetSum Finset.univ (fun color _ =>
      tendsto_finsetSum Finset.univ (fun other _ =>
        (source_primal_work_test stress pointLe first last wave other color (test spin color)).const_mul
          (starRingEnd ℂ (diracAdjointSpinSwap spin other)))))


theorem written_dual_canonical (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) :
    (sourceDual stress pointLe first wave + dualAction stress pointLe first last wave).toLinearMap =
      canonicalDual (matter stress pointLe first wave + primalAction stress pointLe first last wave) := by
  rw [source_dual_write, source_primal_write, source_dual_canonical]

def currentResponse (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  dualAction stress pointLe first last wave (gamma (diracGamma direction) (matter stress pointLe first 0)) +
    sourceDual stress pointLe first wave (gamma (diracGamma direction) (primalAction stress pointLe first last 0)) +
      dualAction stress pointLe first last wave (gamma (diracGamma direction) (primalAction stress pointLe first last 0))

theorem source_current_response (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (direction : Fin 4) (wave : IntegerWavevector) :
    currentResponse stress pointLe first last direction wave =
      current stress pointLe last direction wave - current stress pointLe first direction wave := by
  have read (node : TimeNode) : current stress pointLe node direction wave =
      dualCLM (H := Space stress pointLe) (matter stress pointLe node wave)
        (gamma (diracGamma direction) (matter stress pointLe node 0)) := (dualCLM_apply _ _).symm
  rw [read last, read first, ← source_primal_write stress pointLe first last wave,
    ← source_primal_write stress pointLe first last 0]
  exact (current_increment _ _ _ _ direction).symm

theorem raw_current_integral_response (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1)
    (index : ℕ) (first last : TimeNode) (direction : Fin 4) (wave : IntegerWavevector) :
    currentWork escape pointLe index first last direction wave =
      rawDualWork escape pointLe index first last wave
        (gamma (diracGamma direction) (rawMatter escape pointLe index first 0)) +
      dualCLM (H := ScalarSequence) (rawMatter escape pointLe index first wave)
        (gamma (diracGamma direction) (rawPrimalWork escape pointLe index first last 0)) +
      rawDualWork escape pointLe index first last wave
        (gamma (diracGamma direction) (rawPrimalWork escape pointLe index first last 0)) := by
  have read (node : TimeNode) : rawCurrent escape pointLe index node direction wave =
      dualCLM (H := ScalarSequence) (rawMatter escape pointLe index node wave)
        (gamma (diracGamma direction) (rawMatter escape pointLe index node 0)) := (dualCLM_apply _ _).symm
  rw [currentWork_eq, read last, read first, rawDualWork_eq,
    ← raw_primal_write escape pointLe index first last wave,
    ← raw_primal_write escape pointLe index first last 0]
  exact current_increment _ _ _ _ direction

theorem source_current_integral_response (stress : StressAt escape) (pointLe : point ≤ 1)
    (first last : TimeNode) (direction : Fin 4) (wave : IntegerWavevector) :
    Tendsto (fun index => currentWork escape pointLe (stress.refinement index) first last direction wave)
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (currentResponse stress pointLe first last direction wave)) := by
  rw [source_current_response]
  exact source_current_integral_write stress pointLe first last direction wave

theorem source_current_coefficient_write (stress : StressAt escape) (pointLe : point ≤ 1)
    (first last : TimeNode) (direction : Fin 4) (wave : IntegerWavevector) :
    NativePairedCurrentFourier.coefficient
      (receipt.wholePath (NativeRecoveryTimeGramReadout.physicalTime escape pointLe first))
      (NativeRecoveryTimeGramReadout.stressRead stress pointLe first) direction wave +
        currentResponse stress pointLe first last direction wave =
      NativePairedCurrentFourier.coefficient
        (receipt.wholePath (NativeRecoveryTimeGramReadout.physicalTime escape pointLe last))
        (NativeRecoveryTimeGramReadout.stressRead stress pointLe last) direction wave := by
  rw [source_current_response, ← current_eq, ← current_eq]
  abel

end
end SaturationMonoid.NavierStokes.NativeRecoveryTimeCanonicalWrite
