import H0mework.NavierStokes.TimeGramAction.RecoveryTimeGramAction

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeRecoveryTimeGramWrite

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeRecoveryTimeGramAction NativeEndpointVelocityCarrier NativePhysicalFourier

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def rawWork (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (wave : IntegerWavevector) (coordinate : Coordinate) : ScalarSequence :=
  ∫ actual in (timeAt escape pointLe index first).1..(timeAt escape pointLe index last).1,
    rate escape index wave coordinate actual

theorem rawWork_eq (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (first last : TimeNode) (wave : IntegerWavevector) (coordinate : Coordinate) :
    rawWork escape pointLe index first last wave coordinate =
      NativeRecoveryTimeGramRaw.vector escape pointLe index (.inr (last, wave, coordinate)) -
        NativeRecoveryTimeGramRaw.vector escape pointLe index (.inr (first, wave, coordinate)) := by
  have included : uIcc (timeAt escape pointLe index first).1 (timeAt escape pointLe index last).1 ⊆ Icc (0 : ℝ) 1 :=
    uIcc_subset_Icc (timeAt escape pointLe index first).2 (timeAt escape pointLe index last).2
  have paid : IntervalIntegrable (rate escape index wave coordinate) volume
      (timeAt escape pointLe index first).1 (timeAt escape pointLe index last).1 :=
    ((rate_continuousOn escape index wave coordinate).mono included).intervalIntegrable
  have write := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun actual inside => field_hasDerivAt escape index wave coordinate actual (included inside)) paid
  rw [field_read, field_read] at write
  exact write

def action (stress : StressAt escape) (pointLe : point ≤ 1)
    (first last : TimeNode) (wave : IntegerWavevector) (coordinate : Coordinate) : Space stress pointLe :=
  NativeRecoveryJointTimeKernel.vector stress pointLe (.inr (last, wave, coordinate)) -
    NativeRecoveryJointTimeKernel.vector stress pointLe (.inr (first, wave, coordinate))

theorem source_work_pairing (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) (coordinate : Coordinate) (right : Index) :
    Tendsto (fun index => inner ℂ (rawWork escape pointLe (stress.refinement index) first last wave coordinate)
      (NativeRecoveryTimeGramRaw.vector escape pointLe (stress.refinement index) right))
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (inner ℂ (action stress pointLe first last wave coordinate)
          (NativeRecoveryJointTimeKernel.vector stress pointLe right))) := by
  simpa only [rawWork_eq, action, inner_sub_left, gram, Matrix.gram_apply] using
    (pairing_tendsto stress pointLe (.inr (last, wave, coordinate)) right).sub
      (pairing_tendsto stress pointLe (.inr (first, wave, coordinate)) right)

theorem source_work_inner (stress : StressAt escape) (pointLe : point ≤ 1)
    (first last start finish : TimeNode) (left right : IntegerWavevector × Coordinate) :
    Tendsto (fun index => inner ℂ
      (rawWork escape pointLe (stress.refinement index) first last left.1 left.2)
      (rawWork escape pointLe (stress.refinement index) start finish right.1 right.2))
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (inner ℂ (action stress pointLe first last left.1 left.2)
          (action stress pointLe start finish right.1 right.2))) := by
  simpa only [rawWork_eq, action, inner_sub_right, inner_sub_left] using
    (source_work_pairing stress pointLe first last left.1 left.2 (.inr (finish, right))).sub
      (source_work_pairing stress pointLe first last left.1 left.2 (.inr (start, right)))

theorem source_work_norm_sq (stress : StressAt escape) (pointLe : point ≤ 1)
    (first last : TimeNode) (wave : IntegerWavevector) (coordinate : Coordinate) :
    Tendsto (fun index => ‖rawWork escape pointLe (stress.refinement index) first last wave coordinate‖ ^ 2)
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (‖action stress pointLe first last wave coordinate‖ ^ 2)) := by
  simp_rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact (Complex.continuous_re.tendsto _).comp
    (source_work_inner stress pointLe first last first last (wave, coordinate) (wave, coordinate))

def rawTest (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (test : Index →₀ ℂ) : ScalarSequence :=
  test.sum fun entry scalar => scalar • NativeRecoveryTimeGramRaw.vector escape pointLe index entry

def testVector (stress : StressAt escape) (pointLe : point ≤ 1) (test : Index →₀ ℂ) : Space stress pointLe :=
  test.sum fun entry scalar => scalar • NativeRecoveryJointTimeKernel.vector stress pointLe entry

theorem source_work_test (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) (coordinate : Coordinate) (test : Index →₀ ℂ) :
    Tendsto (fun index => inner ℂ (rawWork escape pointLe (stress.refinement index) first last wave coordinate)
      (rawTest escape pointLe (stress.refinement index) test))
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (inner ℂ (action stress pointLe first last wave coordinate) (testVector stress pointLe test))) := by
  simpa only [rawTest, testVector, Finsupp.sum, inner_sum, inner_smul_right] using
    tendsto_finsetSum test.support (fun entry _ =>
      (source_work_pairing stress pointLe first last wave coordinate entry).const_mul (test entry))

theorem testVector_coe (stress : StressAt escape) (pointLe : point ≤ 1)
    (test : NativePositiveKernelCarrier.PreSpace (generated stress pointLe).kernel) :
    testVector stress pointLe (NativePositiveKernelCarrier.ofPreSpace _ test) =
      (test : Space stress pointLe) := by
  classical
  let embed : NativePositiveKernelCarrier.PreSpace (generated stress pointLe).kernel →ₗᵢ[ℂ] Space stress pointLe :=
    UniformSpace.Completion.toComplₗᵢ
  change (NativePositiveKernelCarrier.ofPreSpace _ test).sum
    (fun entry scalar => scalar • (NativePositiveKernelCarrier.vector _ entry)) = _
  change (NativePositiveKernelCarrier.ofPreSpace _ test).sum
    (fun entry scalar => scalar • embed ((NativePositiveKernelCarrier.ofPreSpace _).symm (Finsupp.single entry 1))) = embed test
  rw [Finsupp.sum]
  simp only [← map_smul, ← map_sum]
  congr 1
  apply (NativePositiveKernelCarrier.ofPreSpace _).injective
  simp only [map_sum, LinearEquiv.apply_symm_apply, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact Finsupp.sum_single (NativePositiveKernelCarrier.ofPreSpace _ test)

theorem action_unique (stress : StressAt escape) (pointLe : point ≤ 1) (first last : TimeNode)
    (wave : IntegerWavevector) (coordinate : Coordinate) (candidate : Space stress pointLe)
    (actual : ∀ test : Index →₀ ℂ, Tendsto (fun index =>
      inner ℂ (rawWork escape pointLe (stress.refinement index) first last wave coordinate)
        (rawTest escape pointLe (stress.refinement index) test))
      ((generated stress pointLe).refinement : Filter ℕ)
        (𝓝 (inner ℂ candidate (testVector stress pointLe test)))) :
    candidate = action stress pointLe first last wave coordinate := by
  apply ext_inner_right ℂ
  intro target
  refine UniformSpace.Completion.induction_on target ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  intro test
  have same := tendsto_nhds_unique (actual (NativePositiveKernelCarrier.ofPreSpace _ test))
    (source_work_test stress pointLe first last wave coordinate (NativePositiveKernelCarrier.ofPreSpace _ test))
  simpa only [testVector_coe] using same

end
end SaturationMonoid.NavierStokes.NativeRecoveryTimeGramWrite
