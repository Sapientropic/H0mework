import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedTemporalQuantumIR
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCommonCurrentNumerator

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedQuantumDriverCofactor
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open PreparationVacuumGaugeSourceInjection PreparationVacuumMixedPrincipal
open PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFullOriginResponse PreparationVacuumStaticPoleResponse
open PreparationPhysicalStaticSpatialCouplingReturn
open ActualEMAction ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedUniformMaterialCoefficients ActualDressedPhysicalRayNumerator
open LowEnergy.GaussComposite.ActualDressedVisiblePole ActualDressedZeroDamping
open ActualDressedEMTensorClock
open ActualSourcePreparedStaticCorrectedReturn ActualSourcePreparedEMEnclosure
open ActualSourcePreparedN3MovingResponse ActualSourcePreparedNoetherPi
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedTemporalQuantumIR
open scoped Matrix BigOperators
attribute [local irreducible] commonClearedPencil commonNumerator commonDenominator correctedGreen

def sourceQuantumDriverNumerator (event : DressedEvent) (n : PhysicalMomentum) : Fin 289 → Parameters :=
  (MvPolynomial.X 1 : Parameters) • ((commonNumerator event n)*ᵥ
    ((commonClearedPencil event n).adjugate*ᵥ(fun i => MvPolynomial.C (sourceTemporalEMForce i))))

private theorem cleared_driver {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J N : Matrix ι ι ℂ) (d s : ℂ) (a E : ι → ℂ)
    (clear : (d • J-s • N).det • a = d • ((d • J-s • N).adjugate*ᵥE)) :
    (d • J-s • N).det • (J*ᵥa-E) = s • (N*ᵥ((d • J-s • N).adjugate*ᵥE)) := by
  have adj := congrArg (fun M : Matrix ι ι ℂ => M*ᵥE) (Matrix.mul_adjugate (d • J-s • N))
  rw [←Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec] at adj
  rw [smul_sub, ←Matrix.mulVec_smul, clear, Matrix.mulVec_smul]
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp adj).trans (add_comm _ _))

private theorem mapped_pencil (event : DressedEvent) (epsilon sigma : ℝ) (n : PhysicalMomentum) :
    (commonClearedPencil event n).map (MvPolynomial.eval (irValues epsilon sigma 0)) =
      MvPolynomial.eval (irValues epsilon sigma 0) (commonDenominator event n) •
        emOriginalJacobi (frequencyRay epsilon 0 n) -
      (sigma : ℂ) • (commonNumerator event n).map (MvPolynomial.eval (irValues epsilon sigma 0)) := by
  let evaluation := MvPolynomial.eval (irValues epsilon sigma 0)
  unfold commonClearedPencil
  rw [Matrix.map_sub _ (fun a b => evaluation.map_sub a b),
    Matrix.map_smul' _ _ _ (fun a b => evaluation.map_mul a b),
    Matrix.map_smul' _ _ _ (fun a b => evaluation.map_mul a b), common_jacobi_eval]
  simp only [evaluation, MvPolynomial.eval_X, irValues, one_ne_zero, ite_false, ite_true]

private theorem numerator_eval (event : DressedEvent) (epsilon sigma : ℝ) (n : PhysicalMomentum) :
    (fun i => MvPolynomial.eval (irValues epsilon sigma 0) (sourceQuantumDriverNumerator event n i)) =
      (sigma : ℂ) • ((commonNumerator event n).map (MvPolynomial.eval (irValues epsilon sigma 0))*ᵥ
        (((commonClearedPencil event n).map (MvPolynomial.eval (irValues epsilon sigma 0))).adjugate*ᵥ
          sourceTemporalEMForce)) := by
  have mapped : (commonClearedPencil event n).adjugate.map (MvPolynomial.eval (irValues epsilon sigma 0)) =
      ((commonClearedPencil event n).map (MvPolynomial.eval (irValues epsilon sigma 0))).adjugate :=
    (MvPolynomial.eval (irValues epsilon sigma 0)).map_adjugate _
  rw [←mapped]
  funext i
  simp only [sourceQuantumDriverNumerator, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    map_mul, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X, irValues, one_ne_zero,
    ite_false, ite_true, Matrix.map_apply]

/-- Pi's source clearing factor cancels exactly against the original Green
cofactor. All quantum/contact terms remain in the single source numerator. -/
theorem source_quantum_driver_clear (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0) :
    MvPolynomial.eval (irValues e.val sigma 0) (commonDeterminant event n) •
      sourceTemporalActualQuantumDriver event e sigma n =
      (fun i => MvPolynomial.eval (irValues e.val sigma 0) (sourceQuantumDriverNumerator event n i)) := by
  have green := actual_common_green_adjugate event e.val sigma 0 n positive regular
  rw [←source_prepared_full_green_original event e.val sigma n positive regular] at green
  have field := congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ => M*ᵥsourceTemporalEMForce) green
  simp only [Matrix.smul_mulVec] at field
  have equation := source_temporal_corrected_field_equation event e.val sigma n positive regular
  change (emOriginalJacobi (frequencyRay e.val 0 n)-sourcePreparedClockQuantumMatrix event e.val sigma n)*ᵥ
    sourceTemporalCorrectedField event e.val sigma n = sourceTemporalEMForce at equation
  rw [Matrix.sub_mulVec] at equation
  have driver : sourceTemporalActualQuantumDriver event e sigma n =
      emOriginalJacobi (frequencyRay e.val 0 n)*ᵥsourceTemporalCorrectedField event e.val sigma n-
        sourceTemporalEMForce := by
    exact (sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp equation).trans (add_comm _ _))).symm
  rw [driver, numerator_eval]
  have cleared := cleared_driver (emOriginalJacobi (frequencyRay e.val 0 n))
    ((commonNumerator event n).map (MvPolynomial.eval (irValues e.val sigma 0)))
    (MvPolynomial.eval (irValues e.val sigma 0) (commonDenominator event n)) (sigma : ℂ)
    (sourceTemporalCorrectedField event e.val sigma n) sourceTemporalEMForce
    (by rw [←mapped_pencil, ←common_determinant_eval]; exact field)
  rw [←mapped_pencil, ←common_determinant_eval] at cleared
  exact cleared

/-- The exact native source reader used by the quantum spatial pole price. -/
def sourceQuantumNativeReader (e : scaleDomain) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius) : Matrix (Fin 289) (Fin 289) ℂ :=
  let kappa : staticDomain := ⟨e.val^2, pow_pos e.property.1 2, small⟩
  effectiveReader (sourceStaticSpatialPoint n unit kappa) * activeProjection *
    originalReadback (sourceStaticSpatialMomentum n kappa.val)

theorem source_quantum_native_reader_actual (e : scaleDomain) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius) (v : Fin 289 → ℂ) :
    sourceQuantumNativeReader e n unit small*ᵥv =
      sourceSpatialStaticSourceReader n unit ⟨e.val^2, pow_pos e.property.1 2, small⟩ v := by
  simp only [sourceQuantumNativeReader, sourceSpatialStaticSourceReader, sourceSpatialStaticActiveForcing,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

def sourceQuantumNativeReaderNumerator (event : DressedEvent) (e : scaleDomain)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius) (i : Fin 289) : Parameters :=
  dotProduct (fun j => MvPolynomial.C (sourceQuantumNativeReader e n unit small i j))
    (sourceQuantumDriverNumerator event n)

theorem source_quantum_native_reader_clear (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0) (i : Fin 289) :
    MvPolynomial.eval (irValues e.val sigma 0) (commonDeterminant event n) *
      sourceSpatialStaticSourceReader n unit ⟨e.val^2, pow_pos e.property.1 2, small⟩
        (sourceTemporalActualQuantumDriver event e sigma n) i =
      MvPolynomial.eval (irValues e.val sigma 0) (sourceQuantumNativeReaderNumerator event e n unit small i) := by
  have field := congrArg (fun v => (sourceQuantumNativeReader e n unit small*ᵥv) i)
    (source_quantum_driver_clear event e sigma n positive regular)
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, source_quantum_native_reader_actual] at field
  exact field.trans (by simp only [sourceQuantumNativeReaderNumerator, Matrix.mulVec, dotProduct,
    map_sum, map_mul, MvPolynomial.eval_C])

def sourceQuantumNativeReaderFraction (event : DressedEvent) (e : scaleDomain)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius) (i : Fin 289) : RatFunc ℂ :=
  LowEnergy.ActualDressedVisiblePole.readFraction
    (dampingSlice e.val (sourceQuantumNativeReaderNumerator event e n unit small i))
    (dampingDeterminant event e.val n)

open LowEnergy.ActualDressedVisiblePole Filter Set
open scoped Topology

theorem source_quantum_native_reader_fraction (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius)
    (positive : 0 < sigma) (chart : (dampingDeterminant event e.val n).eval (sigma : ℂ) ≠ 0) (i : Fin 289) :
    let R := sourceQuantumNativeReaderFraction event e n unit small i
    sourceSpatialStaticSourceReader n unit ⟨e.val^2, pow_pos e.property.1 2, small⟩
      (sourceTemporalActualQuantumDriver event e sigma n) i = R.num.eval (sigma : ℂ)/R.denom.eval (sigma : ℂ) := by
  have nonzero : MvPolynomial.eval (irValues e.val sigma 0) (commonDeterminant event n) ≠ 0 := by
    rw [←damping_slice_eval]; exact chart
  have regular := actual_common_chart_original event e.val sigma 0 n positive nonzero
  have original := (eq_div_iff nonzero).mpr ((mul_comm _ _).trans
    (source_quantum_native_reader_clear event e sigma n unit small positive regular i))
  refine original.trans ?_
  rw [←damping_slice_eval, ←damping_slice_eval]
  exact (reduced_read_at_regular _ _ (sigma : ℂ) chart).symm

private theorem positive_complex_punctured :
    Tendsto (fun sigma : ℝ => (sigma : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero] using (ne_of_gt positive)

/-- The actual spatial-pole source reader generates its own clock order and
leading coefficient; neither the entire Green nor its columns are balanced. -/
theorem source_quantum_native_reader_clock_return (event : DressedEvent) (e : scaleDomain)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius)
    (nonzero : dampingDeterminant event e.val n ≠ 0) (i : Fin 289) :
    let R := sourceQuantumNativeReaderFraction event e n unit small i
    Tendsto (fun sigma : ℝ => (sigma : ℂ)^poleOrder R 0 *
      sourceSpatialStaticSourceReader n unit ⟨e.val^2, pow_pos e.property.1 2, small⟩
        (sourceTemporalActualQuantumDriver event e sigma n) i)
      (𝓝[>] 0) (𝓝 (leadingPoleCoefficient R 0)) := by
  let R := sourceQuantumNativeReaderFraction event e n unit small i
  have base := (pole_order_limit R 0).comp positive_complex_punctured
  simp only [Function.comp_def, sub_zero] at base
  apply Tendsto.congr' ?_ base
  have inclusion : Ioi (0 : ℝ) ⊆ ({0}ᶜ) := by
    intro sigma positive
    simpa only [mem_compl_iff, mem_singleton_iff] using (ne_of_gt positive)
  have chart := (source_static_punctured_chart _ nonzero).filter_mono (nhdsWithin_mono 0 inclusion)
  filter_upwards [chart, self_mem_nhdsWithin] with sigma regular positive
  exact congrArg (fun v : ℂ => (sigma : ℂ)^poleOrder R 0*v)
    (source_quantum_native_reader_fraction event e sigma n unit small positive regular i).symm

end LowEnergy.GaussComposite.ActualSourcePreparedQuantumDriverCofactor
