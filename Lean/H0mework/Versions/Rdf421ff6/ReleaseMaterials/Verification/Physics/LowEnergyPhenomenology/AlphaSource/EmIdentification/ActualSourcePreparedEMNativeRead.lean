import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMNativeRow
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedMatterAuxiliaryNativeRead

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMNativeRead
open PreparationVacuumOriginalGreenFeedback ActualEMAction ActualEMCarrierOwn
open ActualPreparedMatterAuxiliary
open ActualDressedFullCoulomb
open ActualDressedEMNativeAuxiliary ActualDressedEMNativeSchurClock
open ActualDressedEMNativePrincipal ActualDressedEMNativeMomentum ActualPreparedNativeTemporal
open ActualSourcePreparedEMNativeRow ActualSourcePreparedTemporalEMConstraint
open ActualSourcePreparedReducedQuantumCofactor ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedTemporalQuantumIR ActualDressedCorrectedGreen
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open CanonicalGradedSpatialSource SourcePropagationNativeActionHessian
open ActualSourcePreparedN3EMChargeRead ActualDressedNoetherCoulombUnit
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open scoped Matrix BigOperators
attribute [local irreducible] sourceTemporalCorrectedField
  sourceReducedClockFieldNumerator sourceReducedClockDeterminant

def sourceEMNativeBackgroundRead (v : Fin 289 → ℂ) : ℂ :=
  (sourceMatrix sourceEMNativeBackgroundTerms 0 *ᵥ v) 0

def sourceEMNativeLowerRead (p : Fin 4 → ℂ) (v : Fin 289 → ℂ) : ℂ :=
  (sourceMatrix sourceEMNativeLowerTerms p *ᵥ v) 0

private theorem background_original (v : Fin 289 → ℂ) :
    sourceEMNativeBackgroundRead v =
      (nativeEMRestInsertion.transpose *ᵥ (nativeSchurMatrix 0 *ᵥ emRestSlice v)) 0 := by
  have row := source_em_native_schur_row 0 rfl v
  have lower : sourceMatrix sourceEMNativeLowerTerms 0 = 0 := by
    norm_num [sourceMatrix,sourceEMNativeLowerTerms,SourceTerm.matrix,Powers.value]
  have principal : sourceMatrix sourceEMNativePrincipalTerms 0 = 0 := by
    norm_num [sourceMatrix,sourceEMNativePrincipalTerms,SourceTerm.matrix,Powers.value]
  simpa only [sourceMatrix_append,lower,principal,add_zero,sourceEMNativeBackgroundRead] using row

private theorem lower_odd_read (p : Fin 4 → ℂ) (v : Fin 289 → ℂ) :
    sourceEMNativeLowerRead p v = (1/2 : ℂ) *
      ((sourceMatrix (sourceEMNativeBackgroundTerms ++ sourceEMNativeLowerTerms ++
          sourceEMNativePrincipalTerms) p *ᵥ v) 0 -
        (sourceMatrix (sourceEMNativeBackgroundTerms ++ sourceEMNativeLowerTerms ++
          sourceEMNativePrincipalTerms) (-p) *ᵥ v) 0) := by
  norm_num [sourceEMNativeLowerRead,sourceMatrix,sourceEMNativeBackgroundTerms,
    sourceEMNativeLowerTerms,sourceEMNativePrincipalTerms,SourceTerm.matrix,Powers.value,
    Matrix.add_mulVec,Matrix.single_mulVec,Pi.single_apply,Pi.neg_apply]
  ring

private theorem native_lower_odd (p : Fin 4 → ℂ) :
    nativeMomentumLower p = (1/2 : ℂ) • (nativeSchurMatrix p - nativeSchurMatrix (-p)) := by
  have equation := actual_native_momentum_decomposition p
  rw [← actual_native_schur_even_principal] at equation
  ext i j
  have entry := congrFun (congrFun equation i) j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] at entry ⊢
  linear_combination -entry

private theorem lower_original (p : Fin 4 → ℂ) (static : p 0 = 0) (v : Fin 289 → ℂ) :
    sourceEMNativeLowerRead p v =
      (nativeEMRestInsertion.transpose *ᵥ (nativeMomentumLower p *ᵥ emRestSlice v)) 0 := by
  have negative : (-p) 0 = 0 := by simp only [Pi.neg_apply,static,neg_zero]
  rw [lower_odd_read,source_em_native_schur_row p static,
    source_em_native_schur_row (-p) negative,native_lower_odd]
  simp only [Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.mulVec_smul,Matrix.mulVec_sub,
    Pi.smul_apply,Pi.sub_apply,smul_eq_mul]

/-- The ten generated coefficients consume the actual complete prepared field. -/
theorem source_em_native_background_actual (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) :
    sourceEMNativeBackgroundRead (sourceTemporalCorrectedField event e.val sigma n) =
      actualNativeBackgroundRead event e sigma n :=
  background_original _

/-- The six generated lower coefficients consume the same actual field. -/
theorem source_em_native_lower_actual (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) :
    sourceEMNativeLowerRead (frequencyRay e.val 0 n)
      (sourceTemporalCorrectedField event e.val sigma n) = actualNativeLowerRead event e sigma n := by
  have static : frequencyRay e.val 0 n 0 = 0 := by
    change -Complex.I*((0*e.val^2 : ℝ) : ℂ)=0
    simp
  exact lower_original _ static _

/-- Lower is homogeneous in the original momentum coordinates, while its
actual prepared field retains its full dependence on both scales. -/
theorem source_em_native_lower_scale (z : ℂ) (p : Fin 4 → ℂ) (v : Fin 289 → ℂ) :
    sourceEMNativeLowerRead (z • p) v = z * sourceEMNativeLowerRead p v := by
  norm_num [sourceEMNativeLowerRead,sourceMatrix,sourceEMNativeLowerTerms,SourceTerm.matrix,
    Powers.value,Matrix.add_mulVec,Matrix.single_mulVec,Pi.single_apply,Pi.smul_apply,smul_eq_mul]
  ring

/-- Both original IR coordinates use the source epsilon-squared spatial scale. -/
theorem source_em_native_lower_spatial_factor (eps : ℝ) (n : PhysicalMomentum)
    (v : Fin 289 → ℂ) :
    sourceEMNativeLowerRead (frequencyRay eps 0 n) v =
      (eps : ℂ)^2 * sourceEMNativeLowerRead (frequencyRay 1 0 n) v := by
  have ray : frequencyRay eps 0 n = (eps : ℂ)^2 • frequencyRay 1 0 n := by
    funext mu
    fin_cases mu <;> simp [frequencyRay,physicalFrequencyMomentum,Pi.smul_apply,
      smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_pow,Fin.cases,Fin.induction,Fin.induction.go] <;> ring
  rw [ray,source_em_native_lower_scale]

/-- The actual native equation directly consumes the finite source coefficients. -/
theorem source_em_native_scaled_finite_return (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n = 1)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0) :
    (e.val : ℂ)^4 * sourceN3TemporalEMCoefficient event e.val sigma n =
      noetherPairScale^2 / (2 * (lapse : ℂ)) *
        ((3/4 : ℂ) + dotProduct sourceTemporalEMForce
          (sourceTemporalActualQuantumDriver event e sigma n) -
          sourceEMNativeBackgroundRead (sourceTemporalCorrectedField event e.val sigma n) -
          (e.val : ℂ)^2 * sourceEMNativeLowerRead (frequencyRay 1 0 n)
            (sourceTemporalCorrectedField event e.val sigma n)) := by
  rw [← source_em_native_lower_spatial_factor,source_em_native_background_actual,
    source_em_native_lower_actual]
  exact actual_native_scaled_two_balance event e sigma n unit positive regular

/-- The same actual complete cofactor clears the generated background read. -/
theorem source_em_native_background_cofactor (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event e.val 0 sigma n ≠ 0) :
    sourceReducedClockDeterminant event n e.val sigma * actualNativeBackgroundRead event e sigma n =
      sourceEMNativeBackgroundRead (sourceReducedClockFieldNumerator event n e.val sigma) := by
  have paid := congrArg sourceEMNativeBackgroundRead
    (source_reduced_clock_actual_field_clear event n e.val sigma positive regular)
  simp only [sourceEMNativeBackgroundRead,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul] at paid
  rw [← source_em_native_background_actual]
  exact paid

/-- No new chart, denominator or field is introduced for the source lower read. -/
theorem source_em_native_lower_cofactor (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event e.val 0 sigma n ≠ 0) :
    sourceReducedClockDeterminant event n e.val sigma * actualNativeLowerRead event e sigma n =
      (e.val : ℂ)^2 * sourceEMNativeLowerRead (frequencyRay 1 0 n)
        (sourceReducedClockFieldNumerator event n e.val sigma) := by
  have paid := congrArg (sourceEMNativeLowerRead (frequencyRay e.val 0 n))
    (source_reduced_clock_actual_field_clear event n e.val sigma positive regular)
  simp only [sourceEMNativeLowerRead,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul] at paid
  rw [← source_em_native_lower_actual]
  rw [← source_em_native_lower_spatial_factor]
  exact paid

end LowEnergy.GaussComposite.ActualSourcePreparedEMNativeRead
