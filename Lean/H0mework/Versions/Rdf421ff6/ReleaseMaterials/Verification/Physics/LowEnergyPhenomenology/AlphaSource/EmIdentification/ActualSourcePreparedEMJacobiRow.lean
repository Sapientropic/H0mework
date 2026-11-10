import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMClockEquation
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationOriginalFactorization

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMJacobiRow
open PreparationVacuumOriginalGreenFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open ActualEMAction ActualEMCarrierOwn ActualDressedFullCoulomb
open ActualSourcePreparedTemporalEMConstraint
open CanonicalGradedSpatialSource ActualDressedUniformMaterialCoefficients
open ActualDressedOrderedStatic ActualDressedZeroDamping ActualDressedCorrectedGreen
open ActualSourcePreparedEMClockEquation ActualSourcePreparedClockReducedPencil
open ActualSourcePreparedEMTwoClockCarrier ActualSourcePreparedReducedQuantumCofactor
open ActualSourcePreparedFourClockCarrier Polynomial
open scoped Matrix BigOperators
attribute [local irreducible] commonJacobi sourceEMClockJacobiRow
  sourceFourClockDenominator sourceEMTwoClockResponseNumerator
  sourceReducedClockFieldNumerator sourceReducedClockDeterminant correctedDet

def sourceEMRowProjectorTerms : List SourceTerm := [
  ⟨0,15,⟨0,0,0,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨0,16,⟨0,0,0,0⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨0,20,⟨0,0,0,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩]

def sourceEMStaticJacobiTerms : List SourceTerm :=
  productTerms sourceEMRowProjectorTerms
    (originalJacobiTerms.filter (fun a => a.powers.temporal = 0))

def sourceEMJacobiConstantTerms : List SourceTerm := [
  ⟨0,15,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/36:ℚ)⟩⟩⟩,
  ⟨0,16,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/36:ℚ)⟩⟩⟩,
  ⟨0,19,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/36:ℚ)⟩⟩⟩,
  ⟨0,20,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/18:ℚ)⟩⟩⟩,
  ⟨0,60,⟨0,0,0,0⟩,⟨⟨0,2⟩,⟨0,0⟩⟩⟩,
  ⟨0,76,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨0,82,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨0,100,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨0,106,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨0,253,⟨0,0,0,0⟩,⟨⟨0,(3/5:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨0,266,⟨0,0,0,0⟩,⟨⟨0,(-3/5:ℚ)⟩,⟨0,0⟩⟩⟩]

def sourceEMJacobiSpatialTerms : List SourceTerm := [
  ⟨0,259,⟨0,1,0,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨0,260,⟨0,1,0,0⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨0,264,⟨0,1,0,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨0,271,⟨0,0,1,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨0,272,⟨0,0,1,0⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨0,276,⟨0,0,1,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨0,283,⟨0,0,0,1⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨0,284,⟨0,0,0,1⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨0,288,⟨0,0,0,1⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩]

/-- All original source atoms are normalized; no physical coefficient is fitted. -/
theorem source_em_jacobi_terms_certificate :
    fastNormalizeTerms (sourceEMStaticJacobiTerms ++
      negativeTerms (sourceEMJacobiConstantTerms ++ sourceEMJacobiSpatialTerms)) = [] := by
  decide +kernel

private theorem static_terms_value (terms : List SourceTerm) (p : Fin 4 → ℂ)
    (static : p 0 = 0) :
    sourceMatrix (terms.filter (fun a => a.powers.temporal = 0)) p = sourceMatrix terms p := by
  induction terms with
  | nil => rfl
  | cons a rest ih =>
    by_cases same : a.powers.temporal = 0
    · simp [same, sourceMatrix_cons, ih]
    · have zero : a.matrix p = 0 := by
        ext i j
        simp [SourceTerm.matrix, Powers.value, static, zero_pow same]
      simp [same, sourceMatrix_cons, ih, zero]

theorem source_em_static_jacobi_original (p : Fin 4 → ℂ) (static : p 0 = 0) :
    sourceMatrix sourceEMStaticJacobiTerms p =
      sourceMatrix sourceEMRowProjectorTerms p * emOriginalJacobi p := by
  rw [sourceEMStaticJacobiTerms, productTerms_value, static_terms_value _ p static,
    em_jacobi_source]
  rfl

theorem source_em_static_jacobi_split (p : Fin 4 → ℂ) (static : p 0 = 0) :
    sourceMatrix sourceEMRowProjectorTerms p * emOriginalJacobi p =
      sourceMatrix sourceEMJacobiConstantTerms p + sourceMatrix sourceEMJacobiSpatialTerms p := by
  rw [← source_em_static_jacobi_original p static]
  have value := normalization_equal sourceEMStaticJacobiTerms
    (sourceEMJacobiConstantTerms ++ sourceEMJacobiSpatialTerms) source_em_jacobi_terms_certificate p
  rwa [sourceMatrix_append] at value

theorem source_em_row_projector_actual (p : Fin 4 → ℂ) (v : Fin 289 → ℂ) :
    (sourceMatrix sourceEMRowProjectorTerms p *ᵥ v) 0 =
      dotProduct sourceTemporalEMForce v := by
  have actual : dotProduct sourceTemporalEMForce v =
      (1/2:ℂ) * (-v (gaugeSlot 0 6) + v (gaugeSlot 0 7) - v (gaugeSlot 0 11)) := by
    exact em_projection_coordinates v 0
  rw [actual, show gaugeSlot 0 6 = (15 : Fin 289) from rfl,
    show gaugeSlot 0 7 = (16 : Fin 289) from rfl,
    show gaugeSlot 0 11 = (20 : Fin 289) from rfl]
  norm_num [sourceMatrix, sourceEMRowProjectorTerms, SourceTerm.matrix, Powers.value,
    coefficientValue, Matrix.add_mulVec, Matrix.single_mulVec, Pi.single_apply]
  ring

/-- The complete actual EM Jacobi row consumes the normalized source terms,
including all matter, coframe and auxiliary constant terms. -/
theorem source_em_jacobi_row_split (p : Fin 4 → ℂ) (static : p 0 = 0)
    (j : Fin 289) :
    (∑ i : Fin 289, sourceTemporalEMForce i * emOriginalJacobi p i j) =
      sourceMatrix sourceEMJacobiConstantTerms p 0 j +
        sourceMatrix sourceEMJacobiSpatialTerms p 0 j := by
  have source := congrFun (congrFun (source_em_static_jacobi_split p static) 0) j
  have actual := source_em_row_projector_actual p (fun i => emOriginalJacobi p i j)
  change (sourceMatrix sourceEMRowProjectorTerms p * emOriginalJacobi p) 0 j = _ at source
  change (sourceMatrix sourceEMRowProjectorTerms p * emOriginalJacobi p) 0 j =
    ∑ i : Fin 289, sourceTemporalEMForce i * emOriginalJacobi p i j at actual
  rw [← actual]
  exact source

private theorem clock_slice_eval (eps sigma : ℝ) (P : Parameters) :
    sourceClockEval eps sigma (staticIRClockSlice P) = MvPolynomial.eval (irValues eps sigma 0) P := by
  change (clockSpecialize eps (staticIRClockSlice P)).eval (sigma : ℂ) = _
  rw [ir_clock_specialize, damping_slice_eval]

private theorem force_clock_eval (eps sigma : ℝ) (i : Fin 289) :
    sourceClockEval eps sigma (sourceEMClockForce i) = sourceTemporalEMForce i := by
  simp [sourceClockEval, clockSpecialize, sourceEMClockForce]

private theorem X_clock_eval (eps sigma : ℝ) :
    sourceClockEval eps sigma (X : (ℂ[X])[X]) = (sigma : ℂ) := by
  simp [sourceClockEval, clockSpecialize]

def sourceEMJacobiLiteralRow (n : PhysicalMomentum) (eps : ℝ) (j : Fin 289) : ℂ :=
  sourceMatrix sourceEMJacobiConstantTerms (frequencyRay eps 0 n) 0 j +
    sourceMatrix sourceEMJacobiSpatialTerms (frequencyRay eps 0 n) 0 j

theorem source_em_clock_jacobi_literal (n : PhysicalMomentum) (eps sigma : ℝ) (j : Fin 289) :
    sourceClockEval eps sigma (sourceEMClockJacobiRow n j) =
      sourceEMJacobiLiteralRow n eps j := by
  have static : frequencyRay eps 0 n 0 = 0 := by
    change -Complex.I*((0*eps^2 : ℝ) : ℂ)=0
    simp only [zero_mul, Complex.ofReal_zero, mul_zero]
  have row : sourceClockEval eps sigma (sourceEMClockJacobiRow n j) =
      ∑ i : Fin 289, sourceTemporalEMForce i * emOriginalJacobi (frequencyRay eps 0 n) i j := by
    unfold sourceEMClockJacobiRow
    simp only [map_sum, map_mul, force_clock_eval, clock_slice_eval]
    apply Finset.sum_congr rfl
    intro i _
    have actual := congrFun (congrFun (common_jacobi_eval n eps sigma 0) i) j
    exact congrArg (fun z => sourceTemporalEMForce i * z) actual
  rw [row]
  unfold sourceEMJacobiLiteralRow
  exact source_em_jacobi_row_split (frequencyRay eps 0 n) static j

attribute [local irreducible] sourceTemporalEMForce sourceMatrix
  sourceEMJacobiConstantTerms sourceEMJacobiSpatialTerms sourceEMJacobiLiteralRow

private theorem literal_clock_row_eval (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (j : Fin 289) :
    sourceClockEval eps sigma (sourceEMClockReducedRow event n j) =
      (sigma : ℂ) * sourceClockEval eps sigma (sourceFourClockDenominator event n) *
        sourceEMJacobiLiteralRow n eps j -
          sourceClockEval eps sigma (sourceEMTwoClockResponseNumerator event n j) := by
  unfold sourceEMClockReducedRow
  rw [map_sub, map_mul, map_mul, X_clock_eval, source_em_clock_jacobi_literal]

/-- The actual cofactor field consumes both exact source groups. Matter,
coframe and auxiliary constants remain beside the spatial terms. -/
theorem source_em_clock_cofactor_literal (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (positive : 0 < sigma)
    (regular : correctedDet event eps 0 sigma n ≠ 0) :
    (∑ j : Fin 289,
      ((sigma : ℂ) * sourceClockEval eps sigma (sourceFourClockDenominator event n) *
        sourceEMJacobiLiteralRow n eps j -
            sourceClockEval eps sigma (sourceEMTwoClockResponseNumerator event n j)) *
              sourceReducedClockFieldNumerator event n eps sigma j) =
      sourceReducedClockDeterminant event n eps sigma *
        ((sigma : ℂ) * sourceClockEval eps sigma (sourceFourClockDenominator event n) *
          dotProduct sourceTemporalEMForce sourceTemporalEMForce) := by
  calc
    _ = ∑ j : Fin 289, sourceClockEval eps sigma (sourceEMClockReducedRow event n j) *
        sourceReducedClockFieldNumerator event n eps sigma j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [literal_clock_row_eval]
    _ = _ := source_em_clock_reduced_cofactor_field event n eps sigma positive regular

end LowEnergy.GaussComposite.ActualSourcePreparedEMJacobiRow
