import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedMatterClockReduction
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedQuantumColumnClock
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMEnclosure

set_option autoImplicit false
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualPreparedMatterClock
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedEMTensorClock ActualEMAction
open PreparationVacuumPhysicalCharacteristic ActualDressedUniformMaterialCoefficients
open ActualDressedCorrectedGreen ActualSourcePreparedTemporalEMConstraint
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open ActualSourcePreparedTemporalQuantumIR
open ActualSourcePreparedTemporalQuantumWard ActualDressedOrderedStatic ActualDressedZeroDamping
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedFourClockCarrier
open ActualSourcePreparedEMClockEquation ActualSourcePreparedStaticCorrectedReturn
open ActualSourcePreparedEMNativeRead ActualSourcePreparedN3EMChargeRead ActualDressedNoetherCoulombUnit
open ActualSourcePreparedReducedQuantumCofactor ActualSourcePreparedAuxiliaryClockReduction
open ActualSourcePreparedAuxiliaryActualReturn ActualPreparedMatterSupport
open ActualSourcePreparedQuantumColumnClock ActualSourcePreparedEMEnclosure
open ActualDressedEMZeroClockColumns
open scoped Matrix BigOperators
attribute [local irreducible] sourceMatterClockPencil sourceMatterRemainingRowWeight
  sourceAuxiliaryReducedPencil sourceReducedClockDeterminant sourceReducedClockMatrix
  Matrix.det Matrix.adjugate Matrix.mulVec sourcePreparedStaticPencil

private theorem mapped_det_factor {R S I : Type*} [CommRing R] [CommRing S]
    [Fintype I] [DecidableEq I] (f : R →+* S) (a : R) (k : ℕ)
    (K P : Matrix I I R) (factor : K.det=a^k*P.det) :
    (K.map f).det=(f a)^k*(P.map f).det := by
  have mapped (M : Matrix I I R) : f M.det=(M.map f).det := by
    simpa only [RingHom.mapMatrix_apply] using f.map_det M
  rw [←mapped,factor,map_mul,map_pow,mapped]

private theorem matter_clock_factor_eval (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : sourceClockEval epsilon sigma (sourceAuxiliaryClockFactor event n)=
      (sigma : ℂ)^3*sourceClockEval epsilon sigma (sourceFourClockDenominator event n) := by
  have clock : sourceClockEval epsilon sigma (X : (ℂ[X])[X])=(sigma : ℂ) := by
    simp only [sourceClockEval,RingHom.comp_apply,clockSpecialize,Polynomial.coe_mapRingHom,
      Polynomial.map_X,Polynomial.coe_evalRingHom,Polynomial.eval_X]
  simp only [sourceAuxiliaryClockFactor,map_mul,map_pow,clock]

private theorem matter_clock_point_nonzero (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0<sigma) :
    sourceClockEval epsilon sigma (sourceAuxiliaryClockFactor event n)≠0 := by
  rw [matter_clock_factor_eval]
  exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr positive.ne'))
    (source_reduced_clock_denominator_nonzero event n epsilon sigma positive)

/-- The evaluated forcing weight keeps the inactive rows at weight one and the
active rows at the common clock point. -/
def sourceMatterClockForcingWeight (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (i : Fin 289) : ℂ :=
  if (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val then 1
    else sourceClockEval epsilon sigma (sourceAuxiliaryClockFactor event n)

/-- The evaluated canonical pencil carries the forcing weight only on the
still-active rows: the 192 inactive rows already carry the evaluated static
slice because their Pi rows vanish. -/
private theorem matter_pencil_eval_weighted (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0<sigma) :
    (sourceMatterClockPencil event n).map (sourceClockEval epsilon sigma)=
      Matrix.diagonal (sourceMatterClockForcingWeight event n epsilon sigma)*
        sourcePreparedStaticPencil event epsilon sigma n := by
  apply Matrix.ext
  intro i j
  rw [Matrix.diagonal_mul]
  by_cases outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val
  · have real_positive : 0<(sigma : ℂ).re := by simpa only [Complex.ofReal_re] using positive
    have pi_zero := actual_prepared_inactive_pi_row event (epsilon^2 • n) (sigma : ℂ)
      real_positive i outside j
    have slice : sourceClockEval epsilon sigma (staticIRClockSlice (commonJacobi n i j))=
        MvPolynomial.eval (irValues epsilon sigma 0) (commonJacobi n i j) := by
      change (clockSpecialize epsilon (staticIRClockSlice (commonJacobi n i j))).eval
          (sigma : ℂ)=_
      rw [ir_clock_specialize,damping_slice_eval]
    have jacobi := congrFun (congrFun (common_jacobi_eval n epsilon sigma 0) i) j
    change MvPolynomial.eval (irValues epsilon sigma 0) (commonJacobi n i j)=
      emOriginalJacobi (frequencyRay epsilon 0 n) i j at jacobi
    have entry : sourcePreparedStaticPencil event epsilon sigma n i j=
        emOriginalJacobi (frequencyRay epsilon 0 n) i j-
          (sigma : ℂ)*ActualSourcePreparedNoetherPi.sourcePreparedPiEntry
            event (epsilon^2 • n) (↑sigma) i j := by
      simp only [sourcePreparedStaticPencil,Matrix.sub_apply]
      change _ - ((sigma : ℝ) • ActualSourcePreparedNoetherPi.sourcePreparedPiEntry
          event (epsilon^2 • n) (↑sigma) i j) = _
      rfl
    rw [pi_zero,mul_zero,sub_zero] at entry
    change (sourceClockEval epsilon sigma) (sourceMatterClockPencil event n i j)=_
    simp only [sourceMatterClockPencil]
    rw [if_pos outside,slice,jacobi]
    simp only [outside,if_true,one_mul,entry,sourceMatterClockForcingWeight]
  · have actual := congrFun (congrFun
        (source_clock_reduced_pencil_actual event n epsilon sigma positive) i) j
    have paidScalar := actual
    simp only [Matrix.map_apply,Matrix.smul_apply,smul_eq_mul] at paidScalar
    change (sourceClockEval epsilon sigma) (sourceMatterClockPencil event n i j)=_
    simp only [sourceMatterClockPencil]
    rw [if_neg outside]
    rw [paidScalar]
    simp only [outside,if_false,sourceMatterClockForcingWeight,matter_clock_factor_eval]

/-- A common comm-ring step: a left factor `A*G=W` transported across the
adjugate gives `det A • G = adj A * W`, all 289 columns kept. -/
private theorem green_cofactor {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (A G W : Matrix I I R) (inverse : A*G=W) :
    A.det • G=A.adjugate*W := by
  rw [←inverse,←Matrix.mul_assoc,Matrix.adjugate_mul,Matrix.smul_mul,Matrix.one_mul]

/-- Every forcing column is preserved: the reduced adjugate times the diagonal
forcing weight is the new determinant times the original corrected Green. -/
theorem source_matter_full_green_cofactor_clear (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0<sigma)
    (regular : correctedDet event epsilon 0 sigma n≠0) :
    ((sourceMatterClockPencil event n).map (sourceClockEval epsilon sigma)).det •
        correctedGreen event epsilon 0 sigma n=
      ((sourceMatterClockPencil event n).map (sourceClockEval epsilon sigma)).adjugate*
        Matrix.diagonal (sourceMatterClockForcingWeight event n epsilon sigma) := by
  have weighted := matter_pencil_eval_weighted event n epsilon sigma positive
  have inverse := (source_prepared_static_green_inverse event epsilon sigma n
    positive regular).1
  have product : (sourceMatterClockPencil event n).map (sourceClockEval epsilon sigma)*
      correctedGreen event epsilon 0 sigma n=
      Matrix.diagonal (sourceMatterClockForcingWeight event n epsilon sigma) := by
    rw [weighted,Matrix.mul_assoc,inverse,Matrix.mul_one]
  exact green_cofactor _ _ _ product

/-- The auxiliary determinant loses exactly the generated remaining factor;
the physical fields and all remaining rows are unchanged. -/
def sourceMatterClockActualDeterminant (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : ℂ :=
  ((sourceMatterClockPencil event n).map (sourceClockEval epsilon sigma)).det

theorem source_matter_actual_det_factor (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : sourceAuxiliaryActualDeterminant event n epsilon sigma=
      (sourceClockEval epsilon sigma (sourceAuxiliaryClockFactor event n))^120*
        sourceMatterClockActualDeterminant event n epsilon sigma := by
  unfold sourceAuxiliaryActualDeterminant sourceMatterClockActualDeterminant
  exact mapped_det_factor (sourceClockEval epsilon sigma)
    (sourceAuxiliaryClockFactor event n) 120 (sourceAuxiliaryReducedPencil event n)
    (sourceMatterClockPencil event n) (source_matter_auxiliary_determinant_factor event n)

/-- The actual field numerator is the reduced adjugate on the weighted full
forcing, equal to the clock factor times the same cofactor direction. -/
def sourceMatterClockActualFieldNumerator (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : Fin 289 → ℂ :=
  (((sourceMatterClockPencil event n).map (sourceClockEval epsilon sigma)).adjugate*
      Matrix.diagonal (sourceMatterClockForcingWeight event n epsilon sigma))*ᵥ
    sourceTemporalEMForce

private theorem weighted_force_point (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) :
    Matrix.diagonal (sourceMatterClockForcingWeight event n epsilon sigma)*ᵥ
        sourceTemporalEMForce=
      sourceClockEval epsilon sigma (sourceAuxiliaryClockFactor event n) •
        sourceTemporalEMForce := by
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val
  · have zero := actual_em_force_inactive_zero i outside
    simp only [sourceMatterClockForcingWeight,outside,if_true,zero,mul_zero,
      Pi.smul_apply,smul_eq_mul]
  · simp only [sourceMatterClockForcingWeight,outside,if_false,
      Pi.smul_apply,smul_eq_mul]

/-- Same actual GE0 on its chart; the Green transport supplies the new
cofactor without any new regularity or field-norm premise. -/
theorem source_matter_actual_field_clear (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0<sigma)
    (regular : correctedDet event epsilon 0 sigma n≠0) :
    sourceMatterClockActualDeterminant event n epsilon sigma •
      sourceTemporalCorrectedField event epsilon sigma n=
      sourceMatterClockActualFieldNumerator event n epsilon sigma := by
  have key := source_matter_full_green_cofactor_clear event n epsilon sigma positive regular
  have applied := congrArg (·*ᵥ sourceTemporalEMForce) key
  rw [Matrix.smul_mulVec] at applied
  have green : correctedGreen event epsilon 0 sigma n *ᵥ sourceTemporalEMForce=
      sourceTemporalCorrectedField event epsilon sigma n := by
    unfold sourceTemporalCorrectedField
    rw [source_prepared_full_green_original event epsilon sigma n positive regular]
  rw [green] at applied
  unfold sourceMatterClockActualFieldNumerator sourceMatterClockActualDeterminant
  exact applied

theorem source_matter_actual_determinant_nonzero (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0<sigma)
    (regular : correctedDet event epsilon 0 sigma n≠0) :
    sourceMatterClockActualDeterminant event n epsilon sigma≠0 := by
  have original := source_auxiliary_actual_determinant_nonzero event n epsilon sigma
    positive regular
  rw [source_matter_actual_det_factor] at original
  exact (mul_ne_zero_iff.mp original).2

/-- Both actual field clears commute on the same actual field carrier:
`Naux = Daux•a = c^120•(Dnew•a) = c^120•Nnew`. -/
theorem source_matter_actual_field_factor (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0<sigma)
    (regular : correctedDet event epsilon 0 sigma n≠0) :
    sourceAuxiliaryActualFieldNumerator event n epsilon sigma=
      (sourceClockEval epsilon sigma (sourceAuxiliaryClockFactor event n))^120 •
        sourceMatterClockActualFieldNumerator event n epsilon sigma := by
  have field := source_auxiliary_actual_field_clear event n epsilon sigma positive regular
  rw [source_matter_actual_det_factor,mul_smul,
    source_matter_actual_field_clear event n epsilon sigma positive regular] at field
  exact field.symm

private theorem driver_factor {R I : Type*} [CommRing R] [Fintype I]
    (J : Matrix I I R) (e N F : I → R) (D d b : R)
    (field : N=b • F) (denominator : D=b*d) :
    J*ᵥN-D • e=b • (J*ᵥF-d • e) := by
  rw [field,denominator,Matrix.mulVec_smul,smul_sub,smul_smul]

def sourceMatterClockActualDriverNumerator (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : Fin 289 → ℂ :=
  emOriginalJacobi (frequencyRay epsilon 0 n)*ᵥ
    sourceMatterClockActualFieldNumerator event n epsilon sigma -
      sourceMatterClockActualDeterminant event n epsilon sigma • sourceTemporalEMForce

theorem source_matter_actual_driver_factor (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0<sigma)
    (regular : correctedDet event epsilon 0 sigma n≠0) :
    sourceAuxiliaryActualDriverNumerator event n epsilon sigma=
      (sourceClockEval epsilon sigma (sourceAuxiliaryClockFactor event n))^120 •
        sourceMatterClockActualDriverNumerator event n epsilon sigma := by
  unfold sourceAuxiliaryActualDriverNumerator sourceMatterClockActualDriverNumerator
  exact driver_factor _ _ _ _ _ _ _
    (source_matter_actual_field_factor event n epsilon sigma positive regular)
    (source_matter_actual_det_factor event n epsilon sigma)

/-- The complete quantum/contact driver consumes the same remaining
cancellation as the actual field, through the original `J*a-E0` equation. -/
theorem source_matter_actual_driver_clear (event : DressedEvent) (n : PhysicalMomentum)
    (e : scaleDomain) (sigma : ℝ) (positive : 0<sigma)
    (regular : correctedDet event e.val 0 sigma n≠0) :
    sourceMatterClockActualDeterminant event n e.val sigma •
      sourceTemporalActualQuantumDriver event e sigma n=
      sourceMatterClockActualDriverNumerator event n e.val sigma := by
  have column := source_quantum_driver_em_column event e sigma n positive regular
  have bridge : correctedEMColumn event e.val 0 sigma n 0=
      sourceTemporalCorrectedField event e.val sigma n := by
    unfold correctedEMColumn sourceTemporalCorrectedField
    rw [source_prepared_full_green_original event e.val sigma n positive regular]
    unfold sourceTemporalEMForce
    rfl
  rw [bridge] at column
  unfold sourceMatterClockActualDriverNumerator
  rw [column,smul_sub,←Matrix.mulVec_smul,
    source_matter_actual_field_clear event n e.val sigma positive regular]

/-- The full source EM balance over the new canonical denominator; the same
ten background and six lower terms consume the same numerator. -/
def sourceMatterReducedEMBalance (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : ℂ :=
  (dotProduct sourceTemporalEMForce (sourceMatterClockActualDriverNumerator event n epsilon sigma) -
    sourceEMNativeBackgroundRead (sourceMatterClockActualFieldNumerator event n epsilon sigma) -
      (epsilon : ℂ)^2 * sourceEMNativeLowerRead (frequencyRay 1 0 n)
        (sourceMatterClockActualFieldNumerator event n epsilon sigma)) /
    sourceMatterClockActualDeterminant event n epsilon sigma

theorem source_matter_reduced_balance_original (event : DressedEvent) (n : PhysicalMomentum)
    (e : scaleDomain) (sigma : ℝ) (positive : 0<sigma)
    (regular : correctedDet event e.val 0 sigma n≠0) :
    sourceMatterReducedEMBalance event n e.val sigma=
      sourceAuxiliaryReducedEMBalance event n e.val sigma := by
  have factor := matter_clock_point_nonzero event n e.val sigma positive
  unfold sourceMatterReducedEMBalance sourceAuxiliaryReducedEMBalance
  rw [source_matter_actual_det_factor,
    source_matter_actual_driver_factor event n e.val sigma positive regular,
    source_matter_actual_field_factor event n e.val sigma positive regular]
  have drive_lin : dotProduct sourceTemporalEMForce
        (((sourceClockEval e.val sigma (sourceAuxiliaryClockFactor event n))^120 •
          sourceMatterClockActualDriverNumerator event n e.val sigma))=
      (sourceClockEval e.val sigma (sourceAuxiliaryClockFactor event n))^120*
        dotProduct sourceTemporalEMForce
          (sourceMatterClockActualDriverNumerator event n e.val sigma) := by
    simp only [dotProduct_smul,smul_eq_mul]
  have bg_lin : sourceEMNativeBackgroundRead
        (((sourceClockEval e.val sigma (sourceAuxiliaryClockFactor event n))^120 •
          sourceMatterClockActualFieldNumerator event n e.val sigma))=
      (sourceClockEval e.val sigma (sourceAuxiliaryClockFactor event n))^120*
        sourceEMNativeBackgroundRead
          (sourceMatterClockActualFieldNumerator event n e.val sigma) := by
    simp only [sourceEMNativeBackgroundRead,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul]
  have lo_lin : sourceEMNativeLowerRead (frequencyRay 1 0 n)
        (((sourceClockEval e.val sigma (sourceAuxiliaryClockFactor event n))^120 •
          sourceMatterClockActualFieldNumerator event n e.val sigma))=
      (sourceClockEval e.val sigma (sourceAuxiliaryClockFactor event n))^120*
        sourceEMNativeLowerRead (frequencyRay 1 0 n)
          (sourceMatterClockActualFieldNumerator event n e.val sigma) := by
    simp only [sourceEMNativeLowerRead,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul]
  rw [drive_lin,bg_lin,lo_lin]
  have numfact : (sourceClockEval e.val sigma (sourceAuxiliaryClockFactor event n))^120*
        dotProduct sourceTemporalEMForce
          (sourceMatterClockActualDriverNumerator event n e.val sigma) -
      (sourceClockEval e.val sigma (sourceAuxiliaryClockFactor event n))^120*
        sourceEMNativeBackgroundRead
          (sourceMatterClockActualFieldNumerator event n e.val sigma) -
      (e.val : ℂ)^2 *
        ((sourceClockEval e.val sigma (sourceAuxiliaryClockFactor event n))^120*
          sourceEMNativeLowerRead (frequencyRay 1 0 n)
            (sourceMatterClockActualFieldNumerator event n e.val sigma))=
      (sourceClockEval e.val sigma (sourceAuxiliaryClockFactor event n))^120*
        (dotProduct sourceTemporalEMForce
          (sourceMatterClockActualDriverNumerator event n e.val sigma) -
        sourceEMNativeBackgroundRead
          (sourceMatterClockActualFieldNumerator event n e.val sigma) -
        (e.val : ℂ)^2 * sourceEMNativeLowerRead (frequencyRay 1 0 n)
          (sourceMatterClockActualFieldNumerator event n e.val sigma)) := by
    ring
  rw [numfact]
  exact (mul_div_mul_left _ _ (pow_ne_zero _ factor)).symm

/-- The original finite native equation consumes the reduced full balance;
no IR limit, unit-field or new photon/charge normalization is supplied. -/
theorem source_em_matter_reduced_finite_return (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (positive : 0<sigma) (regular : correctedDet event e.val 0 sigma n≠0) :
    (e.val : ℂ)^4 * sourceN3TemporalEMCoefficient event e.val sigma n=
      noetherPairScale^2 / (2*(lapse : ℂ)) *
        ((3/4 : ℂ)+sourceMatterReducedEMBalance event n e.val sigma) := by
  rw [source_em_auxiliary_reduced_finite_return event e sigma n unit positive regular,
    ←source_matter_reduced_balance_original event n e sigma positive regular]

end LowEnergy.GaussComposite.ActualPreparedMatterClock
