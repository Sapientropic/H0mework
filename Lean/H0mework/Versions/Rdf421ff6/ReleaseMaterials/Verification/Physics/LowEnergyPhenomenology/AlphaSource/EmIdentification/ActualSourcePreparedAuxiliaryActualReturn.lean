import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedAuxiliaryClockReduction

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedAuxiliaryActualReturn
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedEMTensorClock ActualEMAction
open PreparationVacuumPhysicalCharacteristic ActualDressedUniformMaterialCoefficients
open ActualDressedCorrectedGreen ActualSourcePreparedTemporalEMConstraint
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open ActualSourcePreparedTemporalQuantumIR
open ActualSourcePreparedTemporalQuantumWard ActualDressedOrderedStatic ActualDressedZeroDamping
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedFourClockCarrier
open ActualSourcePreparedEMClockEquation
open ActualSourcePreparedEMNativeRead ActualSourcePreparedN3EMChargeRead ActualDressedNoetherCoulombUnit
open ActualSourcePreparedReducedQuantumCofactor ActualSourcePreparedAuxiliaryClockReduction
open scoped Matrix BigOperators
attribute [local irreducible] sourceClockReducedPencil sourceFourClockDenominator
  sourceReducedClockFieldNumerator sourceReducedClockDeterminant sourceReducedClockMatrix
  sourceAuxiliaryReducedPencil Matrix.det Matrix.adjugate Matrix.mulVec

private theorem map_smul_vector {R S I : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : R) (v : I → R) : f ∘ (a • v)=f a • (f ∘ v) := by
  funext i
  exact f.map_mul a (v i)

private theorem map_cofactor_vector {R S I : Type*} [CommRing R] [CommRing S]
    [Fintype I] [DecidableEq I] (f : R →+* S) (a : R) (K : Matrix I I R) (e : I → R) :
    f ∘ (a • (K.adjugate*ᵥe))=f a • ((K.map f).adjugate*ᵥ(f ∘ e)) := by
  rw [map_smul_vector]
  congr 1
  funext i
  rw [Function.comp_apply,f.map_mulVec]
  have adj := f.map_adjugate K
  simp only [RingHom.mapMatrix_apply] at adj
  rw [adj]

private theorem mapped_field_factor {R S I : Type*} [CommRing R] [CommRing S]
    [Fintype I] [DecidableEq I] (f : R →+* S) (a : R) (k : ℕ)
    (K : Matrix I I R) (e N : I → R)
    (factor : a • (K.adjugate*ᵥe)=a^k • N) :
    f a • ((K.map f).adjugate*ᵥ(f ∘ e))=(f a)^k • (f ∘ N) := by
  have mapped := congrArg (fun v : I → R => f ∘ v) factor
  rw [map_cofactor_vector,map_smul_vector,map_pow] at mapped
  exact mapped

private theorem mapped_det_factor {R S I : Type*} [CommRing R] [CommRing S]
    [Fintype I] [DecidableEq I] (f : R →+* S) (a : R) (k : ℕ)
    (K P : Matrix I I R) (factor : K.det=a^k*P.det) :
    (K.map f).det=(f a)^k*(P.map f).det := by
  have mapped (M : Matrix I I R) : f M.det=(M.map f).det := by
    simpa only [RingHom.mapMatrix_apply] using f.map_det M
  rw [←mapped,factor,map_mul,map_pow,mapped]

private theorem clock_force_eval (epsilon sigma : ℝ) :
    sourceClockEval epsilon sigma ∘ sourceEMClockForce=sourceTemporalEMForce := by
  funext i
  simp only [Function.comp_apply,sourceEMClockForce,sourceClockEval,RingHom.comp_apply,
    clockSpecialize,Polynomial.coe_mapRingHom,Polynomial.map_C,
    Polynomial.coe_evalRingHom,Polynomial.eval_C]

private theorem clock_factor_eval (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : sourceClockEval epsilon sigma (sourceAuxiliaryClockFactor event n)=
      (sigma : ℂ)^3*sourceClockEval epsilon sigma (sourceFourClockDenominator event n) := by
  have clock : sourceClockEval epsilon sigma (X : (ℂ[X])[X])=(sigma : ℂ) := by
    simp only [sourceClockEval,RingHom.comp_apply,clockSpecialize,Polynomial.coe_mapRingHom,
      Polynomial.map_X,Polynomial.coe_evalRingHom,Polynomial.eval_X]
  simp only [sourceAuxiliaryClockFactor,map_mul,map_pow,clock]

def sourceAuxiliaryActualDeterminant (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : ℂ :=
  ((sourceAuxiliaryReducedPencil event n).map (sourceClockEval epsilon sigma)).det

def sourceAuxiliaryActualFieldNumerator (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : Fin 289 → ℂ :=
  sourceClockEval epsilon sigma ∘ sourceAuxiliaryReducedFieldNumerator event n

/-- The original chart denominator loses exactly the source-generated
auxiliary factor. The physical fields and all remaining rows are unchanged. -/

theorem source_auxiliary_actual_determinant_factor (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : sourceReducedClockDeterminant event n epsilon sigma=
      (sourceClockEval epsilon sigma (sourceAuxiliaryClockFactor event n))^72*
        sourceAuxiliaryActualDeterminant event n epsilon sigma := by
  unfold sourceReducedClockDeterminant sourceReducedClockMatrix sourceAuxiliaryActualDeterminant
  exact mapped_det_factor (sourceClockEval epsilon sigma) (sourceAuxiliaryClockFactor event n) 72
    (sourceClockReducedPencil event n) (sourceAuxiliaryReducedPencil event n)
    (source_auxiliary_determinant_factor event n)

theorem source_auxiliary_actual_field_factor (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : sourceReducedClockFieldNumerator event n epsilon sigma=
      (sourceClockEval epsilon sigma (sourceAuxiliaryClockFactor event n))^72 •
        sourceAuxiliaryActualFieldNumerator event n epsilon sigma := by
  have mapped := mapped_field_factor (sourceClockEval epsilon sigma) (sourceAuxiliaryClockFactor event n) 72
    (sourceClockReducedPencil event n) sourceEMClockForce
    (sourceAuxiliaryClockFactor event n • ((sourceAuxiliaryReducedPencil event n).adjugate*ᵥsourceEMClockForce))
    (source_auxiliary_field_cofactor_factor event n)
  rw [clock_force_eval,clock_factor_eval] at mapped
  rw [clock_factor_eval]
  unfold sourceReducedClockFieldNumerator sourceReducedClockMatrix sourceAuxiliaryActualFieldNumerator
    sourceAuxiliaryReducedFieldNumerator
  exact mapped

private theorem cancel_vector_factor {I : Type*} (b d : ℂ) (v N : I → ℂ)
    (nonzero : b≠0) (clear : (b*d) • v=b • N) : d • v=N := by
  funext i
  apply mul_left_cancel₀ nonzero
  have entry := congrFun clear i
  change (b*d)*v i=b*N i at entry
  exact (mul_assoc b d (v i)).symm.trans entry

private theorem clock_factor_nonzero (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0<sigma) :
    sourceClockEval epsilon sigma (sourceAuxiliaryClockFactor event n)≠0 := by
  rw [clock_factor_eval]
  exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr positive.ne'))
    (source_reduced_clock_denominator_nonzero event n epsilon sigma positive)

/-- Same actual GE0 on its original chart; auxiliary cancellation supplies
the reduced cofactor without imposing a new regularity or field norm. -/

theorem source_auxiliary_actual_field_clear (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0<sigma)
    (regular : correctedDet event epsilon 0 sigma n≠0) :
    sourceAuxiliaryActualDeterminant event n epsilon sigma •
      sourceTemporalCorrectedField event epsilon sigma n=
      sourceAuxiliaryActualFieldNumerator event n epsilon sigma := by
  have original := source_reduced_clock_actual_field_clear event n epsilon sigma positive regular
  rw [source_auxiliary_actual_determinant_factor,source_auxiliary_actual_field_factor] at original
  exact cancel_vector_factor _ _ _ _
    (pow_ne_zero _ (clock_factor_nonzero event n epsilon sigma positive)) original

theorem source_auxiliary_actual_determinant_nonzero (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0<sigma)
    (regular : correctedDet event epsilon 0 sigma n≠0) :
    sourceAuxiliaryActualDeterminant event n epsilon sigma≠0 := by
  have original := source_reduced_clock_determinant_nonzero event n epsilon sigma positive regular
  rw [source_auxiliary_actual_determinant_factor] at original
  exact (mul_ne_zero_iff.mp original).2

theorem source_auxiliary_actual_field_fraction (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0<sigma)
    (regular : correctedDet event epsilon 0 sigma n≠0) (i : Fin 289) :
    sourceTemporalCorrectedField event epsilon sigma n i=
      sourceAuxiliaryActualFieldNumerator event n epsilon sigma i /
        sourceAuxiliaryActualDeterminant event n epsilon sigma := by
  apply (eq_div_iff (source_auxiliary_actual_determinant_nonzero event n epsilon sigma positive regular)).mpr
  have entry := congrFun (source_auxiliary_actual_field_clear event n epsilon sigma positive regular) i
  change sourceAuxiliaryActualDeterminant event n epsilon sigma *
    sourceTemporalCorrectedField event epsilon sigma n i=_ at entry
  exact (mul_comm _ _).trans entry

def sourceAuxiliaryActualDriverNumerator (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : Fin 289 → ℂ :=
  emOriginalJacobi (frequencyRay epsilon 0 n)*ᵥ
    sourceAuxiliaryActualFieldNumerator event n epsilon sigma -
      sourceAuxiliaryActualDeterminant event n epsilon sigma • sourceTemporalEMForce

private theorem driver_factor {R I : Type*} [CommRing R] [Fintype I]
    (J : Matrix I I R) (e N F : I → R) (D d b : R)
    (field : N=b • F) (denominator : D=b*d) :
    J*ᵥN-D • e=b • (J*ᵥF-d • e) := by
  rw [field,denominator,Matrix.mulVec_smul,smul_sub,smul_smul]

theorem source_auxiliary_actual_driver_factor (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : sourceReducedClockDriverNumerator event n epsilon sigma=
      (sourceClockEval epsilon sigma (sourceAuxiliaryClockFactor event n))^72 •
        sourceAuxiliaryActualDriverNumerator event n epsilon sigma := by
  unfold sourceReducedClockDriverNumerator sourceAuxiliaryActualDriverNumerator
  exact driver_factor _ _ _ _ _ _ _
    (source_auxiliary_actual_field_factor event n epsilon sigma)
    (source_auxiliary_actual_determinant_factor event n epsilon sigma)

/-- The unchanged complete quantum/contact driver consumes the same
auxiliary cancellation as the actual field. -/

theorem source_auxiliary_actual_driver_clear (event : DressedEvent) (n : PhysicalMomentum)
    (e : scaleDomain) (sigma : ℝ) (positive : 0<sigma)
    (regular : correctedDet event e.val 0 sigma n≠0) :
    sourceAuxiliaryActualDeterminant event n e.val sigma •
      sourceTemporalActualQuantumDriver event e sigma n=
      sourceAuxiliaryActualDriverNumerator event n e.val sigma := by
  have original := source_reduced_clock_actual_driver_clear event n e sigma positive regular
  rw [source_auxiliary_actual_determinant_factor,source_auxiliary_actual_driver_factor] at original
  exact cancel_vector_factor _ _ _ _
    (pow_ne_zero _ (clock_factor_nonzero event n e.val sigma positive)) original

/-- The full source EM balance retains the original driver, ten background
terms and six lower terms; all use the same reduced denominator. -/

def sourceAuxiliaryReducedEMBalance (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : ℂ :=
  (dotProduct sourceTemporalEMForce (sourceAuxiliaryActualDriverNumerator event n epsilon sigma) -
    sourceEMNativeBackgroundRead (sourceAuxiliaryActualFieldNumerator event n epsilon sigma) -
      (epsilon : ℂ)^2 * sourceEMNativeLowerRead (frequencyRay 1 0 n)
        (sourceAuxiliaryActualFieldNumerator event n epsilon sigma)) /
    sourceAuxiliaryActualDeterminant event n epsilon sigma

private theorem scalar_balance (d a b c x A B C : ℂ) (nonzero : d≠0)
    (drive : d*a=A) (background : d*b=B) (lower : d*c=C) :
    (A-B-x*C)/d=a-b-x*c := by
  apply (div_eq_iff nonzero).mpr
  rw [←drive,←background,←lower]
  ring

theorem source_auxiliary_reduced_balance_actual (event : DressedEvent) (n : PhysicalMomentum)
    (e : scaleDomain) (sigma : ℝ) (positive : 0<sigma)
    (regular : correctedDet event e.val 0 sigma n≠0) :
    sourceAuxiliaryReducedEMBalance event n e.val sigma=
      dotProduct sourceTemporalEMForce (sourceTemporalActualQuantumDriver event e sigma n) -
        sourceEMNativeBackgroundRead (sourceTemporalCorrectedField event e.val sigma n) -
          (e.val : ℂ)^2 * sourceEMNativeLowerRead (frequencyRay 1 0 n)
            (sourceTemporalCorrectedField event e.val sigma n) := by
  have field := source_auxiliary_actual_field_clear event n e.val sigma positive regular
  have drive := congrArg (dotProduct sourceTemporalEMForce)
    (source_auxiliary_actual_driver_clear event n e sigma positive regular)
  simp only [dotProduct_smul,smul_eq_mul] at drive
  have background := congrArg sourceEMNativeBackgroundRead field
  simp only [sourceEMNativeBackgroundRead,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul] at background
  have lower := congrArg (sourceEMNativeLowerRead (frequencyRay 1 0 n)) field
  simp only [sourceEMNativeLowerRead,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul] at lower
  unfold sourceAuxiliaryReducedEMBalance
  exact scalar_balance _ _ _ _ _ _ _ _
    (source_auxiliary_actual_determinant_nonzero event n e.val sigma positive regular)
    drive background lower

/-- The original finite native equation consumes the reduced full balance;
no IR limit, unit-field or new photon/charge normalization is supplied. -/

theorem source_em_auxiliary_reduced_finite_return (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (positive : 0<sigma) (regular : correctedDet event e.val 0 sigma n≠0) :
    (e.val : ℂ)^4 * sourceN3TemporalEMCoefficient event e.val sigma n=
      noetherPairScale^2 / (2*(lapse : ℂ)) *
        ((3/4 : ℂ)+sourceAuxiliaryReducedEMBalance event n e.val sigma) := by
  rw [source_em_native_scaled_finite_return event e sigma n unit positive regular,
    source_auxiliary_reduced_balance_actual event n e sigma positive regular]
  congr 1
  ring

end LowEnergy.GaussComposite.ActualSourcePreparedAuxiliaryActualReturn
