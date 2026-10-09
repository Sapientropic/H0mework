import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFourierInverse
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationSourceSpectralInverse

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFrequencyInverse
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumJointFieldResponse
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPropagationPencil PreparationVacuumFieldPerturbation
open PreparationVacuumPhysicalCharacteristic
open SourcePropagationNoetherTime SourcePropagationResolvent SourcePropagationAlgebraicResponse
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualDressedSylvester ActualDressedHistoryKernel ActualDressedClockMoment ActualDressedFrequencyHalf
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
attribute [local irreducible] dressedEulerObserver planeNoetherInverse sourceInverse polynomialResolvent
  propagationPolynomial propagationNumerator rawInitial sourceMaterialMap sourceContactMap driveOperator

/-- The same original propagation polynomial generates both inverse denominators. -/
def planeResponseDenominator (q : PhysicalResponsePoint) (clock lambda : ℂ) : ℂ :=
  (propagationPolynomial q).eval lambda*(propagationPolynomial q).eval (lambda-clock)

def planeResponseNumerator (q : PhysicalResponsePoint) (reader force : Field289) (clock lambda : ℂ) : ResponseOp :=
  (propagationPolynomial q).eval (lambda-clock) •
      propagationNumerator q lambda (sourceMaterialMap q reader force)+
    (propagationPolynomial q).eval lambda •
      propagationNumerator q (lambda-clock) (sourceContactMap q reader force)+
    propagationNumerator q (lambda-clock)
      (driveOperator q force (propagationNumerator q lambda (rawInitial q reader)))

attribute [local irreducible] planeResponseDenominator planeResponseNumerator

theorem plane_response_denominator_nonzero (q : PhysicalResponsePoint) (clock lambda : ℂ)
    (positive : 0<lambda.re) (shifted : 0<(lambda-clock).re) :
    planeResponseDenominator q clock lambda≠0 := by
  unfold planeResponseDenominator
  exact mul_ne_zero (propagationPolynomial_offAxis q lambda (ne_of_gt positive))
    (propagationPolynomial_offAxis q (lambda-clock) (ne_of_gt shifted))

private theorem common_denominator {E : Type*} [AddCommGroup E] [Module ℂ E]
    (a b : ℂ) (x y z : E) (ha : a≠0) (hb : b≠0) :
    a⁻¹ • x+b⁻¹ • y+(b⁻¹*a⁻¹) • z=(a*b)⁻¹ • (b • x+a • y+z) := by
  rw [smul_add,smul_add,smul_smul,smul_smul,mul_inv_rev]
  have left : (b⁻¹*a⁻¹)*b=a⁻¹ := by field_simp
  have right : (b⁻¹*a⁻¹)*a=b⁻¹ := by field_simp
  rw [left,right]

private theorem rational_operator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U V D : E→L[ℂ] E) (a b : ℂ) (M C A : E) (ha : a≠0) (hb : b≠0) :
    (a⁻¹ • U) M+(b⁻¹ • V) (C+D ((a⁻¹ • U) A))=
      (a*b)⁻¹ • (b • U M+a • V C+V (D (U A))) := by
  simpa only [smul_apply,map_add,map_smul,smul_add,smul_smul,add_assoc,mul_comm] using!
    common_denominator (E:=E) a b (U M) (V C) (V (D (U A))) ha hb

/-- Numerator and denominator are generated from the original joint evolution, with both contact and preparation retained. -/
theorem plane_noether_inverse_rational (q : PhysicalResponsePoint) (reader force : Field289)
    (clock lambda : ℂ) (positive : 0<lambda.re) (shifted : 0<(lambda-clock).re) :
    planeNoetherInverse q reader force clock lambda=
      (planeResponseDenominator q clock lambda)⁻¹ • planeResponseNumerator q reader force clock lambda := by
  have left := (polynomialResolvent_future q lambda positive).symm
  have right := (polynomialResolvent_future q (lambda-clock) shifted).symm
  have actual : planeNoetherInverse q reader force clock lambda=
      polynomialResolvent q lambda (sourceMaterialMap q reader force)+
        polynomialResolvent q (lambda-clock) (sourceContactMap q reader force+
          driveOperator q force (polynomialResolvent q lambda (rawInitial q reader))) := by
    unfold planeNoetherInverse
    exact congrArg₂
      (fun A B : SourcePropagationResolvent.TransferOp=>A (sourceMaterialMap q reader force)+
        B (sourceContactMap q reader force+driveOperator q force (A (rawInitial q reader)))) left right
  have ha := propagationPolynomial_offAxis q lambda (ne_of_gt positive)
  have hb := propagationPolynomial_offAxis q (lambda-clock) (ne_of_gt shifted)
  have rational : polynomialResolvent q lambda (sourceMaterialMap q reader force)+
        polynomialResolvent q (lambda-clock) (sourceContactMap q reader force+
          driveOperator q force (polynomialResolvent q lambda (rawInitial q reader)))=
      (planeResponseDenominator q clock lambda)⁻¹ • planeResponseNumerator q reader force clock lambda := by
    unfold polynomialResolvent planeResponseDenominator planeResponseNumerator
    exact rational_operator (propagationNumerator q lambda) (propagationNumerator q (lambda-clock))
      (driveOperator q force) ((propagationPolynomial q).eval lambda) ((propagationPolynomial q).eval (lambda-clock))
      (sourceMaterialMap q reader force) (sourceContactMap q reader force) (rawInitial q reader) ha hb
  exact actual.trans rational

def dressedFrequencyNumerator (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (i j : Fin 289) : ℂ :=
  dressedEulerObserver event (planeResponseNumerator (dressedKinematicPoint event transfer)
    (fieldUnit i) (fieldUnit j) (p 0) lambda)

attribute [local irreducible] dressedFrequencyNumerator

theorem dressed_frequency_polarization_rational (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (off : sourceClockGrowth p<lambda.re) (i j : Fin 289) :
    frequencyHalfPolarization event transfer p lambda i j=
      dressedFrequencyNumerator event transfer p lambda i j/
        planeResponseDenominator (dressedKinematicPoint event transfer) (p 0) lambda := by
  have positive : 0<lambda.re := (le_max_left 0 (p 0).re).trans_lt off
  have inputOff : (p 0).re<lambda.re := (le_max_right 0 (p 0).re).trans_lt off
  have shifted : 0<(lambda-p 0).re := by simpa only [Complex.sub_re] using sub_pos.mpr inputOff
  have inverse:=plane_noether_inverse_rational (dressedKinematicPoint event transfer)
    (fieldUnit i) (fieldUnit j) (p 0) lambda positive shifted
  have observed:=congrArg (dressedEulerObserver event) inverse
  have rational : dressedEulerObserver event (planeNoetherInverse (dressedKinematicPoint event transfer)
      (fieldUnit i) (fieldUnit j) (p 0) lambda)=
      dressedFrequencyNumerator event transfer p lambda i j/
        planeResponseDenominator (dressedKinematicPoint event transfer) (p 0) lambda := by
    simpa only [dressedFrequencyNumerator,map_smul,smul_eq_mul,div_eq_mul_inv,mul_comm] using! observed
  exact (dressed_frequency_half_inverse event transfer p lambda off i j).trans rational

/-- The complete original action response now has a source polynomial expression for every quantum entry. -/
theorem dressed_frequency_response_rational (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (off : sourceClockGrowth p<lambda.re) (i j : Fin 289) :
    frequencyResponsePencil event transfer p lambda i j=
      ActualEMAction.emOriginalJacobi p i j-(lambda-p 0)*
        (dressedFrequencyNumerator event transfer p lambda i j/
          planeResponseDenominator (dressedKinematicPoint event transfer) (p 0) lambda) := by
  have inputOff : (p 0).re<lambda.re := (le_max_right 0 (p 0).re).trans_lt off
  unfold frequencyResponsePencil frequencyQuantumCorrection
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,frequency_input_normalizer_generated p lambda inputOff]
  exact congrArg (fun z : ℂ=>ActualEMAction.emOriginalJacobi p i j-(lambda-p 0)*z)
    (dressed_frequency_polarization_rational event transfer p lambda off i j)

/-- Static input retains the square of the same full joint source denominator. -/
theorem plane_static_denominator (q : PhysicalResponsePoint) (lambda : ℂ) :
    planeResponseDenominator q 0 lambda=((propagationPolynomial q).eval lambda)^2 := by
  unfold planeResponseDenominator
  rw [sub_zero,pow_two]

/-- Zero transfer is an actual source pole; the observed numerator must pay its own cancellation. -/
theorem actual_zero_transfer_denominator (event : DressedEvent) :
    planeResponseDenominator (dressedKinematicPoint event 0) 0 0=0 := by
  have pole:=SourcePropagationConstrainedPoleReturn.zero_transfer_sourcePole
    (dressedKinematicPoint event 0) (by simp only [dressedKinematicPoint,neg_zero])
  change (propagationPolynomial (dressedKinematicPoint event 0)).eval 0=0 at pole
  rw [plane_static_denominator,pole,zero_pow (by decide : 2≠0)]

end LowEnergy.GaussComposite.ActualDressedFrequencyInverse
