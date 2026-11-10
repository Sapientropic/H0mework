import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.FullQuantumSourceWindowError

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualMixedNoetherTimePriceOwn
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumGaugeSourceInjection PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumNoetherChart PreparationVacuumRawJointFeedback
open PreparationVacuumNoetherOrdinaryWard PreparationVacuumNoetherResponsePrice
open GaussComposite.ActualDressedFullCoulomb GaussComposite.ActualDressedNoether GaussComposite.ActualDressedSylvester
open ActualSourceMixed289ResponseOwn GaussCoreHilbert
open Set MeasureTheory Filter
open scoped Topology BigOperators Matrix
attribute [local irreducible] physicalTime jointResolvent noetherReaderContact rawReaderContact dressedStaticPolarization

-- The original corrected-minus-raw contact retains both full physical times and both uncut joint resolvents.
private theorem original_corrected_contact_value (q : PhysicalResponsePoint) (reader force : Field289) (age : ℝ) :
    (correctedContactJet q reader force age).value =
      (physicalTime (q.p+q.k) q.F (-age) 0 * jointResolvent (q.p+q.k) q.F q.z 0 *
        (noetherReaderContact reader force q.p q.F - rawReaderContact reader force q.p q.F) *
          jointResolvent q.p q.F q.w 0) * physicalTime q.p q.F age 0 := by
  simp only [correctedContactJet, jetMul, jetConst, physicalTimeJet, timeJet, physicalTime,
    neg_one_mul, one_mul, add_zero]

theorem original_corrected_contact_time_source_price (q : PhysicalResponsePoint) (reader force : Field289)
    (age : ℝ) (leftNonreal : q.z.im ≠ 0) (rightNonreal : q.w.im ≠ 0) :
    ‖(correctedContactJet q reader force age).value‖ ≤
      originalPhysicalTimePrice (q.p+q.k) q.F (-age) * originalJointResolventPrice (q.p+q.k) q.F q.z *
        originalNoetherRawIncrementPrice reader force q.p q.F * originalJointResolventPrice q.p q.F q.w *
          originalPhysicalTimePrice q.p q.F age := by
  have price := PreparationVacuumFullFieldRiesz.triple_price _ _ _ _ _ _
      (PreparationVacuumFullFieldRiesz.triple_price _ _ _ _ _ _
        (originalPhysicalTime_price (q.p+q.k) q.F (-age))
        (originalJointResolvent_price (q.p+q.k) q.F q.z leftNonreal)
        (originalNoetherRawIncrement_price reader force q.p q.F))
      (originalJointResolvent_price q.p q.F q.w rightNonreal)
      (originalPhysicalTime_price q.p q.F age)
  exact (congrArg norm (original_corrected_contact_value q reader force age)).le.trans price

def originalQuantumHorizon (sigma : ℝ) (bits : ℕ) : ℝ := 2 * Real.log 2 * (bits : ℝ) / sigma

theorem originalQuantumHorizon_nonnegative (sigma : ℝ) (positive : 0 < sigma) (bits : ℕ) :
    0 ≤ originalQuantumHorizon sigma bits := by
  have log0 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  unfold originalQuantumHorizon
  positivity

theorem originalQuantumHorizon_binary_decay (sigma : ℝ) (positive : 0 < sigma) (bits : ℕ) :
    Real.exp (-(sigma * originalQuantumHorizon sigma bits / 2)) = (1 / 2 : ℝ)^bits := by
  have exponent : -(sigma * originalQuantumHorizon sigma bits / 2) = (bits : ℝ) * (-Real.log 2) := by
    unfold originalQuantumHorizon
    field_simp [positive.ne']
  rw [exponent, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  norm_num

def originalQuantumBinaryWindow (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ) (bits : ℕ) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  originalFullQuantumWindow event transfer lambda (originalQuantumHorizon lambda.re bits)

theorem actualFullQuantum_binary_source_error (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) (small : lambda.re ≤ 2) (bits : ℕ) (i j : Fin 289) :
    ‖dressedStaticPolarization event transfer lambda i j - originalQuantumBinaryWindow event transfer lambda bits i j‖ ≤
      (896 * sourceCompleteCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j) / lambda.re^4) * (1 / 2 : ℝ)^bits := by
  have source := actualFullQuantum_window_source_error event transfer lambda positive small
    (originalQuantumHorizon lambda.re bits) (originalQuantumHorizon_nonnegative lambda.re positive bits) i j
  rw [originalQuantumHorizon_binary_decay lambda.re positive bits] at source
  exact source

theorem actualFullQuantum_binary_complex_enclosure (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) (small : lambda.re ≤ 2) (bits : ℕ) (i j : Fin 289) :
    |(dressedStaticPolarization event transfer lambda i j).re - (originalQuantumBinaryWindow event transfer lambda bits i j).re| ≤
      (896 * sourceCompleteCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j) / lambda.re^4) * (1 / 2 : ℝ)^bits ∧
    |(dressedStaticPolarization event transfer lambda i j).im - (originalQuantumBinaryWindow event transfer lambda bits i j).im| ≤
      (896 * sourceCompleteCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j) / lambda.re^4) * (1 / 2 : ℝ)^bits := by
  have source := actualFullQuantum_binary_source_error event transfer lambda positive small bits i j
  constructor
  · exact (Complex.abs_re_le_norm _).trans source
  · exact (Complex.abs_im_le_norm _).trans source

end LowEnergy.ActualMixedNoetherTimePriceOwn
