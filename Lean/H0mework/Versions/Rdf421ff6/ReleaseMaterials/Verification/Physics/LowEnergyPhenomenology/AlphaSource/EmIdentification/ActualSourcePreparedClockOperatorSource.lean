import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedPhotonFiniteMoments
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparationWardResidual

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedClockOperatorSource
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSylvester ActualDressedUniformMaterialCoefficients
open ActualDressedZeroClockFrequency ActualDressedEMQuantumThreshold
open ActualDressedPreparationEnergy ActualDressedTemporalResidual
open ActualSourcePreparedPhotonPoleRead ActualSourcePreparedProjectedClock
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalCharacteristic PreparationPhysicalNativePhotonFluxReturn
open Polynomial
open scoped TensorProduct BigOperators Matrix

/-- The complete original numerator before its prepared observer is applied. -/
def sourceClockNoetherOperator (event : DressedEvent) (n : PhysicalMomentum)
    (i j : Fin 289) : ParameterOp :=
  (commonClockPolynomial event n).eval (MvPolynomial.X 1) •
      commonClockAction event n irClock (materialFullNumerator event n (fieldUnit i) (fieldUnit j)) +
    (commonClockPolynomial event n).eval irClock •
      commonClockAction event n (MvPolynomial.X 1) (materialContactNumerator event n (fieldUnit i) (fieldUnit j)) +
    commonClockAction event n (MvPolynomial.X 1)
      (commonDrive event n (fieldUnit j)
        (commonClockAction event n irClock (materialRawNumerator event n (fieldUnit i))))

theorem source_clock_noether_original (event : DressedEvent) (n : PhysicalMomentum) (i j : Fin 289) :
    coefficientObserver (dressedEulerObserver event).toLinearMap (sourceClockNoetherOperator event n i j) =
      commonNumerator event n i j := rfl

def sourceProjectedClockOperator (event : DressedEvent) (epsilon : ℝ) (n : PhysicalMomentum)
    (branch : Fin 2) (sheet : ℝ) : ParameterOp :=
  ∑i, ∑j, (sourcePhotonLeftReaderCLM branch epsilon sheet n (Pi.single i 1) *
    sourceNativeFrequencyPolarization branch epsilon sheet n j) • sourceClockNoetherOperator event n i j

def sourceStaticClockEvaluation (epsilon : ℝ) : Parameters →ₐ[ℂ] ℂ[X] :=
  MvPolynomial.aeval (fun i : Fin 3 => if i=0 then C (epsilon : ℂ) else if i=1 then X else C 0)

theorem source_static_clock_evaluation (epsilon : ℝ) (P : Parameters) :
    sourceStaticClockEvaluation epsilon P =
      ActualDressedOrderedStatic.clockSpecialize 0 (frequencyClockSlice epsilon P) := by
  rw [frequency_clock_specialize]
  rfl

def sourceClockCoefficient (epsilon : ℝ) (r : ℕ) : Parameters →ₗ[ℂ] ℂ where
  toFun := fun P => (X * sourceStaticClockEvaluation epsilon P).coeff r
  map_add' := by intro P Q; simp only [map_add, mul_add, coeff_add]
  map_smul' := by
    intro c P
    simp only [map_smul, mul_smul_comm, coeff_smul, RingHom.id_apply]

private theorem clock_coefficient_apply (epsilon : ℝ) (r : ℕ) (P : Parameters) :
    sourceClockCoefficient epsilon r P = (X * sourceStaticClockEvaluation epsilon P).coeff r := rfl

def sourceClockWordRead (epsilon : ℝ) (r : ℕ) : ParameterOp →ₗ[ℂ] Op :=
  (TensorProduct.lid ℂ Op).toLinearMap.comp
    (TensorProduct.map (sourceClockCoefficient epsilon r) (LinearMap.id : Op →ₗ[ℂ] Op))

theorem source_clock_observer_word (epsilon : ℝ) (r : ℕ) (observer : Op →ₗ[ℂ] ℂ) (B : ParameterOp) :
    sourceClockCoefficient epsilon r (coefficientObserver observer B) =
      observer (sourceClockWordRead epsilon r B) := by
  induction B using TensorProduct.induction_on with
  | zero => simp
  | tmul P A => simp [sourceClockWordRead, coefficientObserver, mul_comm]
  | add B C hB hC => simp only [map_add, hB, hC]

def sourceProjectedClockWord (event : DressedEvent) (epsilon : ℝ) (n : PhysicalMomentum)
    (branch : Fin 2) (sheet : ℝ) (r : ℕ) : Op :=
  sourceClockWordRead epsilon r (sourceProjectedClockOperator event epsilon n branch sheet)

/-- Every actual scalar coefficient is a read of this same full operator word. -/
theorem source_projected_clock_coefficient (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) (r : ℕ) :
    (sourceProjectedClockNumerator event epsilon n branch sheet).coeff r =
      dressedEulerObserver event (sourceProjectedClockWord event epsilon n branch sheet r) := by
  change _ = (dressedEulerObserver event).toLinearMap
    (sourceClockWordRead epsilon r (sourceProjectedClockOperator event epsilon n branch sheet))
  rw [← source_clock_observer_word]
  unfold sourceProjectedClockOperator sourceProjectedClockNumerator
  simp only [map_sum, map_smul, smul_eq_mul, source_clock_noether_original]
  simp only [clock_coefficient_apply, source_static_clock_evaluation, finsetSum_coeff, coeff_C_mul, coeff_mul_C,
    fullClockQuantumNumerator, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem source_projected_clock_coefficient_price (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) (r : ℕ) :
    ‖(sourceProjectedClockNumerator event epsilon n branch sheet).coeff r‖ ≤
      2 * ‖sourceProjectedClockWord event epsilon n branch sheet r‖ := by
  rw [source_projected_clock_coefficient]
  exact ((dressedEulerObserver event).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (ActualDressedSignal.dressed_euler_observer_price event) (norm_nonneg _))

/-- Preparation points differ, while the original operator numerator is one computed carrier. -/
theorem source_clock_operator_preparation (event : DressedEvent) (k : ℕ) (epsilon : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) :
    sourceProjectedClockOperator (preparationEventSequence event k) epsilon n branch sheet =
      sourceProjectedClockOperator event epsilon n branch sheet := rfl

theorem source_clock_word_preparation (event : DressedEvent) (k : ℕ) (epsilon : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) (r : ℕ) :
    sourceProjectedClockWord (preparationEventSequence event k) epsilon n branch sheet r =
      sourceProjectedClockWord event epsilon n branch sheet r := rfl

theorem source_clock_clearing_preparation (event : DressedEvent) (k : ℕ) (epsilon : ℝ)
    (n : PhysicalMomentum) :
    sourceStaticClockClearing (preparationEventSequence event k) epsilon n =
      sourceStaticClockClearing event epsilon n := rfl

theorem source_clock_order_preparation (event : DressedEvent) (k : ℕ) (epsilon : ℝ)
    (n : PhysicalMomentum) :
    sourceStaticClockOrder (preparationEventSequence event k) epsilon n =
      sourceStaticClockOrder event epsilon n := rfl

end LowEnergy.GaussComposite.ActualSourcePreparedClockOperatorSource
