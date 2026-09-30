import H0mework.Versions.X.NavierStokes.SourceAction.ReceiptProfile
import H0mework.Versions.X.NavierStokes.SourceAction.PolynomialObservations
import H0mework.Versions.X.NavierStokes.RecoveryAction.RecoveryJets

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeReceiptSpacetime

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeStressSource NativeFullOrderSynthesis NativeFullOrderFlux NativeFullOrderTime
open NativeTimeJetCarrier NativeMixedTimeSpace NativeSpacetimeControl NativeReceiptTimeProfile
open NativeTimeJetObservation NativeCorrectionPhysical NativeCorrectionTime

noncomputable section

variable {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}

def state (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (actual : ℝ) : ComplexVorticityHilbertState :=
  receipt.wholePath (projIcc (0 : ℝ) duration receipt.requestedTimePos.le actual)

def velocity (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (actual : ℝ) : ComplexVorticityHilbertState :=
  wholeBiotSavartVelocityState (state receipt actual)

theorem state_on_interval (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (time : Icc (0 : ℝ) duration) : state receipt time.1 = receipt.wholePath time := by
  unfold state
  rw [projIcc_of_mem receipt.requestedTimePos.le time.2]

variable {receipt : WholeContinuousMildSerrinReceipt nu initial duration}

def inverse (window : Window receipt) (actual : ℝ) : ℝ := (actual - window.first) / factor window

theorem inverse_mem (window : Window receipt) (actual : ℝ) (inside : actual ∈ Icc window.first window.last) :
    inverse window actual ∈ Icc (0 : ℝ) (run stackedShortCurrent 0).duration := by
  refine ⟨div_nonneg (sub_nonneg.mpr inside.1) (factor_pos window).le, ?_⟩
  apply (div_le_iff₀ (factor_pos window)).mpr
  rw [mul_comm, factor_duration]
  exact sub_le_sub_right inside.2 _

theorem parameter_inverse (window : Window receipt) (actual : ℝ) : parameter window (inverse window actual) = actual := by
  unfold parameter inverse
  rw [mul_div_cancel₀ _ (factor_pos window).ne']
  ring

theorem velocity_read (window : Window receipt) (actual : ℝ) (inside : actual ∈ Icc window.first window.last) :
    readProfile (jets window 0) (inverse window actual) = velocity receipt actual := by
  rw [show jets window 0 = base window from NativePolynomialTimeJets.jet_zero _ _ _,
    base_read window ⟨inverse window actual, inverse_mem window actual inside⟩]
  unfold velocity state
  congr 2
  apply Subtype.ext
  change parameter window (inverse window actual) = _
  rw [parameter_inverse, projIcc_of_mem receipt.requestedTimePos.le
    ⟨window.first_nonnegative.trans inside.1, inside.2.trans window.last_le⟩]

def timeJet (window : Window receipt) (order : ℕ) (actual : ℝ) : ComplexVorticityHilbertState :=
  (factor window)⁻¹ ^ order • readProfile (jets window order) (inverse window actual)

theorem timeJet_zero (window : Window receipt) (actual : ℝ) (inside : actual ∈ Icc window.first window.last) :
    timeJet window 0 actual = velocity receipt actual := by
  simp only [timeJet, pow_zero, one_smul, velocity_read window actual inside]

theorem timeJet_one_row (window : Window receipt) (actual : ℝ) (inside : actual ∈ Icc window.first window.last)
    (wave : IntegerWavevector) : timeJet window 1 actual wave = receiptMomentumAction receipt wave actual := by
  change (factor window)⁻¹ ^ 1 • readProfile (jets window 1) (inverse window actual) wave = _
  rw [pow_one, jet_one_row window ⟨inverse window actual, inverse_mem window actual inside⟩ wave,
    parameter_inverse, smul_smul, inv_mul_cancel₀ (factor_pos window).ne', one_smul]

theorem timeJet_evolves (window : Window receipt) (order : ℕ) (actual : ℝ) (inside : actual ∈ Icc window.first window.last) :
    HasDerivWithinAt (timeJet window order) (timeJet window (order + 1) actual) (Icc window.first window.last) actual := by
  have source := jets_evolve window order ⟨inverse window actual, inverse_mem window actual inside⟩
  have coordinate : HasDerivWithinAt (inverse window) (factor window)⁻¹ (Icc window.first window.last) actual := by
    convert! (((hasDerivAt_id actual).sub_const window.first).div_const (factor window)).hasDerivWithinAt using 1
    simp only [one_div]
  have scaled := (source.scomp actual coordinate (inverse_mem window)).const_smul ((factor window)⁻¹ ^ order)
  convert! scaled using 1
  simp only [timeJet, smul_smul, pow_succ]

theorem velocity_iteratedDerivWithin (window : Window receipt) (order : ℕ) (actual : ℝ)
    (inside : actual ∈ Icc window.first window.last) :
    iteratedDerivWithin order (velocity receipt) (Icc window.first window.last) actual = timeJet window order actual := by
  induction order generalizing actual with
  | zero => rw [iteratedDerivWithin_zero]; exact (timeJet_zero window actual inside).symm
  | succ order previous =>
      rw [iteratedDerivWithin_succ, derivWithin_congr (f := timeJet window order)
        (fun sample member => previous sample member) (previous actual inside)]
      exact (timeJet_evolves window order actual inside).derivWithin (uniqueDiffOn_Icc window.ordered actual inside)

theorem timeJet_moment_control (window : Window receipt) (order spatialOrder : ℕ) (actual : ℝ) :
    Summable (velocityMomentDensity spatialOrder (timeJet window order actual)) ∧
      (∑' wave, velocityMomentDensity spatialOrder (timeJet window order actual) wave) ≤
        ((factor window)⁻¹ ^ order) ^ 2 * (jets window order).budget spatialOrder := by
  let profile := scale ((factor window)⁻¹ ^ order) (jets window order)
  let time := projIcc (0 : ℝ) (run stackedShortCurrent 0).duration
    (run stackedShortCurrent 0).receipt.requestedTimePos.le (inverse window actual)
  exact ⟨profile.paid spatialOrder time, profile.bound spatialOrder time⟩

def vorticityFamily (window : Window receipt) : ℕ → Profile 0 := NativePolynomialObservations.curl (jets window)

def correctionFamily (window : Window receipt) (modes : Finset IntegerWavevector) : ℕ → Profile 0 :=
  NativePolynomialObservations.correction (jets window) modes

theorem state_zero (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (actual : ℝ) : state receipt actual 0 = 0 :=
  receipt.wholePath_zero_row _

theorem state_transverse (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (actual : ℝ) :
    WholeStateTransverse (state receipt actual) := wholePath_transverse receipt _

theorem vorticity_read (window : Window receipt) (actual : ℝ) (inside : actual ∈ Icc window.first window.last) :
    readProfile (vorticityFamily window 0) (inverse window actual) = state receipt actual := by
  apply lp.ext
  funext wave
  change fourierCurlCoefficient wave (readProfile (jets window 0) (inverse window actual) wave) = _
  rw [velocity_read window actual inside]
  change fourierCurlCoefficient wave (biotSavartVelocityCoefficient wave (state receipt actual wave)) = _
  by_cases nonzero : wave ≠ 0
  · exact fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse wave _ nonzero (state_transverse receipt actual wave)
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    rw [state_zero]
    simp [fourierCurlCoefficient]

theorem native_correction_action (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (modes : Finset IntegerWavevector) (actual : ℝ) (wave : IntegerWavevector) :
    nativeTurbulenceCorrectionAt modes (state receipt actual) wave =
      ThreeDimensionalVorticityCoefficientNativeFluidMedium.nativeFluidConstitutiveVorticityAction
        ((fun k => if k ∈ modes then quadraticFlux (velocity receipt actual) k else 0) -
          quadraticFlux (complexSharpSupportProjection modes (velocity receipt actual))) wave := by
  rw [← correctionStress_action modes _ (state_zero receipt actual) (state_transverse receipt actual) wave]
  have tensor : correctionStress modes (state receipt actual) =
      (fun k => if k ∈ modes then quadraticFlux (velocity receipt actual) k else 0) -
        quadraticFlux (complexSharpSupportProjection modes (velocity receipt actual)) := by
    funext k output input
    simp only [correctionStress, velocity_projection_commutes, velocity, Pi.sub_apply]
    split_ifs <;> rfl
  rw [tensor]

theorem correction_read (window : Window receipt) (modes : Finset IntegerWavevector) (actual : ℝ)
    (inside : actual ∈ Icc window.first window.last) :
    readProfile (correctionFamily window modes 0) (inverse window actual) = correctionState modes (state receipt actual) := by
  unfold correctionFamily
  apply lp.ext
  funext wave
  rw [NativePolynomialObservations.correction_zero_row (jets window) modes
      ⟨inverse window actual, inverse_mem window actual inside⟩,
    correctionState_apply modes _ (state_zero receipt actual), velocity_read window actual inside,
    native_correction_action receipt modes actual wave]

def field (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (pair : Spacetime) : PhysicalSpace :=
  spatialField (velocity receipt pair.1) pair.2

def vorticityField (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (pair : Spacetime) : PhysicalSpace :=
  spatialField (state receipt pair.1) pair.2

def correctionField (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (modes : Finset IntegerWavevector) (pair : Spacetime) : PhysicalSpace :=
  nativeTurbulenceCorrectionField modes (state receipt pair.1) pair.2

def slab (window : Window receipt) : Set Spacetime := Icc window.first window.last ×ˢ univ

def inverseSpacetime (window : Window receipt) (pair : Spacetime) : Spacetime := (inverse window pair.1, pair.2)

theorem observation_contDiffOn (window : Window receipt) (family : ℕ → Profile 0)
    (evolves : ∀ order (time : Time 0), HasDerivWithinAt (readProfile (family order))
      (readProfile (family (order + 1)) time.1) (Icc (0 : ℝ) (run stackedShortCurrent 0).duration) time.1)
    (observation : Spacetime → PhysicalSpace)
    (read : ∀ pair ∈ slab window, observation pair = jointField family (inverseSpacetime window pair)) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) observation (slab window) := by
  have coordinates : ContDiff ℝ (↑(⊤ : ℕ∞)) (inverseSpacetime window) :=
    ((contDiff_fst.sub contDiff_const).div_const (factor window)).prodMk contDiff_snd
  exact ((joint_contDiffOn family evolves).comp coordinates.contDiffOn
    (fun pair member => ⟨inverse_mem window pair.1 member.1, trivial⟩)).congr read

theorem field_contDiffOn (window : Window receipt) : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (field receipt) (slab window) := by
  apply observation_contDiffOn window (jets window) (jets_evolve window)
  intro pair member
  change spatialField (velocity receipt pair.1) pair.2 = spatialField (readProfile (jets window 0) (inverse window pair.1)) pair.2
  rw [velocity_read window pair.1 member.1]

theorem vorticityField_contDiffOn (window : Window receipt) : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (vorticityField receipt) (slab window) := by
  apply observation_contDiffOn window (vorticityFamily window)
    (NativePolynomialObservations.curl_evolves (jets window) (jets_evolve window))
  intro pair member
  change spatialField (state receipt pair.1) pair.2 = spatialField
    (readProfile (vorticityFamily window 0) (inverse window pair.1)) pair.2
  rw [vorticity_read window pair.1 member.1]

theorem correctionField_contDiffOn (window : Window receipt) (modes : Finset IntegerWavevector) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (correctionField receipt modes) (slab window) := by
  apply observation_contDiffOn window (correctionFamily window modes)
    (NativePolynomialObservations.correction_evolves (jets window) (jets_evolve window) modes)
  intro pair member
  rw [correctionField, ← correctionState_physical_eq_original]
  change spatialField _ pair.2 = spatialField (readProfile (correctionFamily window modes 0) (inverse window pair.1)) pair.2
  rw [correction_read window modes pair.1 member.1]

theorem slab_uniqueDiffOn (window : Window receipt) : UniqueDiffOn ℝ (slab window) :=
  (uniqueDiffOn_Icc window.ordered).prod uniqueDiffOn_univ

theorem field_frechet_Lp (window : Window receipt) (order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set Spacetime} (compact : IsCompact domain) (contained : domain ⊆ slab window) :
    ∃ budget : ℝ, 0 ≤ budget ∧
      MemLp (iteratedFDerivWithin ℝ order (field receipt) (slab window)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDerivWithin ℝ order (field receipt) (slab window)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal budget * volume domain ^ (1 / exponent.toReal) :=
  NativeRecoveryTimeJets.spacetime_frechet_Lp_of_smooth _ _ (field_contDiffOn window) (slab_uniqueDiffOn window) order exponent compact contained

theorem vorticityField_frechet_Lp (window : Window receipt) (order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set Spacetime} (compact : IsCompact domain) (contained : domain ⊆ slab window) :
    ∃ budget : ℝ, 0 ≤ budget ∧
      MemLp (iteratedFDerivWithin ℝ order (vorticityField receipt) (slab window)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDerivWithin ℝ order (vorticityField receipt) (slab window)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal budget * volume domain ^ (1 / exponent.toReal) :=
  NativeRecoveryTimeJets.spacetime_frechet_Lp_of_smooth _ _ (vorticityField_contDiffOn window) (slab_uniqueDiffOn window) order exponent compact contained

theorem correctionField_frechet_Lp (window : Window receipt) (modes : Finset IntegerWavevector)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain) (contained : domain ⊆ slab window) :
    ∃ budget : ℝ, 0 ≤ budget ∧
      MemLp (iteratedFDerivWithin ℝ order (correctionField receipt modes) (slab window)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDerivWithin ℝ order (correctionField receipt modes) (slab window)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal budget * volume domain ^ (1 / exponent.toReal) :=
  NativeRecoveryTimeJets.spacetime_frechet_Lp_of_smooth _ _ (correctionField_contDiffOn window modes) (slab_uniqueDiffOn window) order exponent compact contained

end
end SaturationMonoid.NavierStokes.NativeReceiptSpacetime
