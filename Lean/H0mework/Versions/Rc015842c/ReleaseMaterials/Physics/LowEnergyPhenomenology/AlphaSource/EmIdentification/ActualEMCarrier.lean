import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMFieldCurrent
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativePolarizationFlux
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhaseGaugeField

set_option autoImplicit false
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCarrierOwn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction
open StageNineHolonomicField StageNineP286GaugeAuxiliaryVariation
open Stage10 SourceQuantumScalarOrbitDimensions
open PhysicalEMGaugeRealization PhysicalEMFieldCurrent
open PreparationCoordinates PreparationVacuumGaugeSourceInjection
open PreparationPhysicalNativePhotonFluxReturn PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet PreparationVacuumOriginalGreenFeedback
open CanonicalGradedSpatialSource
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator

/-- The original EM direction inserted into all four source gauge slots. -/
def emInsertion : Matrix (Fin 289) (Fin 4) ℂ :=
  fun j mu => (emGaugeField mu j : ℂ)

/-- The complete field response is retained before taking its EM read. -/
def emPropagatingCarrier (epsilon s : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 4) ℂ :=
  sourceWholePhotonResidue epsilon s n * emInsertion

def emPropagator (epsilon s : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  emInsertion.transpose * sourceWholePhotonGreen epsilon s n * emInsertion

def emPoleTensor (epsilon s : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  emInsertion.transpose * sourceWholePhotonResidue epsilon s n * emInsertion

/-- The actual four-current tensor is the pole of the complete original Green tensor. -/
theorem em_pole_generated (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach, Tendsto
      (fun s : ℝ => ((s-sourceSheet branch n unit e.val:ℝ):ℂ) • emPropagator e.val s n)
      (𝓝[≠] (sourceSheet branch n unit e.val))
      (𝓝 (emPoleTensor e.val (sourceSheet branch n unit e.val) n)) := by
  filter_upwards [sourceWholePhotonGreen_residue branch n unit] with e pole
  have cont : Continuous (fun R : Matrix (Fin 289) (Fin 289) ℂ =>
      emInsertion.transpose * R * emInsertion) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have result := (cont.tendsto _).comp pole
  simpa only [emPropagator, emPoleTensor, Function.comp_def, Matrix.mul_smul, Matrix.smul_mul] using result

/-- All289 output rows obey the same original Jacobi equation on the pole. -/
theorem em_carrier_homogeneous (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      originalJacobi (frequencyRay e.val (sourceSheet branch n unit e.val) n) *
        emPropagatingCarrier e.val (sourceSheet branch n unit e.val) n = 0 := by
  filter_upwards [sourceWholePhotonResidue_homogeneous branch n unit] with e homogeneous
  rw [emPropagatingCarrier, ←Matrix.mul_assoc, homogeneous.2, Matrix.zero_mul]

/-- Residue normalization keeps the complete Jacobi jet and the complete mixed carrier. -/
theorem em_flux_generated (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      emInsertion.transpose * sourceWholePhotonResidue e.val (sourceSheet branch n unit e.val) n *
        sourcePhotonSheetJacobiJet e.val (sourceSheet branch n unit e.val) n *
        emPropagatingCarrier e.val (sourceSheet branch n unit e.val) n =
      emPoleTensor e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourceWholePhotonResidue_sheetFlux branch n unit] with e flux
  simp only [emPropagatingCarrier, emPoleTensor]
  calc
    _ = emInsertion.transpose *
        (sourceWholePhotonResidue e.val (sourceSheet branch n unit e.val) n *
          sourcePhotonSheetJacobiJet e.val (sourceSheet branch n unit e.val) n *
          sourceWholePhotonResidue e.val (sourceSheet branch n unit e.val) n) * emInsertion := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [flux]


/-- The source's actual background derivative of the literal EM direction. -/
def emBackgroundDerivative (point : BasePoint) (mu : Fin 4) : P286LieBlockData :=
  p286LieBracket (actual.gaugeConnection point mu) emDirection

private theorem color_hypercharge (i : Fin 3) :
    p286LieBracket (sourceColorP286Generator i) HyperchargeResponse.chargeDirection = 0 := by
  apply Prod.ext
  · apply Subtype.ext
    simp [p286LieBracket, HyperchargeResponse.chargeDirection, suLieBracket]
  · apply Prod.ext
    · apply Subtype.ext
      simp [p286LieBracket, HyperchargeResponse.chargeDirection, suLieBracket]
    · simp [p286LieBracket]

/-- All four original background commutators are computed, retaining both transverse colour rows. -/
theorem em_actual_background_derivative (point : BasePoint) :
    emBackgroundDerivative point =
      ![0, -gaugeScale • sourceColorP286Generator 1,
        gaugeScale • sourceColorP286Generator 0, 0] := by
  have split : emDirection = (-1:ℝ) • sourceColorP286Generator 2 +
      (-1/2:ℝ) • HyperchargeResponse.chargeDirection := by
    unfold emDirection
    module
  have color (i : Fin 3) : p286LieBracket (gaugeScale • sourceColorP286Generator i) emDirection =
      -gaugeScale • p286LieBracket (sourceColorP286Generator i) (sourceColorP286Generator 2) := by
    rw [split, p286LieBracket_smul_left, p286LieBracket_add_right,
      p286LieBracket_smul_right, p286LieBracket_smul_right, color_hypercharge,
      smul_zero, add_zero, smul_smul]
    module
  funext mu
  fin_cases mu
  · change p286LieBracket 0 emDirection = 0
    simp [p286LieBracket, suLieBracket]
  · change p286LieBracket (gaugeScale • sourceColorP286Generator 0) emDirection =
      -gaugeScale • sourceColorP286Generator 1
    rw [color, sourceColorP286Generator_bracket]
    rfl
  · change p286LieBracket (gaugeScale • sourceColorP286Generator 1) emDirection =
      gaugeScale • sourceColorP286Generator 0
    rw [color, sourceColorP286Generator_bracket]
    simp
  · change p286LieBracket (gaugeScale • sourceColorP286Generator 2) emDirection = 0
    rw [color, sourceColorP286Generator_bracket]
    simp

open PreparationVacuumElectromagneticIdentity Electromagnetic.CanonicalCoframe
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalActualPhaseChargeReturn
open PreparationVacuumPhysicalQuantumLockedCharge

/-- The full actual rest-pair force, propagated before reading the EM components. -/
def emElectronCarrier (epsilon s : ℝ) (n : PhysicalMomentum)
    (point : BasePoint) (left right : RestStateIndex) : Fin 289 → ℂ :=
  sourceWholePhotonResidue epsilon s n *ᵥ actualRestNativeComplexForcingCovector point left right

/-- The original source couples to precisely the EM current already generated by the original action. -/
theorem em_source_current (point : BasePoint) (left right : RestStateIndex) (mu : Fin 4) :
    (emInsertion.transpose *ᵥ actualRestNativeComplexForcingCovector point left right) mu =
      emForcingRead point left right mu := by
  simp only [emInsertion, Matrix.mulVec, dotProduct, Matrix.transpose_apply, emGaugeField,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [gaugeField, Pi.single_apply, apply_ite, Complex.ofReal_one,
    Complex.ofReal_zero, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Both charged and neutral rest edges retain their generated charge at the input of the full propagator. -/
theorem em_electron_source_unit (side edge : Fin 2) :
    (emInsertion.transpose *ᵥ actualRestNativeComplexForcingCovector 0
      (sourceChargedRestIndex side edge) (sourceChargedRestIndex side edge)) 0 =
      (ActionNormalization.phaseMomentum : ℂ) * (sourceActualPhaseCharge edge : ℂ) := by
  rw [em_source_current]
  exact em_forcing_temporal_unit side edge

/-- The actual complete force yields a homogeneous whole-field mode on each generated pole. -/
theorem em_electron_homogeneous (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (point : BasePoint) (left right : RestStateIndex) :
    ∀ᶠ e in scaleApproach,
      originalJacobi (frequencyRay e.val (sourceSheet branch n unit e.val) n) *ᵥ
        emElectronCarrier e.val (sourceSheet branch n unit e.val) n point left right = 0 := by
  filter_upwards [sourceWholePhotonResidue_homogeneous branch n unit] with e homogeneous
  rw [emElectronCarrier, Matrix.mulVec_mulVec, homogeneous.2, Matrix.zero_mulVec]

/-- Constraint sources are removed by the original null projector, never by selecting an EM axis. -/
theorem em_electron_constraint_return (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (point : BasePoint) (left right : RestStateIndex) :
    ∀ᶠ e in scaleApproach, ∀ᶠ s in 𝓝[≠] (sourceSheet branch n unit e.val),
      originalJacobi (frequencyRay e.val s n) *ᵥ
        (sourceWholePhotonGreen e.val s n *ᵥ actualRestNativeComplexForcingCovector point left right) =
      actualRestNativeComplexForcingCovector point left right -
        sourcePhotonNullSource e.val s n *ᵥ actualRestNativeComplexForcingCovector point left right := by
  filter_upwards [sourceWholePhotonGreen_equations branch n unit] with e equations
  filter_upwards [equations] with s equation
  rw [Matrix.mulVec_mulVec, equation.1, Matrix.sub_mulVec, Matrix.one_mulVec]

/-- Actual current-coupled residue normalization with all mixed field rows retained. -/
theorem em_electron_residue_flux (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (point : BasePoint) (left right : RestStateIndex) :
    ∀ᶠ e in scaleApproach,
      sourceWholePhotonResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
        (sourcePhotonSheetJacobiJet e.val (sourceSheet branch n unit e.val) n *ᵥ
          emElectronCarrier e.val (sourceSheet branch n unit e.val) n point left right) =
      emElectronCarrier e.val (sourceSheet branch n unit e.val) n point left right := by
  filter_upwards [sourceWholePhotonResidue_sheetFlux branch n unit] with e flux
  simp only [emElectronCarrier, Matrix.mulVec_mulVec, ←Matrix.mul_assoc, flux]

/-- The actual electron force is nonzero before propagation, from its source-generated unit current. -/
theorem em_electron_source_nonzero (side : Fin 2) :
    actualRestNativeComplexForcingCovector 0 (sourceChargedRestIndex side 0)
      (sourceChargedRestIndex side 0) ≠ 0 := by
  intro vanish
  have charge := em_electron_source_unit side 0
  rw [vanish, Matrix.mulVec_zero] at charge
  have positive := ActionNormalization.phaseMomentum_positive
  have nonzero : (ActionNormalization.phaseMomentum : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr positive.ne'
  apply nonzero
  simpa [sourceActualPhaseCharge] using charge.symm

/-- The complete current-coupled vector is the residue of its own actual full Green response. -/
theorem em_electron_pole_generated (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (point : BasePoint) (left right : RestStateIndex) :
    ∀ᶠ e in scaleApproach, Tendsto
      (fun s : ℝ => ((s-sourceSheet branch n unit e.val:ℝ):ℂ) •
        (sourceWholePhotonGreen e.val s n *ᵥ actualRestNativeComplexForcingCovector point left right))
      (𝓝[≠] (sourceSheet branch n unit e.val))
      (𝓝 (emElectronCarrier e.val (sourceSheet branch n unit e.val) n point left right)) := by
  filter_upwards [sourceWholePhotonGreen_residue branch n unit] with e pole
  have cont : Continuous (fun R : Matrix (Fin 289) (Fin 289) ℂ =>
      R *ᵥ actualRestNativeComplexForcingCovector point left right) :=
    continuous_id.matrix_mulVec continuous_const
  simpa only [Function.comp_def, emElectronCarrier, Matrix.smul_mulVec] using
    (cont.tendsto _).comp pole

/-- This is the original physical-frequency residue, with the source scale factor paid once. -/
def emElectronFrequencyCarrier (epsilon s : ℝ) (n : PhysicalMomentum)
    (point : BasePoint) (left right : RestStateIndex) : Fin 289 → ℂ :=
  sourceWholePhotonFrequencyResidue epsilon s n *ᵥ actualRestNativeComplexForcingCovector point left right

theorem em_electron_physical_frequency_flux (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (point : BasePoint) (left right : RestStateIndex) :
    ∀ᶠ e in scaleApproach,
      sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
        (sourcePhotonFrequencyJacobiJet e.val (sourceFrequency e.val (sourceSheet branch n unit e.val)) n *ᵥ
          emElectronFrequencyCarrier e.val (sourceSheet branch n unit e.val) n point left right) =
      emElectronFrequencyCarrier e.val (sourceSheet branch n unit e.val) n point left right := by
  filter_upwards [sourceWholePhotonResidue_frequencyFlux branch n unit] with e flux
  simp only [emElectronFrequencyCarrier, Matrix.mulVec_mulVec, ←Matrix.mul_assoc, flux]

/-- The fixed EM direction has an actual nonzero background derivative, so its two computed mixed rows must be retained. -/
theorem em_actual_background_derivative_nonzero (point : BasePoint) :
    emBackgroundDerivative point ≠ 0 := by
  intro vanish
  have row := congrFun vanish 1
  rw [em_actual_background_derivative] at row
  change -gaugeScale • sourceColorP286Generator 1 = 0 at row
  have color : sourceColorP286Generator 1 = 0 :=
    (smul_eq_zero.mp row).resolve_left (neg_ne_zero.mpr gaugeScale_pos.ne')
  have norm := sourceColorP286Generator_pairing_self 1
  rw [color] at norm
  norm_num [p286LiePairing, specialUnitaryLiePairing, hyperchargeLiePairing] at norm


open PreparationPhysicalNativePolarizationEmitter

/-- The pole amplitude is read from the complete original rest-pair force. -/
def emElectronPoleAmplitude (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (point : BasePoint) (left right : RestStateIndex) : ℂ :=
  sourcePhotonLeftReader branch epsilon s n (actualRestNativeComplexForcingCovector point left right)

/-- The actual force selects the source-generated polarization; no direction or residue is supplied. -/
theorem em_electron_native_factor (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (point : BasePoint) (left right : RestStateIndex) :
    ∀ᶠ e in scaleApproach,
      emElectronCarrier e.val (sourceSheet branch n unit e.val) n point left right =
        emElectronPoleAmplitude branch e.val (sourceSheet branch n unit e.val) n point left right •
          sourceNativePolarization branch e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourceWholePhotonResidue_factor branch n unit] with e factor
  exact factor _

/-- The actual mixed carrier lies in the original active field image and obeys the original full null-field constraint. -/
theorem em_electron_null_constraint (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (point : BasePoint) (left right : RestStateIndex) :
    ∀ᶠ e in scaleApproach,
      sourcePhotonNullField e.val (sourceSheet branch n unit e.val) n *ᵥ
        emElectronCarrier e.val (sourceSheet branch n unit e.val) n point left right = 0 := by
  filter_upwards [em_electron_native_factor branch n unit point left right] with e factor
  rw [factor, Matrix.mulVec_smul, sourceNativePolarization_null, smul_zero]

/-- Visibility is now exactly one original current/cofactor value, rather than an external polarization premise. -/
theorem em_electron_visibility_iff (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (point : BasePoint) (left right : RestStateIndex) :
    ∀ᶠ e in scaleApproach,
      emElectronCarrier e.val (sourceSheet branch n unit e.val) n point left right ≠ 0 ↔
        emElectronPoleAmplitude branch e.val (sourceSheet branch n unit e.val) n point left right ≠ 0 := by
  filter_upwards [em_electron_native_factor branch n unit point left right,
    sourceNativePolarization_generated branch n unit] with e factor polarization
  rw [factor, smul_ne_zero_iff]
  exact and_iff_left polarization.1

/-- The same full electron response has its pole at the source physical frequency. -/
theorem em_electron_frequency_pole_generated (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (point : BasePoint) (left right : RestStateIndex) :
    ∀ᶠ e in scaleApproach, Tendsto
      (fun omega : ℝ => ((omega-sourceFrequency e.val (sourceSheet branch n unit e.val):ℝ):ℂ) •
        (sourceWholePhotonGreen e.val (omega/e.val^2) n *ᵥ
          actualRestNativeComplexForcingCovector point left right))
      (𝓝[≠] (sourceFrequency e.val (sourceSheet branch n unit e.val)))
      (𝓝 (emElectronFrequencyCarrier e.val (sourceSheet branch n unit e.val) n point left right)) := by
  filter_upwards [sourceWholePhotonGreen_frequencyResidue branch n unit] with e pole
  have cont : Continuous (fun R : Matrix (Fin 289) (Fin 289) ℂ =>
      R *ᵥ actualRestNativeComplexForcingCovector point left right) :=
    continuous_id.matrix_mulVec continuous_const
  simpa only [Function.comp_def, emElectronFrequencyCarrier, Matrix.smul_mulVec] using
    (cont.tendsto _).comp pole

end LowEnergy.GaussComposite.ActualEMCarrierOwn
