import H0mework.NavierStokes.SourceGeometry.SymmetryPhase

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceEvenFrequency

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow

noncomputable section

theorem phase_neg (wave : IntegerWavevector) : phase (-wave) = phase wave := by
  simp only [phase, Pi.neg_apply, zpow_neg, neg_one_zpow_eq_ite]
  split_ifs <;> norm_num

theorem phase_conj (wave : IntegerWavevector) : star (phase wave) = phase wave := by
  simp [phase]

theorem shift_transverse {field : ComplexVorticityHilbertState} (physical : WholeStateTransverse field) :
    WholeStateTransverse (shift field) := by
  intro wave
  simp only [shift_apply, dotProduct_smul, physical wave, smul_zero]

def transverseShift :
    wholeTransverseVorticitySubmodule →L[ℂ] wholeTransverseVorticitySubmodule :=
  (shift.comp wholeTransverseVorticitySubmodule.subtypeL).codRestrict
    wholeTransverseVorticitySubmodule (fun field => shift_transverse field.property)

@[simp] theorem transverseShift_val (field : wholeTransverseVorticitySubmodule) :
    (transverseShift field).val = shift field.val := rfl

theorem shift_reality {field : ComplexVorticityHilbertState} (physical : FiniteStateFourierReality field) :
    FiniteStateFourierReality (shift field) := by
  intro wave
  rw [shift_apply, shift_apply, physical wave]
  change phase (-wave) • vectorConj (field wave) = vectorConj (phase wave • field wave)
  rw [phase_neg]
  funext coordinate
  simp only [Pi.smul_apply, vectorConj, smul_eq_mul, star_mul, phase_conj]
  exact mul_comm _ _

theorem shift_amplitude (field : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    complexCoordinateAmplitudeSq (shift field wave) = complexCoordinateAmplitudeSq (field wave) := by
  simp only [shift_apply, complexCoordinateAmplitudeSq, Pi.smul_apply, smul_eq_mul,
    Complex.normSq_eq_norm_sq, norm_mul, phase_norm, one_mul]

theorem shift_mass (field : ComplexVorticityHilbertState) :
    wholeVorticityEuclideanMass (shift field) = wholeVorticityEuclideanMass field := by
  simp only [wholeVorticityEuclideanMass, vorticityRowAmplitude, shift_amplitude]

def OnEvenLattice (field : ComplexVorticityHilbertState) : Prop :=
  ∀ wave : IntegerWavevector, ¬ Even (wave 0) → field wave = 0

theorem shift_fixed_of_even {field : ComplexVorticityHilbertState} (supported : OnEvenLattice field) :
    shift field = field := by
  apply Subtype.ext
  funext wave
  by_cases even : Even (wave 0)
  · simp only [shift_apply, phase, even.neg_one_zpow, one_smul]
  · simp only [shift_apply, supported wave even, smul_zero]

theorem even_of_shift_fixed {field : ComplexVorticityHilbertState} (fixed : shift field = field) :
    OnEvenLattice field := by
  intro wave odd
  have same := congrArg (fun value : ComplexVorticityHilbertState => value wave) fixed
  simp only [shift_apply, phase, neg_one_zpow_eq_ite, if_neg odd, neg_one_smul] at same
  have twice : (2 : ℂ) • field wave = 0 := by
    calc
      _ = field wave + field wave := two_smul ℂ (field wave)
      _ = -field wave + field wave := congrArg (fun value => value + field wave) same.symm
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp twice).resolve_left (by norm_num)

end
end SaturationMonoid.NavierStokes.SourceEvenFrequency
