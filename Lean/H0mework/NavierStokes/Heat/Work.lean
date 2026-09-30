import H0mework.NavierStokes.SourceEstimates.ReferencePair

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.HeatWork

open Matrix
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientCoarseFilterProcess
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger

noncomputable section

def pair (p q : IntegerWavevector) (left right : ComplexCoordinateVector) : ComplexCoordinateVector :=
  ReferencePair.stretching left right q - ReferencePair.transport left right p q

theorem pair_eq_original (p q : IntegerWavevector) (left right : ComplexVorticityHilbertState) :
    pair p q (left p) (right q) = finiteStateVorticityBilinearPairContribution left right (p,q) := rfl

private theorem velocity_smul (wave : IntegerWavevector) (scalar : Real) (row : ComplexCoordinateVector) :
    biotSavartVelocityCoefficient wave (scalar • row) = scalar • biotSavartVelocityCoefficient wave row := by
  change biotSavartVelocityCoefficient wave ((scalar : Complex) • row) =
    (scalar : Complex) • biotSavartVelocityCoefficient wave row
  exact biotSavartVelocityCoefficient_smul wave scalar row

theorem pair_smul_left (p q : IntegerWavevector) (scalar : Real) (left right : ComplexCoordinateVector) :
    pair p q (scalar • left) right = scalar • pair p q left right := by
  unfold pair ReferencePair.stretching ReferencePair.transport
  rw [velocity_smul]
  change (Complex.I * ((2 * Real.pi : Real) : Complex) *
      (complexWavevector q ⬝ᵥ ((scalar : Complex) • left))) • biotSavartVelocityCoefficient q right -
    (Complex.I * ((2 * Real.pi : Real) : Complex) *
      (complexWavevector q ⬝ᵥ ((scalar : Complex) • biotSavartVelocityCoefficient p left))) • right =
    (scalar : Complex) •
      ((Complex.I * ((2 * Real.pi : Real) : Complex) * (complexWavevector q ⬝ᵥ left)) •
          biotSavartVelocityCoefficient q right -
        (Complex.I * ((2 * Real.pi : Real) : Complex) *
          (complexWavevector q ⬝ᵥ biotSavartVelocityCoefficient p left)) • right)
  simp only [dotProduct_smul]
  module

theorem pair_smul_right (p q : IntegerWavevector) (scalar : Real) (left right : ComplexCoordinateVector) :
    pair p q left (scalar • right) = scalar • pair p q left right := by
  unfold pair ReferencePair.stretching ReferencePair.transport
  rw [velocity_smul]
  change (Complex.I * ((2 * Real.pi : Real) : Complex) * (complexWavevector q ⬝ᵥ left)) •
      ((scalar : Complex) • biotSavartVelocityCoefficient q right) -
    (Complex.I * ((2 * Real.pi : Real) : Complex) *
      (complexWavevector q ⬝ᵥ biotSavartVelocityCoefficient p left)) • ((scalar : Complex) • right) =
    (scalar : Complex) •
      ((Complex.I * ((2 * Real.pi : Real) : Complex) * (complexWavevector q ⬝ᵥ left)) •
          biotSavartVelocityCoefficient q right -
        (Complex.I * ((2 * Real.pi : Real) : Complex) *
          (complexWavevector q ⬝ᵥ biotSavartVelocityCoefficient p left)) • right)
  module

def work (p q : IntegerWavevector) (output left right : ComplexCoordinateVector) : Real :=
  complexCoordinateRealInner output (pair p q left right)

private theorem inner_smul_left (scalar : Real) (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner (scalar • left) right = scalar * complexCoordinateRealInner left right := by
  unfold complexCoordinateRealInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem work_smul_output (p q : IntegerWavevector) (scalar : Real) (output left right : ComplexCoordinateVector) :
    work p q (scalar • output) left right = scalar * work p q output left right :=
  inner_smul_left scalar output (pair p q left right)

theorem work_smul_left (p q : IntegerWavevector) (scalar : Real) (output left right : ComplexCoordinateVector) :
    work p q output (scalar • left) right = scalar * work p q output left right := by
  rw [work, pair_smul_left, complexCoordinateRealInner_real_smul_right]
  rfl

theorem work_smul_right (p q : IntegerWavevector) (scalar : Real) (output left right : ComplexCoordinateVector) :
    work p q output left (scalar • right) = scalar * work p q output left right := by
  rw [work, pair_smul_right, complexCoordinateRealInner_real_smul_right]
  rfl

def heatWeight (nu : Viscosity) (p q : IntegerWavevector) : Real :=
  nu.coeff * (integerWaveViscousMultiplier p + integerWaveViscousMultiplier q + integerWaveViscousMultiplier (p+q))

theorem heatWeight_pos (nu : Viscosity) (p q : IntegerWavevector) (nonzero : p ≠ 0) :
    0 < heatWeight nu p q := by
  apply mul_pos nu.coeff_pos
  have ppos := integerWaveNormSq_pos nonzero
  have qnonneg := integerWaveNormSq_nonneg q
  have outnonneg := integerWaveNormSq_nonneg (p+q)
  unfold integerWaveViscousMultiplier
  positivity

/-- The scalar work uses three covariant legs. Its heat divisor is a positive
sum, so vector-field spectral resonances do not obstruct this primitive. -/
theorem heat_primitive (nu : Viscosity) (p q : IntegerWavevector) (nonzero : p ≠ 0)
    (output left right : ComplexCoordinateVector) :
    (work p q (-(nu.coeff * integerWaveViscousMultiplier (p+q)) • output) left right +
      work p q output (-(nu.coeff * integerWaveViscousMultiplier p) • left) right +
      work p q output left (-(nu.coeff * integerWaveViscousMultiplier q) • right)) /
        heatWeight nu p q = -work p q output left right := by
  rw [work_smul_output, work_smul_left, work_smul_right]
  apply (div_eq_iff (heatWeight_pos nu p q nonzero).ne').2
  unfold heatWeight
  ring

end
end SaturationMonoid.NavierStokes.HeatWork
