import H0mework.Physics.DiracEvolution.WeakGalerkinEnergy
import H0mework.NavierStokes.Energy.StrongContinuationKineticDifferenceGronwall
import H0mework.NavierStokes.Restart.CanonicalReplay
import H0mework.NavierStokes.VelocityGalerkin.FiniteObservationTimeTightness
import H0mework.NavierStokes.Fourier.WholeVelocityFixedOutputNonlinearRow

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeFullOrderEnergy

open PhysicsCore.StageNineDiracMatterWeakGalerkinEnergy
open Set
open scoped BigOperators
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Stage-Nine mass consumer accepts the original spectral Hilbert
carrier and its actual frozen linear action; it does not require a CU field. -/
theorem spectral_energy_from_stageNine
    (generator : H →L[ℝ] H) (path : ℝ → H) (domain : Set ℝ) (time : ℝ)
    (sourceDerivative :
      HasDerivWithinAt path (generator (path time)) domain time) :
    HasDerivWithinAt (fun actual => ‖path actual‖ ^ 2)
      (2 * inner ℝ (generator (path time)) (path time)) domain time := by
  let mass : ℝ → H →L[ℝ] H →L[ℝ] ℝ := fun _ => innerSL ℝ
  let stiffness : ℝ → H →L[ℝ] H →L[ℝ] ℝ :=
    fun _ => -((innerSL ℝ).comp generator)
  have derivative := galerkinWeakEnergy_hasDerivWithinAt
    mass 0 stiffness path (generator (path time)) domain time
    (by exact (hasDerivAt_const time (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ)).hasDerivWithinAt)
    sourceDerivative (by
      intro first second
      exact (real_inner_comm first second).symm)
    (by
      change inner ℝ (generator (path time)) (path time) +
        -inner ℝ (generator (path time)) (path time) = 0
      exact add_neg_cancel _)
  change HasDerivWithinAt (fun actual => inner ℝ (path actual) (path actual))
    (0 - 2 * -inner ℝ (generator (path time)) (path time)) domain time at derivative
  simpa only [real_inner_self_eq_norm_sq, mul_neg, sub_neg_eq_add, zero_add] using derivative

theorem observed_energy_from_stageNine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (read : E →L[ℝ] H) (generator : E →L[ℝ] E)
    (path : ℝ → E) (domain : Set ℝ) (time : ℝ)
    (sourceDerivative : HasDerivWithinAt path (generator (path time)) domain time) :
    HasDerivWithinAt (fun actual => ‖read (path actual)‖ ^ 2)
      (2 * inner ℝ (read (generator (path time))) (read (path time))) domain time := by
  let mass : ℝ → E →L[ℝ] E →L[ℝ] ℝ :=
    fun _ => (innerSL ℝ).bilinearComp read read
  let stiffness : ℝ → E →L[ℝ] E →L[ℝ] ℝ :=
    fun _ => -((innerSL ℝ).bilinearComp (read.comp generator) read)
  have derivative := galerkinWeakEnergy_hasDerivWithinAt
    mass 0 stiffness path (generator (path time)) domain time
    (by exact (hasDerivAt_const time ((innerSL ℝ).bilinearComp read read)).hasDerivWithinAt)
    sourceDerivative (by
      intro first second
      exact (real_inner_comm (read first) (read second)).symm)
    (by
      change inner ℝ (read (generator (path time))) (read (path time)) +
        -inner ℝ (read (generator (path time))) (read (path time)) = 0
      exact add_neg_cancel _)
  change HasDerivWithinAt
    (fun actual => inner ℝ (read (path actual)) (read (path actual)))
    (0 - 2 * -inner ℝ (read (generator (path time))) (read (path time))) domain time at derivative
  simpa only [real_inner_self_eq_norm_sq, mul_neg, sub_neg_eq_add, zero_add] using derivative

def rowRead (wave : IntegerWavevector) :
    ComplexVorticityHilbertState →L[ℝ] ComplexCoordinateVector :=
  lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave

def velocityRead (wave : IntegerWavevector) :
    ComplexVorticityHilbertState →L[ℝ] ComplexCoordinateVector :=
  (biotSavartVelocityCLM wave).comp (rowRead wave)

def frozenPair (state : ComplexVorticityHilbertState) (first second : IntegerWavevector) :
    ComplexVorticityHilbertState →L[ℝ] ComplexCoordinateVector :=
  (Complex.I * (((2 * Real.pi : ℝ) : ℂ)) *
      (dotProduct (complexWavevector second) (state first))) • velocityRead second -
    (Complex.I * (((2 * Real.pi : ℝ) : ℂ)) *
      (dotProduct (complexWavevector second) (finiteStateVelocityCoefficient state first))) • rowRead second

def frozenGenerator (modes : Finset IntegerWavevector) (nu : ℝ)
    (state : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState :=
  ∑ output ∈ modes,
    (lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 output).comp
      ((∑ first ∈ modes, ∑ second ∈ modes,
        if first + second = output then frozenPair state first second else 0) -
          (nu * integerWaveViscousMultiplier output) • rowRead output)

theorem frozenGenerator_self (modes : Finset IntegerWavevector) (nu : ℝ)
    (state : ComplexVorticityHilbertState) :
    frozenGenerator modes nu state state = finiteStateVorticityGenerator modes nu state := by
  simp only [frozenGenerator, finiteStateVorticityGenerator, sum_apply,
    ContinuousLinearMap.comp_apply, sub_apply, smul_apply]
  apply Finset.sum_congr rfl
  intro output _
  congr 1
  change (∑ first ∈ modes, ∑ second ∈ modes,
    (if first + second = output then frozenPair state first second else 0) state) -
      (nu * integerWaveViscousMultiplier output) • state output = _
  congr 1
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  split_ifs <;> rfl

abbrev SpectralIndex (modes : Finset IntegerWavevector) :=
  {wave // wave ∈ modes} × Coordinate

abbrev WeightedVelocityCarrier (modes : Finset IntegerWavevector) :=
  EuclideanSpace ℂ (SpectralIndex modes)

def weightedVelocityRead (modes : Finset IntegerWavevector) (weight : IntegerWavevector → ℝ) :
    ComplexVorticityHilbertState →L[ℝ] WeightedVelocityCarrier modes :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : SpectralIndex modes => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun index =>
      weight index.1.1 • ((ContinuousLinearMap.proj index.2).comp (velocityRead index.1.1)))

theorem weightedVelocityRead_apply (modes : Finset IntegerWavevector)
    (weight : IntegerWavevector → ℝ) (state : ComplexVorticityHilbertState)
    (index : SpectralIndex modes) :
    weightedVelocityRead modes weight state index =
      weight index.1.1 • finiteStateVelocityCoefficient state index.1.1 index.2 := rfl

def weightedVelocityEnergy (modes : Finset IntegerWavevector) (weight : IntegerWavevector → ℝ)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑ wave ∈ modes, weight wave ^ 2 * complexCoordinateVectorNormSq
    (finiteStateVelocityCoefficient state wave)

theorem weightedVelocityRead_norm_sq (modes : Finset IntegerWavevector)
    (weight : IntegerWavevector → ℝ) (state : ComplexVorticityHilbertState) :
    ‖weightedVelocityRead modes weight state‖ ^ 2 = weightedVelocityEnergy modes weight state := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [weightedVelocityRead_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Fintype.sum_prod_type, ← Finset.mul_sum, weightedVelocityEnergy, complexCoordinateVectorNormSq,
    ← Complex.normSq_eq_norm_sq]
  exact Finset.sum_attach modes (fun wave => weight wave ^ 2 *
    ∑ coordinate : Coordinate, Complex.normSq (finiteStateVelocityCoefficient state wave coordinate))

theorem weightedVelocityRead_inner (modes : Finset IntegerWavevector)
    (weight : IntegerWavevector → ℝ) (left right : ComplexVorticityHilbertState) :
    inner ℝ (weightedVelocityRead modes weight left) (weightedVelocityRead modes weight right) =
      ∑ wave ∈ modes, weight wave ^ 2 * complexCoordinateRealInner
        (finiteStateVelocityCoefficient left wave) (finiteStateVelocityCoefficient right wave) := by
  rw [PiLp.inner_apply]
  simp only [weightedVelocityRead_apply, real_inner_smul_left, real_inner_smul_right,
    Fintype.sum_prod_type]
  simp_rw [← mul_assoc, ← pow_two, ← Finset.mul_sum]
  rw [show (∑ wave : {wave // wave ∈ modes}, weight wave.1 ^ 2 *
      ∑ coordinate : Coordinate, inner ℝ (finiteStateVelocityCoefficient left wave.1 coordinate)
        (finiteStateVelocityCoefficient right wave.1 coordinate)) =
      ∑ wave ∈ modes, weight wave ^ 2 *
        ∑ coordinate : Coordinate, inner ℝ (finiteStateVelocityCoefficient left wave coordinate)
          (finiteStateVelocityCoefficient right wave coordinate) from
    Finset.sum_attach modes (fun wave => weight wave ^ 2 *
      ∑ coordinate : Coordinate, inner ℝ (finiteStateVelocityCoefficient left wave coordinate)
        (finiteStateVelocityCoefficient right wave coordinate))]
  apply Finset.sum_congr rfl
  intro wave _
  congr 1
  unfold complexCoordinateRealInner
  apply Finset.sum_congr rfl
  intro coordinate _
  simp [real_inner_eq_re_inner, RCLike.inner_apply, mul_comm]

variable {nu : Viscosity} {Seed : Type} [WholeRestartPhysicalSeed nu Seed]
  {seed : Seed} {radius : ℕ}

theorem stage_weightedVelocity_hasDerivAt
    (stage : GeneratedWholeRestartCanonicalStage seed radius) (weight : IntegerWavevector → ℝ)
    (time : ℝ) (inside : time ∈ Icc 0 (wholeRestartDuration seed)) :
    HasDerivAt (fun actual => weightedVelocityRead (wholeRestartModes radius) weight (stage.trajectory actual))
      (weightedVelocityRead (wholeRestartModes radius) weight
        (finiteStateVorticityGenerator (wholeRestartModes radius) nu.coeff (stage.trajectory time))) time :=
  (weightedVelocityRead (wholeRestartModes radius) weight).hasFDerivAt.comp_hasDerivAt time
    (stage.physical time inside).1

theorem stage_weightedVelocityEnergy_hasDerivAt
    (stage : GeneratedWholeRestartCanonicalStage seed radius) (weight : IntegerWavevector → ℝ)
    (time : ℝ) (inside : time ∈ Icc 0 (wholeRestartDuration seed)) :
    HasDerivAt (fun actual => weightedVelocityEnergy (wholeRestartModes radius) weight (stage.trajectory actual))
      (2 * ∑ wave ∈ wholeRestartModes radius, weight wave ^ 2 * complexCoordinateRealInner
        (finiteStateVelocityCoefficient (stage.trajectory time) wave)
        (biotSavartVelocityCoefficient wave
          (finiteStateVorticityGenerator (wholeRestartModes radius) nu.coeff (stage.trajectory time) wave))) time := by
  have actual := (stage.physical time inside).1
  rw [← frozenGenerator_self (wholeRestartModes radius) nu.coeff (stage.trajectory time)] at actual
  have derivative := observed_energy_from_stageNine
    (weightedVelocityRead (wholeRestartModes radius) weight)
    (frozenGenerator (wholeRestartModes radius) nu.coeff (stage.trajectory time))
    stage.trajectory univ time actual.hasDerivWithinAt
  rw [frozenGenerator_self, real_inner_comm, weightedVelocityRead_inner] at derivative
  simpa only [weightedVelocityRead_norm_sq, hasDerivWithinAt_univ,
    finiteStateVelocityCoefficient] using derivative

def weightedVelocityDissipation (modes : Finset IntegerWavevector)
    (weight : IntegerWavevector → ℝ) (state : ComplexVorticityHilbertState) : ℝ :=
  ∑ wave ∈ modes, weight wave ^ 2 * integerWaveViscousMultiplier wave *
    complexCoordinateVectorNormSq (finiteStateVelocityCoefficient state wave)

def weightedVelocityNonlinearWork (modes : Finset IntegerWavevector)
    (weight : IntegerWavevector → ℝ) (state : ComplexVorticityHilbertState) : ℝ :=
  ∑ wave ∈ modes, weight wave ^ 2 * complexCoordinateRealInner
    (finiteStateVelocityCoefficient state wave)
    (wholeStateVelocityNonlinearCoefficientAt (finiteStateWholeVelocity modes state) wave)

theorem stage_weightedVelocityEnergy_action_hasDerivAt
    (stage : GeneratedWholeRestartCanonicalStage seed radius) (weight : IntegerWavevector → ℝ)
    (time : ℝ) (inside : time ∈ Icc 0 (wholeRestartDuration seed)) :
    HasDerivAt (fun actual => weightedVelocityEnergy (wholeRestartModes radius) weight (stage.trajectory actual))
      (2 * weightedVelocityNonlinearWork (wholeRestartModes radius) weight (stage.trajectory time) -
        2 * nu.coeff * weightedVelocityDissipation (wholeRestartModes radius) weight (stage.trajectory time)) time := by
  have derivative := stage_weightedVelocityEnergy_hasDerivAt stage weight time inside
  have work :
      (∑ wave ∈ wholeRestartModes radius, weight wave ^ 2 * complexCoordinateRealInner
        (finiteStateVelocityCoefficient (stage.trajectory time) wave)
        (biotSavartVelocityCoefficient wave
          (finiteStateVorticityGenerator (wholeRestartModes radius) nu.coeff (stage.trajectory time) wave))) =
      weightedVelocityNonlinearWork (wholeRestartModes radius) weight (stage.trajectory time) -
        nu.coeff * weightedVelocityDissipation (wholeRestartModes radius) weight (stage.trajectory time) := by
    unfold weightedVelocityNonlinearWork weightedVelocityDissipation
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro wave waveMem
    have waveNe : wave ≠ 0 := fun same =>
      zero_not_mem_puncturedIntegerWaveFrequencyCube radius (same ▸ waveMem)
    rw [biotSavart_finiteStateVorticityGenerator_eq_velocityUpdate
      (wholeRestartModes radius) (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
      nu.coeff (stage.trajectory time) (fun actual _ => (stage.physical time inside).2.2.1 actual)
      wave waveMem,
      complexCoordinateRealInner_sub_right,
      complexCoordinateRealInner_transverseProjection wave
        (finiteStateVelocityCoefficient (stage.trajectory time) wave) _ waveNe
        (by exact complexWavevector_dot_biotSavartVelocityCoefficient wave (stage.trajectory time wave)),
      complexCoordinateRealInner_real_smul_right,
      complexCoordinateRealInner_self,
      wholeStateVelocityNonlinearCoefficientAt_finiteStateWholeVelocity]
    ring
  rw [work] at derivative
  convert derivative using 1
  ring

end
end SaturationMonoid.NavierStokes.NativeFullOrderEnergy
