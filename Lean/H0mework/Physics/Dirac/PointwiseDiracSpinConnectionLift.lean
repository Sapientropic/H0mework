import H0mework.Physics.Dirac.DiracCliffordRepresentation
import H0mework.Physics.Lorentz.PointwiseLorentzSpinConnectionRecovery

/-!
# Generated pointwise Dirac spin-connection lift

The existing coframe first-jet producer computes an `so(1,3)` vector
connection and proves its Lorentz-skew law.  This module lowers its internal
indices, reads the six oriented bivector components, and applies the actual
Dirac bivector representation.  The Clifford commutator law, chirality
preservation, and coframe-gamma compatibility are theorem outputs.

In particular, the already generated tetrad postulate is transported to

`nabla_mu gamma_nu = 0`.

No spinor-action matrix or gamma-compatibility certificate is supplied as an
input.  The result is still pointwise/first-jet geometry, not a smooth spin
bundle or a proof of global spin-structure existence.
-/

namespace SaturationMonoid.PhysicsCore.PointwiseDiracSpinConnectionLift

open DiracCliffordRepresentation
open PointwiseLorentzianCoframeJet
open scoped Matrix

noncomputable section

def lorentzBivectorFirst : Fin 6 → LorentzianIndex :=
  ![0, 0, 0, 2, 3, 1]

def lorentzBivectorSecond : Fin 6 → LorentzianIndex :=
  ![1, 2, 3, 3, 1, 2]

@[simp] theorem minkowskiInternalSign_zero_value :
    minkowskiInternalSign (0 : LorentzianIndex) = -1 := by
  simp [minkowskiInternalSign]

@[simp] theorem minkowskiInternalSign_one_value :
    minkowskiInternalSign (1 : LorentzianIndex) = 1 := by
  simp [minkowskiInternalSign, show (1 : LorentzianIndex) ≠ 0 by decide]

@[simp] theorem minkowskiInternalSign_two_value :
    minkowskiInternalSign (2 : LorentzianIndex) = 1 := by
  simp [minkowskiInternalSign, show (2 : LorentzianIndex) ≠ 0 by decide]

@[simp] theorem minkowskiInternalSign_three_value :
    minkowskiInternalSign (3 : LorentzianIndex) = 1 := by
  simp [minkowskiInternalSign, show (3 : LorentzianIndex) ≠ 0 by decide]

def loweredLorentzConnectionCoefficient
    (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex) (pair : Fin 6) : ℝ :=
  minkowskiInternalSign (lorentzBivectorFirst pair) *
    connection direction (lorentzBivectorFirst pair)
      (lorentzBivectorSecond pair)

/-- The genuine Dirac lift of a Lorentz-vector connection.  The factor
`1/2` multiplies the six oriented independent pairs and is equivalent to the
usual `1/4` sum over all ordered internal pairs. -/
def diracSpinConnectionLift
    (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex) : DiracMatrix :=
  ∑ pair : Fin 6,
    ((2 : ℂ)⁻¹ *
        (loweredLorentzConnectionCoefficient connection direction pair : ℂ)) •
      (diracGamma (lorentzBivectorFirst pair) *
        diracGamma (lorentzBivectorSecond pair))

/-- Dependency-light real-linear packaging of the generated Dirac lift. -/
def diracSpinConnectionLiftLinear
    (direction : LorentzianIndex) :
    PointwiseLorentzSpinConnection →ₗ[ℝ] DiracMatrix where
  toFun connection := diracSpinConnectionLift connection direction
  map_add' := by
    intro first second
    unfold diracSpinConnectionLift
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro pair _
    simp only [loweredLorentzConnectionCoefficient, Pi.add_apply]
    module
  map_smul' := by
    intro parameter connection
    conv_rhs =>
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    unfold diracSpinConnectionLift
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro pair _
    simp only [loweredLorentzConnectionCoefficient, Pi.smul_apply,
      smul_eq_mul]
    rw [smul_smul]
    congr 1
    push_cast
    simp only [id_eq]
    field_simp
    rw [mul_assoc, mul_assoc]
    congr 1
    exact mul_comm _ _

@[simp] theorem diracSpinConnectionLiftLinear_apply
    (direction : LorentzianIndex)
    (connection : PointwiseLorentzSpinConnection) :
    diracSpinConnectionLiftLinear direction connection =
      diracSpinConnectionLift connection direction :=
  rfl

/-- Every oriented Clifford bivector used by the lift is traceless. -/
theorem diracGamma_orientedBivector_trace_eq_zero (pair : Fin 6) :
    Matrix.trace
        (diracGamma (lorentzBivectorFirst pair) *
          diracGamma (lorentzBivectorSecond pair)) = 0 := by
  have clifford :=
    diracGamma_clifford (lorentzBivectorFirst pair)
      (lorentzBivectorSecond pair)
  have offDiagonal :
      complexMinkowskiEntry (lorentzBivectorFirst pair)
          (lorentzBivectorSecond pair) = 0 := by
    fin_cases pair <;>
      simp [lorentzBivectorFirst, lorentzBivectorSecond,
        complexMinkowskiEntry, minkowskiInternalMetric]
  rw [offDiagonal] at clifford
  simp only [mul_zero, zero_smul] at clifford
  have traceClifford := congrArg Matrix.trace clifford
  rw [Matrix.trace_add, Matrix.trace_zero] at traceClifford
  have traceCommute := Matrix.trace_mul_comm
    (diracGamma (lorentzBivectorFirst pair))
    (diracGamma (lorentzBivectorSecond pair))
  rw [traceCommute] at traceClifford
  have doubled :
      (2 : ℂ) * Matrix.trace
          (diracGamma (lorentzBivectorSecond pair) *
            diracGamma (lorentzBivectorFirst pair)) = 0 := by
    simpa [two_mul] using traceClifford
  have secondZero :
      Matrix.trace
          (diracGamma (lorentzBivectorSecond pair) *
            diracGamma (lorentzBivectorFirst pair)) = 0 :=
    (mul_eq_zero.mp doubled).resolve_left (by norm_num)
  exact traceCommute.trans secondZero

/-- The actual six-coordinate Dirac lift is traceless for every raw
connection; this is an output of its Clifford formula. -/
theorem diracSpinConnectionLift_trace_eq_zero
    (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex) :
    Matrix.trace (diracSpinConnectionLift connection direction) = 0 := by
  rw [diracSpinConnectionLift, Matrix.trace_sum]
  apply Finset.sum_eq_zero
  intro pair _
  rw [Matrix.trace_smul, diracGamma_orientedBivector_trace_eq_zero]
  simp

def diracMatrixCommutator (first second : DiracMatrix) : DiracMatrix :=
  first * second - second * first

theorem diracGamma_bivector_commutator
    (first second internal : LorentzianIndex) :
    diracMatrixCommutator
        (diracGamma first * diracGamma second) (diracGamma internal) =
      (2 * complexMinkowskiEntry second internal) • diracGamma first -
        (2 * complexMinkowskiEntry internal first) •
          diracGamma second := by
  rw [diracMatrixCommutator]
  calc
    (diracGamma first * diracGamma second) * diracGamma internal -
          diracGamma internal * (diracGamma first * diracGamma second) =
        diracGamma first *
            (diracGamma second * diracGamma internal +
              diracGamma internal * diracGamma second) -
          (diracGamma internal * diracGamma first +
              diracGamma first * diracGamma internal) *
            diracGamma second := by noncomm_ring
    _ = diracGamma first *
            ((2 * complexMinkowskiEntry second internal) •
              (1 : DiracMatrix)) -
          ((2 * complexMinkowskiEntry internal first) •
              (1 : DiracMatrix)) * diracGamma second := by
        rw [diracGamma_clifford, diracGamma_clifford]
    _ = _ := by
      simp

theorem lorentzSkew_entry
    (connection : PointwiseLorentzSpinConnection)
    (hskew : LorentzSkew connection)
    (direction first second : LorentzianIndex) :
    minkowskiInternalSign second * connection direction second first +
        minkowskiInternalSign first * connection direction first second =
      0 := by
  have hentry := congrFun (congrFun (hskew direction) first) second
  rw [minkowskiInternalMetric_eq_diagonal_sign] at hentry
  simpa [spinConnectionMatrix, Matrix.mul_diagonal,
    Matrix.diagonal_mul, mul_comm] using hentry

theorem lorentzSkew_diagonal_zero
    (connection : PointwiseLorentzSpinConnection)
    (hskew : LorentzSkew connection)
    (direction internal : LorentzianIndex) :
    connection direction internal internal = 0 := by
  have hentry := lorentzSkew_entry connection hskew direction internal internal
  fin_cases internal <;>
    norm_num [minkowskiInternalSign] at hentry ⊢ <;> linarith

/-- Ordered-pair form of the six-coordinate lift on the Lorentz-skew domain.
It is the finite `1/4` formula over all internal pairs and is the convenient
mouth for finite Spin covariance. -/
theorem diracSpinConnectionLift_eq_ordered_sum
    (connection : PointwiseLorentzSpinConnection)
    (hskew : LorentzSkew connection)
    (direction : LorentzianIndex) :
    diracSpinConnectionLift connection direction =
      ∑ first : LorentzianIndex, ∑ second : LorentzianIndex,
        ((4 : ℂ)⁻¹ *
            (minkowskiInternalSign first *
              connection direction first second : ℝ)) •
          (diracGamma first * diracGamma second) := by
  have h00 := lorentzSkew_diagonal_zero connection hskew direction 0
  have h11 := lorentzSkew_diagonal_zero connection hskew direction 1
  have h22 := lorentzSkew_diagonal_zero connection hskew direction 2
  have h33 := lorentzSkew_diagonal_zero connection hskew direction 3
  have h10 : connection direction 1 0 = connection direction 0 1 := by
    have h := lorentzSkew_entry connection hskew direction 0 1
    simp only [minkowskiInternalSign_one_value,
      minkowskiInternalSign_zero_value, one_mul, neg_one_mul] at h
    linarith
  have h20 : connection direction 2 0 = connection direction 0 2 := by
    have h := lorentzSkew_entry connection hskew direction 0 2
    simp only [minkowskiInternalSign_two_value,
      minkowskiInternalSign_zero_value, one_mul, neg_one_mul] at h
    linarith
  have h30 : connection direction 3 0 = connection direction 0 3 := by
    have h := lorentzSkew_entry connection hskew direction 0 3
    simp only [minkowskiInternalSign_three_value,
      minkowskiInternalSign_zero_value, one_mul, neg_one_mul] at h
    linarith
  have h21 : connection direction 2 1 = -connection direction 1 2 := by
    have h := lorentzSkew_entry connection hskew direction 1 2
    simp only [minkowskiInternalSign_two_value,
      minkowskiInternalSign_one_value, one_mul] at h
    linarith
  have h31 : connection direction 3 1 = -connection direction 1 3 := by
    have h := lorentzSkew_entry connection hskew direction 1 3
    simp only [minkowskiInternalSign_three_value,
      minkowskiInternalSign_one_value, one_mul] at h
    linarith
  have h32 : connection direction 3 2 = -connection direction 2 3 := by
    have h := lorentzSkew_entry connection hskew direction 2 3
    simp only [minkowskiInternalSign_three_value,
      minkowskiInternalSign_two_value, one_mul] at h
    linarith
  have gamma10 :
      diracGamma 1 * diracGamma 0 =
        -(diracGamma 0 * diracGamma 1) :=
    eq_neg_of_add_eq_zero_left diracGammaOneZero_anticommute
  have gamma20 :
      diracGamma 2 * diracGamma 0 =
        -(diracGamma 0 * diracGamma 2) :=
    eq_neg_of_add_eq_zero_left diracGammaTwoZero_anticommute
  have gamma30 :
      diracGamma 3 * diracGamma 0 =
        -(diracGamma 0 * diracGamma 3) :=
    eq_neg_of_add_eq_zero_left diracGammaThreeZero_anticommute
  have gamma21 :
      diracGamma 2 * diracGamma 1 =
        -(diracGamma 1 * diracGamma 2) :=
    eq_neg_of_add_eq_zero_right diracGammaOneTwo_anticommute
  have gamma31 :
      diracGamma 3 * diracGamma 1 =
        -(diracGamma 1 * diracGamma 3) :=
    eq_neg_of_add_eq_zero_right diracGammaOneThree_anticommute
  have gamma32 :
      diracGamma 3 * diracGamma 2 =
        -(diracGamma 2 * diracGamma 3) :=
    eq_neg_of_add_eq_zero_left diracGammaThreeTwo_anticommute
  simp [diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient,
    lorentzBivectorFirst, lorentzBivectorSecond,
    Fin.sum_univ_four, Fin.sum_univ_six,
    h00, h11, h22, h33, h10, h20, h30, h21, h31, h32,
    gamma10, gamma20, gamma30, gamma21, gamma31, gamma32];
  module

theorem diracSpinConnectionLift_commutator_upperGamma
    (connection : PointwiseLorentzSpinConnection)
    (hskew : LorentzSkew connection)
    (direction internal : LorentzianIndex) :
    diracMatrixCommutator (diracSpinConnectionLift connection direction)
        (diracGamma internal) =
      -∑ basisIndex : LorentzianIndex,
        (connection direction internal basisIndex : ℂ) •
          diracGamma basisIndex := by
  have h00 := lorentzSkew_diagonal_zero connection hskew direction 0
  have h11 := lorentzSkew_diagonal_zero connection hskew direction 1
  have h22 := lorentzSkew_diagonal_zero connection hskew direction 2
  have h33 := lorentzSkew_diagonal_zero connection hskew direction 3
  have h10 : connection direction 1 0 = connection direction 0 1 := by
    have h := lorentzSkew_entry connection hskew direction 0 1
    simp only [minkowskiInternalSign_one_value,
      minkowskiInternalSign_zero_value, one_mul, neg_one_mul] at h
    linarith
  have h20 : connection direction 2 0 = connection direction 0 2 := by
    have h := lorentzSkew_entry connection hskew direction 0 2
    simp only [minkowskiInternalSign_two_value,
      minkowskiInternalSign_zero_value, one_mul, neg_one_mul] at h
    linarith
  have h30 : connection direction 3 0 = connection direction 0 3 := by
    have h := lorentzSkew_entry connection hskew direction 0 3
    simp only [minkowskiInternalSign_three_value,
      minkowskiInternalSign_zero_value, one_mul, neg_one_mul] at h
    linarith
  have h21 : connection direction 2 1 = -connection direction 1 2 := by
    have h := lorentzSkew_entry connection hskew direction 1 2
    simp only [minkowskiInternalSign_two_value,
      minkowskiInternalSign_one_value, one_mul] at h
    linarith
  have h31 : connection direction 3 1 = -connection direction 1 3 := by
    have h := lorentzSkew_entry connection hskew direction 1 3
    simp only [minkowskiInternalSign_three_value,
      minkowskiInternalSign_one_value, one_mul] at h
    linarith
  have h32 : connection direction 3 2 = -connection direction 2 3 := by
    have h := lorentzSkew_entry connection hskew direction 2 3
    simp only [minkowskiInternalSign_three_value,
      minkowskiInternalSign_two_value, one_mul] at h
    linarith
  calc
    diracMatrixCommutator (diracSpinConnectionLift connection direction)
        (diracGamma internal) =
      ∑ pair : Fin 6,
        ((2 : ℂ)⁻¹ *
            (loweredLorentzConnectionCoefficient connection direction pair : ℂ)) •
          diracMatrixCommutator
            (diracGamma (lorentzBivectorFirst pair) *
              diracGamma (lorentzBivectorSecond pair))
            (diracGamma internal) := by
        simp only [diracMatrixCommutator, diracSpinConnectionLift,
          Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul,
          Matrix.mul_smul, ← Finset.sum_sub_distrib, smul_sub]
    _ = ∑ pair : Fin 6,
        ((2 : ℂ)⁻¹ *
            (loweredLorentzConnectionCoefficient connection direction pair : ℂ)) •
          ((2 * complexMinkowskiEntry (lorentzBivectorSecond pair) internal) •
              diracGamma (lorentzBivectorFirst pair) -
            (2 * complexMinkowskiEntry internal (lorentzBivectorFirst pair)) •
              diracGamma (lorentzBivectorSecond pair)) := by
        apply Finset.sum_congr rfl
        intro pair _
        rw [diracGamma_bivector_commutator]
    _ = -∑ basisIndex : LorentzianIndex,
        (connection direction internal basisIndex : ℂ) •
          diracGamma basisIndex := by
        fin_cases internal <;>
          simp [lorentzBivectorFirst, lorentzBivectorSecond,
            loweredLorentzConnectionCoefficient,
            complexMinkowskiEntry, minkowskiInternalMetric,
            minkowskiInternalSign, Fin.sum_univ_six,
            Fin.sum_univ_four, h00, h11, h22, h33,
            h10, h20, h30, h21, h31, h32] <;>
          module

theorem diracSpinConnectionLift_commutator_lowerGamma
    (connection : PointwiseLorentzSpinConnection)
    (hskew : LorentzSkew connection)
    (direction internal : LorentzianIndex) :
    diracMatrixCommutator (diracSpinConnectionLift connection direction)
        (loweredDiracGamma internal) =
      ∑ basisIndex : LorentzianIndex,
        (connection direction basisIndex internal : ℂ) •
          loweredDiracGamma basisIndex := by
  have hupper :=
    diracSpinConnectionLift_commutator_upperGamma
      connection hskew direction internal
  calc
    diracMatrixCommutator (diracSpinConnectionLift connection direction)
        (loweredDiracGamma internal) =
      (minkowskiInternalSign internal : ℂ) •
        diracMatrixCommutator
          (diracSpinConnectionLift connection direction)
          (diracGamma internal) := by
        simp [loweredDiracGamma, diracMatrixCommutator, smul_sub]
    _ = (minkowskiInternalSign internal : ℂ) •
        (-∑ basisIndex : LorentzianIndex,
          (connection direction internal basisIndex : ℂ) •
            diracGamma basisIndex) := by rw [hupper]
    _ = ∑ basisIndex : LorentzianIndex,
        (connection direction basisIndex internal : ℂ) •
          loweredDiracGamma basisIndex := by
      rw [smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro basisIndex _
      rw [loweredDiracGamma, smul_smul, smul_smul]
      have hentry :=
        lorentzSkew_entry connection hskew direction internal basisIndex
      have hcoefficientReal :
          -minkowskiInternalSign internal *
                connection direction internal basisIndex =
            connection direction basisIndex internal *
              minkowskiInternalSign basisIndex := by
        linarith
      have hcoefficientComplex :
          (-(minkowskiInternalSign internal : ℂ)) *
                (connection direction internal basisIndex : ℂ) =
            (connection direction basisIndex internal : ℂ) *
              (minkowskiInternalSign basisIndex : ℂ) := by
        exact_mod_cast hcoefficientReal
      rw [← hcoefficientComplex]
      module

theorem diracGammaFive_commutes_bivector
    (first second : LorentzianIndex) :
    diracGammaFive * (diracGamma first * diracGamma second) =
      (diracGamma first * diracGamma second) * diracGammaFive := by
  have hfirstSum := diracGammaFive_anticommutes first
  have hsecondSum := diracGammaFive_anticommutes second
  have hfirst :
      diracGammaFive * diracGamma first =
        -(diracGamma first * diracGammaFive) :=
    eq_neg_of_add_eq_zero_left hfirstSum
  have hsecond :
      diracGammaFive * diracGamma second =
        -(diracGamma second * diracGammaFive) :=
    eq_neg_of_add_eq_zero_left hsecondSum
  calc
    diracGammaFive * (diracGamma first * diracGamma second) =
        (diracGammaFive * diracGamma first) * diracGamma second := by
          rw [Matrix.mul_assoc]
    _ = -(diracGamma first * diracGammaFive) *
          diracGamma second := by rw [hfirst]
    _ = -diracGamma first *
          (diracGammaFive * diracGamma second) := by noncomm_ring
    _ = -diracGamma first *
          (-(diracGamma second * diracGammaFive)) := by rw [hsecond]
    _ = (diracGamma first * diracGamma second) *
          diracGammaFive := by noncomm_ring

theorem diracSpinConnectionLift_commutes_gammaFive
    (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex) :
    diracSpinConnectionLift connection direction * diracGammaFive =
      diracGammaFive * diracSpinConnectionLift connection direction := by
  rw [diracSpinConnectionLift, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [diracGammaFive_commutes_bivector]

theorem diracSpinConnectionLift_preserves_leftChirality
    (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex) :
    diracSpinConnectionLift connection direction * leftChiralityProjector =
      leftChiralityProjector *
        diracSpinConnectionLift connection direction := by
  rw [leftChiralityProjector, Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    diracSpinConnectionLift_commutes_gammaFive]

theorem diracSpinConnectionLift_preserves_rightChirality
    (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex) :
    diracSpinConnectionLift connection direction * rightChiralityProjector =
      rightChiralityProjector *
        diracSpinConnectionLift connection direction := by
  rw [rightChiralityProjector, Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    diracSpinConnectionLift_commutes_gammaFive]

def coframeDiracGamma
    (jet : PointwiseLorentzianCoframeJet)
    (coordinate : LorentzianIndex) : DiracMatrix :=
  ∑ internal : LorentzianIndex,
    (jet.coframe internal coordinate : ℂ) • loweredDiracGamma internal

def coframeDiracGammaDerivative
    (jet : PointwiseLorentzianCoframeJet)
    (direction coordinate : LorentzianIndex) : DiracMatrix :=
  ∑ internal : LorentzianIndex,
    (jet.derivative direction internal coordinate : ℂ) •
      loweredDiracGamma internal

def complexTetradResidual
    (jet : PointwiseLorentzianCoframeJet)
    (direction internal coordinate : LorentzianIndex) : ℂ :=
  (jet.derivative direction internal coordinate : ℂ) -
    ∑ upper : LorentzianIndex,
      (jet.leviCivitaConnection upper direction coordinate : ℂ) *
        (jet.coframe internal upper : ℂ) +
    ∑ internalIn : LorentzianIndex,
      (jet.lorentzSpinConnection direction internal internalIn : ℂ) *
        (jet.coframe internalIn coordinate : ℂ)

theorem complexTetradResidual_eq_zero
    (jet : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det jet.coframe ≠ 0)
    (direction internal coordinate : LorentzianIndex) :
    complexTetradResidual jet direction internal coordinate = 0 := by
  have hreal := jet.tetradPostulate_lorentzSpinConnection
    (isUnit_iff_ne_zero.mpr hcoframe) direction internal coordinate
  have hcomplex := congrArg (fun value : ℝ => (value : ℂ)) hreal
  push_cast at hcomplex
  simpa [complexTetradResidual] using hcomplex

theorem diracSpinConnectionLift_commutator_coframeGamma
    (jet : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det jet.coframe ≠ 0)
    (direction coordinate : LorentzianIndex) :
    diracMatrixCommutator
        (diracSpinConnectionLift jet.lorentzSpinConnection direction)
        (coframeDiracGamma jet coordinate) =
      ∑ internal : LorentzianIndex,
        (jet.coframe internal coordinate : ℂ) •
          (∑ internalOut : LorentzianIndex,
            (jet.lorentzSpinConnection direction internalOut internal : ℂ) •
              loweredDiracGamma internalOut) := by
  have hskew := jet.lorentzSpinConnection_lorentzSkew hcoframe
  calc
    diracMatrixCommutator
        (diracSpinConnectionLift jet.lorentzSpinConnection direction)
        (coframeDiracGamma jet coordinate) =
      ∑ internal : LorentzianIndex,
        (jet.coframe internal coordinate : ℂ) •
          diracMatrixCommutator
            (diracSpinConnectionLift jet.lorentzSpinConnection direction)
            (loweredDiracGamma internal) := by
        simp only [diracMatrixCommutator, coframeDiracGamma,
          Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul,
          Matrix.smul_mul, ← Finset.sum_sub_distrib, smul_sub]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro internal _
      rw [diracSpinConnectionLift_commutator_lowerGamma
        jet.lorentzSpinConnection hskew]

def coframeDiracGammaCovariantDerivative
    (jet : PointwiseLorentzianCoframeJet)
    (direction coordinate : LorentzianIndex) : DiracMatrix :=
  coframeDiracGammaDerivative jet direction coordinate -
    ∑ upper : LorentzianIndex,
      (jet.leviCivitaConnection upper direction coordinate : ℂ) •
        coframeDiracGamma jet upper +
    diracMatrixCommutator
      (diracSpinConnectionLift jet.lorentzSpinConnection direction)
      (coframeDiracGamma jet coordinate)

theorem coframeDiracGammaCovariantDerivative_eq_tetradResidual
    (jet : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det jet.coframe ≠ 0)
    (direction coordinate : LorentzianIndex) :
    coframeDiracGammaCovariantDerivative jet direction coordinate =
      ∑ internal : LorentzianIndex,
        complexTetradResidual jet direction internal coordinate •
          loweredDiracGamma internal := by
  rw [coframeDiracGammaCovariantDerivative,
    diracSpinConnectionLift_commutator_coframeGamma jet hcoframe]
  simp only [coframeDiracGammaDerivative, coframeDiracGamma,
    complexTetradResidual, Fin.sum_univ_four]
  module

/-- The generated Levi-Civita/Lorentz connection and its actual Dirac lift
make the coframe gamma field covariantly constant. -/
theorem coframeDiracGammaCovariantDerivative_eq_zero
    (jet : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det jet.coframe ≠ 0)
    (direction coordinate : LorentzianIndex) :
    coframeDiracGammaCovariantDerivative jet direction coordinate = 0 := by
  rw [coframeDiracGammaCovariantDerivative_eq_tetradResidual jet hcoframe]
  apply Finset.sum_eq_zero
  intro internal _
  rw [complexTetradResidual_eq_zero jet hcoframe]
  exact zero_smul ℂ (loweredDiracGamma internal)

end
end SaturationMonoid.PhysicsCore.PointwiseDiracSpinConnectionLift
