import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorExchangeSelection

/-! The complete peripheral-scalar coefficient table is emitted from
`scalar-exchange/receipt.json`: its exact Python producer owns the projected
inverse. Lean consumes these literal coefficients on the original real CAR
source matrices and proves the concrete candidate selection rule. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.MixedSpectatorScalar61Exchange
open SaturationMonoid.PhysicsCore
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction StageNineDynamicBreakingVacuum
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open QuantizationCheck.Fermion ActiveMatterSectorCharge MixedSpectatorCandidate
open scoped BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

/-- Original lexicographic exterior-coordinate order of the 35 complex directions. -/
def scalarWord (a : Fin 35) : ExteriorBasisIndex 4 :=
  ![⟨{Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr (Sum.inl 0)}, by simp⟩,
    ⟨{Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr (Sum.inl 1)}, by simp⟩,
    ⟨{Sum.inl 0, Sum.inl 1, Sum.inl 2, hyperPlusIndex}, by simp [hyperPlusIndex]⟩,
    ⟨{Sum.inl 0, Sum.inl 1, Sum.inl 2, hyperMinusIndex}, by simp [hyperMinusIndex]⟩,
    ⟨{Sum.inl 0, Sum.inl 1, Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1)}, by simp⟩,
    ⟨{Sum.inl 0, Sum.inl 1, Sum.inr (Sum.inl 0), hyperPlusIndex}, by simp [hyperPlusIndex]⟩,
    ⟨{Sum.inl 0, Sum.inl 1, Sum.inr (Sum.inl 0), hyperMinusIndex}, by simp [hyperMinusIndex]⟩,
    ⟨{Sum.inl 0, Sum.inl 1, Sum.inr (Sum.inl 1), hyperPlusIndex}, by simp [hyperPlusIndex]⟩,
    ⟨{Sum.inl 0, Sum.inl 1, Sum.inr (Sum.inl 1), hyperMinusIndex}, by simp [hyperMinusIndex]⟩,
    ⟨{Sum.inl 0, Sum.inl 1, hyperPlusIndex, hyperMinusIndex}, by simp [hyperPlusIndex, hyperMinusIndex]⟩,
    ⟨{Sum.inl 0, Sum.inl 2, Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1)}, by simp⟩,
    ⟨{Sum.inl 0, Sum.inl 2, Sum.inr (Sum.inl 0), hyperPlusIndex}, by simp [hyperPlusIndex]⟩,
    ⟨{Sum.inl 0, Sum.inl 2, Sum.inr (Sum.inl 0), hyperMinusIndex}, by simp [hyperMinusIndex]⟩,
    ⟨{Sum.inl 0, Sum.inl 2, Sum.inr (Sum.inl 1), hyperPlusIndex}, by simp [hyperPlusIndex]⟩,
    ⟨{Sum.inl 0, Sum.inl 2, Sum.inr (Sum.inl 1), hyperMinusIndex}, by simp [hyperMinusIndex]⟩,
    ⟨{Sum.inl 0, Sum.inl 2, hyperPlusIndex, hyperMinusIndex}, by simp [hyperPlusIndex, hyperMinusIndex]⟩,
    ⟨{Sum.inl 0, Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), hyperPlusIndex}, by simp [hyperPlusIndex]⟩,
    ⟨{Sum.inl 0, Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), hyperMinusIndex}, by simp [hyperMinusIndex]⟩,
    ⟨{Sum.inl 0, Sum.inr (Sum.inl 0), hyperPlusIndex, hyperMinusIndex}, by simp [hyperPlusIndex, hyperMinusIndex]⟩,
    ⟨{Sum.inl 0, Sum.inr (Sum.inl 1), hyperPlusIndex, hyperMinusIndex}, by simp [hyperPlusIndex, hyperMinusIndex]⟩,
    ⟨{Sum.inl 1, Sum.inl 2, Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1)}, by simp⟩,
    ⟨{Sum.inl 1, Sum.inl 2, Sum.inr (Sum.inl 0), hyperPlusIndex}, by simp [hyperPlusIndex]⟩,
    ⟨{Sum.inl 1, Sum.inl 2, Sum.inr (Sum.inl 0), hyperMinusIndex}, by simp [hyperMinusIndex]⟩,
    ⟨{Sum.inl 1, Sum.inl 2, Sum.inr (Sum.inl 1), hyperPlusIndex}, by simp [hyperPlusIndex]⟩,
    ⟨{Sum.inl 1, Sum.inl 2, Sum.inr (Sum.inl 1), hyperMinusIndex}, by simp [hyperMinusIndex]⟩,
    ⟨{Sum.inl 1, Sum.inl 2, hyperPlusIndex, hyperMinusIndex}, by simp [hyperPlusIndex, hyperMinusIndex]⟩,
    ⟨{Sum.inl 1, Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), hyperPlusIndex}, by simp [hyperPlusIndex]⟩,
    ⟨{Sum.inl 1, Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), hyperMinusIndex}, by simp [hyperMinusIndex]⟩,
    ⟨{Sum.inl 1, Sum.inr (Sum.inl 0), hyperPlusIndex, hyperMinusIndex}, by simp [hyperPlusIndex, hyperMinusIndex]⟩,
    ⟨{Sum.inl 1, Sum.inr (Sum.inl 1), hyperPlusIndex, hyperMinusIndex}, by simp [hyperPlusIndex, hyperMinusIndex]⟩,
    ⟨{Sum.inl 2, Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), hyperPlusIndex}, by simp [hyperPlusIndex]⟩,
    ⟨{Sum.inl 2, Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), hyperMinusIndex}, by simp [hyperMinusIndex]⟩,
    ⟨{Sum.inl 2, Sum.inr (Sum.inl 0), hyperPlusIndex, hyperMinusIndex}, by simp [hyperPlusIndex, hyperMinusIndex]⟩,
    ⟨{Sum.inl 2, Sum.inr (Sum.inl 1), hyperPlusIndex, hyperMinusIndex}, by simp [hyperPlusIndex, hyperMinusIndex]⟩,
    ⟨{Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), hyperPlusIndex, hyperMinusIndex}, by simp [hyperPlusIndex, hyperMinusIndex]⟩] a

def scalarIndex (a : Fin 70) : SourceScalarFock.ScalarIndex :=
  (decide (35 ≤ a.val), scalarWord ⟨a.val % 35, Nat.mod_lt _ (by decide)⟩)

def sourceVertex (a : Fin 70) : Matrix Mode Mode ℂ :=
  SourceRealScalarFock.sourceMatrix (scalarIndex a)

def sourceChart (a : Fin 70) : Scalar :=
  scalarCoordinateEquiv (SourceScalarFock.scalarDirection (scalarIndex a))

theorem sourceVertex_original (a : Fin 70) :
    sourceVertex a = GaussYukawaCoefficient.fullMatrix (sourceChart a) := by
  simp only [sourceVertex, SourceRealScalarFock.sourceMatrix, SourceScalarFock.sourceMatrix,
    GaussYukawaCoefficient.fullMatrix, GaussYukawaCoefficient.primal, sourceChart,
    LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_restrictScalars,
    LinearEquiv.symm_apply_apply]
  rfl

def sourceLeg (a : Fin 70) : SourceTreeCombination := [(1, .scalar (sourceChart a), false)]

theorem sourceLeg_original (a : Fin 70) :
    sourceTreeCoherentMatrix (sourceLeg a) = sourceVertex a := by
  simp [sourceLeg, sourceTreeCoherentMatrix, sourceTreeOrientedMatrix,
    sourceTreeMatrix, sourceVertex_original]

/-- Twenty distinct polynomial entries, without a fitted or user-supplied kernel. -/
def numeratorPolynomial (p : Fin 4 → ℂ) (a : Fin 20) : ℂ :=
  ![((5329/5000) + (2 * (p 1 ^ 4)) + (2 * (p 2 ^ 4)) + (2 * (p 3 ^ 4)) + (2 * (p 0 ^ 4)) + ((-73/25) * (p 0 ^ 2)) + ((91/25) * (p 1 ^ 2)) + ((91/25) * (p 2 ^ 2)) + ((91/25) * (p 3 ^ 2)) + ((-4) * (p 1 ^ 2) * (p 0 ^ 2)) + ((-4) * (p 2 ^ 2) * (p 0 ^ 2)) + ((-4) * (p 3 ^ 2) * (p 0 ^ 2)) + (4 * (p 1 ^ 2) * (p 2 ^ 2)) + (4 * (p 1 ^ 2) * (p 3 ^ 2)) + (4 * (p 2 ^ 2) * (p 3 ^ 2))),
    ((-5329/5000) + ((-2) * (p 1 ^ 4)) + ((-2) * (p 2 ^ 4)) + ((-2) * (p 3 ^ 4)) + ((-2) * (p 0 ^ 4)) + ((-91/25) * (p 1 ^ 2)) + ((-91/25) * (p 2 ^ 2)) + ((-91/25) * (p 3 ^ 2)) + ((73/25) * (p 0 ^ 2)) + ((-4) * (p 1 ^ 2) * (p 2 ^ 2)) + ((-4) * (p 1 ^ 2) * (p 3 ^ 2)) + ((-4) * (p 2 ^ 2) * (p 3 ^ 2)) + (4 * (p 1 ^ 2) * (p 0 ^ 2)) + (4 * (p 2 ^ 2) * (p 0 ^ 2)) + (4 * (p 3 ^ 2) * (p 0 ^ 2))),
    ((5329/2500) + (4 * (p 1 ^ 4)) + (4 * (p 2 ^ 4)) + (4 * (p 3 ^ 4)) + (4 * (p 0 ^ 4)) + ((-146/25) * (p 0 ^ 2)) + ((182/25) * (p 1 ^ 2)) + ((182/25) * (p 2 ^ 2)) + ((182/25) * (p 3 ^ 2)) + ((-8) * (p 1 ^ 2) * (p 0 ^ 2)) + ((-8) * (p 2 ^ 2) * (p 0 ^ 2)) + ((-8) * (p 3 ^ 2) * (p 0 ^ 2)) + (8 * (p 1 ^ 2) * (p 2 ^ 2)) + (8 * (p 1 ^ 2) * (p 3 ^ 2)) + (8 * (p 2 ^ 2) * (p 3 ^ 2))),
    ((73/25) + (4 * (p 1 ^ 4)) + (4 * (p 2 ^ 4)) + (4 * (p 3 ^ 4)) + (4 * (p 0 ^ 4)) + ((-173/25) * (p 0 ^ 2)) + ((173/25) * (p 1 ^ 2)) + ((173/25) * (p 2 ^ 2)) + ((173/25) * (p 3 ^ 2)) + ((-8) * (p 1 ^ 2) * (p 0 ^ 2)) + ((-8) * (p 2 ^ 2) * (p 0 ^ 2)) + ((-8) * (p 3 ^ 2) * (p 0 ^ 2)) + (8 * (p 1 ^ 2) * (p 2 ^ 2)) + (8 * (p 1 ^ 2) * (p 3 ^ 2)) + (8 * (p 2 ^ 2) * (p 3 ^ 2))),
    (((-12/5) * p 2) + ((-12/5) * (p 2 ^ 3)) + ((-12/5) * p 2 * (p 1 ^ 2)) + ((-12/5) * p 2 * (p 3 ^ 2)) + ((12/5) * p 2 * (p 0 ^ 2))),
    (((12/5) * p 3) + ((12/5) * (p 3 ^ 3)) + ((-12/5) * p 3 * (p 0 ^ 2)) + ((12/5) * p 3 * (p 1 ^ 2)) + ((12/5) * p 3 * (p 2 ^ 2))),
    (((12/5) * p 1) + ((12/5) * (p 1 ^ 3)) + ((-12/5) * p 1 * (p 0 ^ 2)) + ((12/5) * p 1 * (p 2 ^ 2)) + ((12/5) * p 1 * (p 3 ^ 2))),
    ((73/50) + (2 * (p 1 ^ 4)) + (2 * (p 2 ^ 4)) + (2 * (p 3 ^ 4)) + (2 * (p 0 ^ 4)) + ((-173/50) * (p 0 ^ 2)) + ((173/50) * (p 1 ^ 2)) + ((173/50) * (p 2 ^ 2)) + ((173/50) * (p 3 ^ 2)) + ((-4) * (p 1 ^ 2) * (p 0 ^ 2)) + ((-4) * (p 2 ^ 2) * (p 0 ^ 2)) + ((-4) * (p 3 ^ 2) * (p 0 ^ 2)) + (4 * (p 1 ^ 2) * (p 2 ^ 2)) + (4 * (p 1 ^ 2) * (p 3 ^ 2)) + (4 * (p 2 ^ 2) * (p 3 ^ 2))),
    ((-73/50) + ((-2) * (p 1 ^ 4)) + ((-2) * (p 2 ^ 4)) + ((-2) * (p 3 ^ 4)) + ((-2) * (p 0 ^ 4)) + ((-173/50) * (p 1 ^ 2)) + ((-173/50) * (p 2 ^ 2)) + ((-173/50) * (p 3 ^ 2)) + ((173/50) * (p 0 ^ 2)) + ((-4) * (p 1 ^ 2) * (p 2 ^ 2)) + ((-4) * (p 1 ^ 2) * (p 3 ^ 2)) + ((-4) * (p 2 ^ 2) * (p 3 ^ 2)) + (4 * (p 1 ^ 2) * (p 0 ^ 2)) + (4 * (p 2 ^ 2) * (p 0 ^ 2)) + (4 * (p 3 ^ 2) * (p 0 ^ 2))),
    (((-6/5) * p 2) + ((-6/5) * (p 2 ^ 3)) + ((-6/5) * p 2 * (p 1 ^ 2)) + ((-6/5) * p 2 * (p 3 ^ 2)) + ((6/5) * p 2 * (p 0 ^ 2))),
    (((6/5) * p 2) + ((6/5) * (p 2 ^ 3)) + ((-6/5) * p 2 * (p 0 ^ 2)) + ((6/5) * p 2 * (p 1 ^ 2)) + ((6/5) * p 2 * (p 3 ^ 2))),
    (((6/5) * p 3) + ((6/5) * (p 3 ^ 3)) + ((-6/5) * p 3 * (p 0 ^ 2)) + ((6/5) * p 3 * (p 1 ^ 2)) + ((6/5) * p 3 * (p 2 ^ 2))),
    (((-6/5) * p 3) + ((-6/5) * (p 3 ^ 3)) + ((-6/5) * p 3 * (p 1 ^ 2)) + ((-6/5) * p 3 * (p 2 ^ 2)) + ((6/5) * p 3 * (p 0 ^ 2))),
    (((6/5) * p 1) + ((6/5) * (p 1 ^ 3)) + ((-6/5) * p 1 * (p 0 ^ 2)) + ((6/5) * p 1 * (p 2 ^ 2)) + ((6/5) * p 1 * (p 3 ^ 2))),
    (((-6/5) * p 1) + ((-6/5) * (p 1 ^ 3)) + ((-6/5) * p 1 * (p 2 ^ 2)) + ((-6/5) * p 1 * (p 3 ^ 2)) + ((6/5) * p 1 * (p 0 ^ 2))),
    (((12/5) * p 2) + ((12/5) * (p 2 ^ 3)) + ((-12/5) * p 2 * (p 0 ^ 2)) + ((12/5) * p 2 * (p 1 ^ 2)) + ((12/5) * p 2 * (p 3 ^ 2))),
    (((-12/5) * p 3) + ((-12/5) * (p 3 ^ 3)) + ((-12/5) * p 3 * (p 1 ^ 2)) + ((-12/5) * p 3 * (p 2 ^ 2)) + ((12/5) * p 3 * (p 0 ^ 2))),
    ((5329/10000) + (p 1 ^ 4) + (p 2 ^ 4) + (p 3 ^ 4) + (p 0 ^ 4) + ((-73/50) * (p 0 ^ 2)) + ((91/50) * (p 1 ^ 2)) + ((91/50) * (p 2 ^ 2)) + ((91/50) * (p 3 ^ 2)) + ((-2) * (p 1 ^ 2) * (p 0 ^ 2)) + ((-2) * (p 2 ^ 2) * (p 0 ^ 2)) + ((-2) * (p 3 ^ 2) * (p 0 ^ 2)) + (2 * (p 1 ^ 2) * (p 2 ^ 2)) + (2 * (p 1 ^ 2) * (p 3 ^ 2)) + (2 * (p 2 ^ 2) * (p 3 ^ 2))),
    ((-5329/10000) + ((-1) * (p 1 ^ 4)) + ((-1) * (p 2 ^ 4)) + ((-1) * (p 3 ^ 4)) + ((-1) * (p 0 ^ 4)) + ((-91/50) * (p 1 ^ 2)) + ((-91/50) * (p 2 ^ 2)) + ((-91/50) * (p 3 ^ 2)) + ((73/50) * (p 0 ^ 2)) + ((-2) * (p 1 ^ 2) * (p 2 ^ 2)) + ((-2) * (p 1 ^ 2) * (p 3 ^ 2)) + ((-2) * (p 2 ^ 2) * (p 3 ^ 2)) + (2 * (p 1 ^ 2) * (p 0 ^ 2)) + (2 * (p 2 ^ 2) * (p 0 ^ 2)) + (2 * (p 3 ^ 2) * (p 0 ^ 2))),
    (((-12/5) * p 1) + ((-12/5) * (p 1 ^ 3)) + ((-12/5) * p 1 * (p 2 ^ 2)) + ((-12/5) * p 1 * (p 3 ^ 2)) + ((12/5) * p 1 * (p 0 ^ 2)))] a

/-- The source table has 238 nonzero positions in all 70 real scalar coordinates. -/
def numerator (p : Fin 4 → ℂ) (a b : Fin 70) : ℂ :=
  match a.val, b.val with
  | 0, 0 => numeratorPolynomial p 0
  | 0, 5 => numeratorPolynomial p 1
  | 1, 1 => numeratorPolynomial p 2
  | 2, 2 => numeratorPolynomial p 2
  | 3, 3 => numeratorPolynomial p 2
  | 4, 4 => numeratorPolynomial p 2
  | 5, 0 => numeratorPolynomial p 1
  | 5, 5 => numeratorPolynomial p 0
  | 6, 6 => numeratorPolynomial p 2
  | 7, 7 => numeratorPolynomial p 2
  | 8, 8 => numeratorPolynomial p 2
  | 9, 9 => numeratorPolynomial p 2
  | 10, 10 => numeratorPolynomial p 3
  | 10, 20 => numeratorPolynomial p 4
  | 10, 45 => numeratorPolynomial p 5
  | 10, 55 => numeratorPolynomial p 6
  | 11, 11 => numeratorPolynomial p 3
  | 11, 21 => numeratorPolynomial p 4
  | 11, 46 => numeratorPolynomial p 5
  | 11, 56 => numeratorPolynomial p 6
  | 12, 12 => numeratorPolynomial p 3
  | 12, 22 => numeratorPolynomial p 4
  | 12, 47 => numeratorPolynomial p 5
  | 12, 57 => numeratorPolynomial p 6
  | 13, 13 => numeratorPolynomial p 7
  | 13, 15 => numeratorPolynomial p 8
  | 13, 23 => numeratorPolynomial p 9
  | 13, 25 => numeratorPolynomial p 10
  | 13, 48 => numeratorPolynomial p 11
  | 13, 50 => numeratorPolynomial p 12
  | 13, 58 => numeratorPolynomial p 13
  | 13, 60 => numeratorPolynomial p 14
  | 14, 14 => numeratorPolynomial p 3
  | 14, 24 => numeratorPolynomial p 4
  | 14, 49 => numeratorPolynomial p 5
  | 14, 59 => numeratorPolynomial p 6
  | 15, 13 => numeratorPolynomial p 8
  | 15, 15 => numeratorPolynomial p 7
  | 15, 23 => numeratorPolynomial p 10
  | 15, 25 => numeratorPolynomial p 9
  | 15, 48 => numeratorPolynomial p 12
  | 15, 50 => numeratorPolynomial p 11
  | 15, 58 => numeratorPolynomial p 14
  | 15, 60 => numeratorPolynomial p 13
  | 16, 16 => numeratorPolynomial p 3
  | 16, 26 => numeratorPolynomial p 4
  | 16, 51 => numeratorPolynomial p 5
  | 16, 61 => numeratorPolynomial p 6
  | 17, 17 => numeratorPolynomial p 3
  | 17, 27 => numeratorPolynomial p 4
  | 17, 52 => numeratorPolynomial p 5
  | 17, 62 => numeratorPolynomial p 6
  | 18, 18 => numeratorPolynomial p 3
  | 18, 28 => numeratorPolynomial p 4
  | 18, 53 => numeratorPolynomial p 5
  | 18, 63 => numeratorPolynomial p 6
  | 19, 19 => numeratorPolynomial p 3
  | 19, 29 => numeratorPolynomial p 4
  | 19, 54 => numeratorPolynomial p 5
  | 19, 64 => numeratorPolynomial p 6
  | 20, 10 => numeratorPolynomial p 15
  | 20, 20 => numeratorPolynomial p 3
  | 20, 45 => numeratorPolynomial p 6
  | 20, 55 => numeratorPolynomial p 16
  | 21, 11 => numeratorPolynomial p 15
  | 21, 21 => numeratorPolynomial p 3
  | 21, 46 => numeratorPolynomial p 6
  | 21, 56 => numeratorPolynomial p 16
  | 22, 12 => numeratorPolynomial p 15
  | 22, 22 => numeratorPolynomial p 3
  | 22, 47 => numeratorPolynomial p 6
  | 22, 57 => numeratorPolynomial p 16
  | 23, 13 => numeratorPolynomial p 10
  | 23, 15 => numeratorPolynomial p 9
  | 23, 23 => numeratorPolynomial p 7
  | 23, 25 => numeratorPolynomial p 8
  | 23, 48 => numeratorPolynomial p 13
  | 23, 50 => numeratorPolynomial p 14
  | 23, 58 => numeratorPolynomial p 12
  | 23, 60 => numeratorPolynomial p 11
  | 24, 14 => numeratorPolynomial p 15
  | 24, 24 => numeratorPolynomial p 3
  | 24, 49 => numeratorPolynomial p 6
  | 24, 59 => numeratorPolynomial p 16
  | 25, 13 => numeratorPolynomial p 9
  | 25, 15 => numeratorPolynomial p 10
  | 25, 23 => numeratorPolynomial p 8
  | 25, 25 => numeratorPolynomial p 7
  | 25, 48 => numeratorPolynomial p 14
  | 25, 50 => numeratorPolynomial p 13
  | 25, 58 => numeratorPolynomial p 11
  | 25, 60 => numeratorPolynomial p 12
  | 26, 16 => numeratorPolynomial p 15
  | 26, 26 => numeratorPolynomial p 3
  | 26, 51 => numeratorPolynomial p 6
  | 26, 61 => numeratorPolynomial p 16
  | 27, 17 => numeratorPolynomial p 15
  | 27, 27 => numeratorPolynomial p 3
  | 27, 52 => numeratorPolynomial p 6
  | 27, 62 => numeratorPolynomial p 16
  | 28, 18 => numeratorPolynomial p 15
  | 28, 28 => numeratorPolynomial p 3
  | 28, 53 => numeratorPolynomial p 6
  | 28, 63 => numeratorPolynomial p 16
  | 29, 19 => numeratorPolynomial p 15
  | 29, 29 => numeratorPolynomial p 3
  | 29, 54 => numeratorPolynomial p 6
  | 29, 64 => numeratorPolynomial p 16
  | 30, 30 => numeratorPolynomial p 2
  | 31, 31 => numeratorPolynomial p 2
  | 32, 32 => numeratorPolynomial p 2
  | 33, 33 => numeratorPolynomial p 2
  | 34, 34 => numeratorPolynomial p 2
  | 35, 35 => numeratorPolynomial p 0
  | 35, 40 => numeratorPolynomial p 1
  | 36, 36 => numeratorPolynomial p 17
  | 36, 38 => numeratorPolynomial p 18
  | 36, 42 => numeratorPolynomial p 18
  | 36, 44 => numeratorPolynomial p 17
  | 37, 37 => numeratorPolynomial p 2
  | 38, 36 => numeratorPolynomial p 18
  | 38, 38 => numeratorPolynomial p 17
  | 38, 42 => numeratorPolynomial p 17
  | 38, 44 => numeratorPolynomial p 18
  | 39, 39 => numeratorPolynomial p 2
  | 40, 35 => numeratorPolynomial p 1
  | 40, 40 => numeratorPolynomial p 0
  | 41, 41 => numeratorPolynomial p 2
  | 42, 36 => numeratorPolynomial p 18
  | 42, 38 => numeratorPolynomial p 17
  | 42, 42 => numeratorPolynomial p 17
  | 42, 44 => numeratorPolynomial p 18
  | 43, 43 => numeratorPolynomial p 2
  | 44, 36 => numeratorPolynomial p 17
  | 44, 38 => numeratorPolynomial p 18
  | 44, 42 => numeratorPolynomial p 18
  | 44, 44 => numeratorPolynomial p 17
  | 45, 10 => numeratorPolynomial p 16
  | 45, 20 => numeratorPolynomial p 19
  | 45, 45 => numeratorPolynomial p 3
  | 45, 55 => numeratorPolynomial p 4
  | 46, 11 => numeratorPolynomial p 16
  | 46, 21 => numeratorPolynomial p 19
  | 46, 46 => numeratorPolynomial p 3
  | 46, 56 => numeratorPolynomial p 4
  | 47, 12 => numeratorPolynomial p 16
  | 47, 22 => numeratorPolynomial p 19
  | 47, 47 => numeratorPolynomial p 3
  | 47, 57 => numeratorPolynomial p 4
  | 48, 13 => numeratorPolynomial p 12
  | 48, 15 => numeratorPolynomial p 11
  | 48, 23 => numeratorPolynomial p 14
  | 48, 25 => numeratorPolynomial p 13
  | 48, 48 => numeratorPolynomial p 7
  | 48, 50 => numeratorPolynomial p 8
  | 48, 58 => numeratorPolynomial p 9
  | 48, 60 => numeratorPolynomial p 10
  | 49, 14 => numeratorPolynomial p 16
  | 49, 24 => numeratorPolynomial p 19
  | 49, 49 => numeratorPolynomial p 3
  | 49, 59 => numeratorPolynomial p 4
  | 50, 13 => numeratorPolynomial p 11
  | 50, 15 => numeratorPolynomial p 12
  | 50, 23 => numeratorPolynomial p 13
  | 50, 25 => numeratorPolynomial p 14
  | 50, 48 => numeratorPolynomial p 8
  | 50, 50 => numeratorPolynomial p 7
  | 50, 58 => numeratorPolynomial p 10
  | 50, 60 => numeratorPolynomial p 9
  | 51, 16 => numeratorPolynomial p 16
  | 51, 26 => numeratorPolynomial p 19
  | 51, 51 => numeratorPolynomial p 3
  | 51, 61 => numeratorPolynomial p 4
  | 52, 17 => numeratorPolynomial p 16
  | 52, 27 => numeratorPolynomial p 19
  | 52, 52 => numeratorPolynomial p 3
  | 52, 62 => numeratorPolynomial p 4
  | 53, 18 => numeratorPolynomial p 16
  | 53, 28 => numeratorPolynomial p 19
  | 53, 53 => numeratorPolynomial p 3
  | 53, 63 => numeratorPolynomial p 4
  | 54, 19 => numeratorPolynomial p 16
  | 54, 29 => numeratorPolynomial p 19
  | 54, 54 => numeratorPolynomial p 3
  | 54, 64 => numeratorPolynomial p 4
  | 55, 10 => numeratorPolynomial p 19
  | 55, 20 => numeratorPolynomial p 5
  | 55, 45 => numeratorPolynomial p 15
  | 55, 55 => numeratorPolynomial p 3
  | 56, 11 => numeratorPolynomial p 19
  | 56, 21 => numeratorPolynomial p 5
  | 56, 46 => numeratorPolynomial p 15
  | 56, 56 => numeratorPolynomial p 3
  | 57, 12 => numeratorPolynomial p 19
  | 57, 22 => numeratorPolynomial p 5
  | 57, 47 => numeratorPolynomial p 15
  | 57, 57 => numeratorPolynomial p 3
  | 58, 13 => numeratorPolynomial p 14
  | 58, 15 => numeratorPolynomial p 13
  | 58, 23 => numeratorPolynomial p 11
  | 58, 25 => numeratorPolynomial p 12
  | 58, 48 => numeratorPolynomial p 10
  | 58, 50 => numeratorPolynomial p 9
  | 58, 58 => numeratorPolynomial p 7
  | 58, 60 => numeratorPolynomial p 8
  | 59, 14 => numeratorPolynomial p 19
  | 59, 24 => numeratorPolynomial p 5
  | 59, 49 => numeratorPolynomial p 15
  | 59, 59 => numeratorPolynomial p 3
  | 60, 13 => numeratorPolynomial p 13
  | 60, 15 => numeratorPolynomial p 14
  | 60, 23 => numeratorPolynomial p 12
  | 60, 25 => numeratorPolynomial p 11
  | 60, 48 => numeratorPolynomial p 9
  | 60, 50 => numeratorPolynomial p 10
  | 60, 58 => numeratorPolynomial p 8
  | 60, 60 => numeratorPolynomial p 7
  | 61, 16 => numeratorPolynomial p 19
  | 61, 26 => numeratorPolynomial p 5
  | 61, 51 => numeratorPolynomial p 15
  | 61, 61 => numeratorPolynomial p 3
  | 62, 17 => numeratorPolynomial p 19
  | 62, 27 => numeratorPolynomial p 5
  | 62, 52 => numeratorPolynomial p 15
  | 62, 62 => numeratorPolynomial p 3
  | 63, 18 => numeratorPolynomial p 19
  | 63, 28 => numeratorPolynomial p 5
  | 63, 53 => numeratorPolynomial p 15
  | 63, 63 => numeratorPolynomial p 3
  | 64, 19 => numeratorPolynomial p 19
  | 64, 29 => numeratorPolynomial p 5
  | 64, 54 => numeratorPolynomial p 15
  | 64, 64 => numeratorPolynomial p 3
  | 65, 65 => numeratorPolynomial p 2
  | 66, 66 => numeratorPolynomial p 2
  | 67, 67 => numeratorPolynomial p 2
  | 68, 68 => numeratorPolynomial p 2
  | 69, 69 => numeratorPolynomial p 2
  | _, _ => 0

def denominator (p : Fin 4 → ℂ) : ℂ :=
  (((-15987/31250) * (Real.sqrt 30 : ℂ)) + ((-70587/31250) * (Real.sqrt 30 : ℂ) * (p 1 ^ 2)) + ((-70587/31250) * (Real.sqrt 30 : ℂ) * (p 2 ^ 2)) + ((-70587/31250) * (Real.sqrt 30 : ℂ) * (p 3 ^ 2)) + ((-1692/625) * (Real.sqrt 30 : ℂ) * (p 1 ^ 4)) + ((-1692/625) * (Real.sqrt 30 : ℂ) * (p 2 ^ 4)) + ((-1692/625) * (Real.sqrt 30 : ℂ) * (p 3 ^ 4)) + ((-1476/625) * (Real.sqrt 30 : ℂ) * (p 0 ^ 4)) + ((-24/25) * (Real.sqrt 30 : ℂ) * (p 1 ^ 6)) + ((-24/25) * (Real.sqrt 30 : ℂ) * (p 2 ^ 6)) + ((-24/25) * (Real.sqrt 30 : ℂ) * (p 3 ^ 6)) + ((24/25) * (Real.sqrt 30 : ℂ) * (p 0 ^ 6)) + ((59787/31250) * (Real.sqrt 30 : ℂ) * (p 0 ^ 2)) + ((-3384/625) * (Real.sqrt 30 : ℂ) * (p 1 ^ 2) * (p 2 ^ 2)) + ((-3384/625) * (Real.sqrt 30 : ℂ) * (p 1 ^ 2) * (p 3 ^ 2)) + ((-3384/625) * (Real.sqrt 30 : ℂ) * (p 2 ^ 2) * (p 3 ^ 2)) + ((-72/25) * (Real.sqrt 30 : ℂ) * (p 1 ^ 2) * (p 2 ^ 4)) + ((-72/25) * (Real.sqrt 30 : ℂ) * (p 1 ^ 2) * (p 3 ^ 4)) + ((-72/25) * (Real.sqrt 30 : ℂ) * (p 1 ^ 2) * (p 0 ^ 4)) + ((-72/25) * (Real.sqrt 30 : ℂ) * (p 1 ^ 4) * (p 2 ^ 2)) + ((-72/25) * (Real.sqrt 30 : ℂ) * (p 1 ^ 4) * (p 3 ^ 2)) + ((-72/25) * (Real.sqrt 30 : ℂ) * (p 2 ^ 2) * (p 3 ^ 4)) + ((-72/25) * (Real.sqrt 30 : ℂ) * (p 2 ^ 2) * (p 0 ^ 4)) + ((-72/25) * (Real.sqrt 30 : ℂ) * (p 2 ^ 4) * (p 3 ^ 2)) + ((-72/25) * (Real.sqrt 30 : ℂ) * (p 3 ^ 2) * (p 0 ^ 4)) + ((72/25) * (Real.sqrt 30 : ℂ) * (p 1 ^ 4) * (p 0 ^ 2)) + ((72/25) * (Real.sqrt 30 : ℂ) * (p 2 ^ 4) * (p 0 ^ 2)) + ((72/25) * (Real.sqrt 30 : ℂ) * (p 3 ^ 4) * (p 0 ^ 2)) + ((3168/625) * (Real.sqrt 30 : ℂ) * (p 1 ^ 2) * (p 0 ^ 2)) + ((3168/625) * (Real.sqrt 30 : ℂ) * (p 2 ^ 2) * (p 0 ^ 2)) + ((3168/625) * (Real.sqrt 30 : ℂ) * (p 3 ^ 2) * (p 0 ^ 2)) + ((-144/25) * (Real.sqrt 30 : ℂ) * (p 1 ^ 2) * (p 2 ^ 2) * (p 3 ^ 2)) + ((144/25) * (Real.sqrt 30 : ℂ) * (p 1 ^ 2) * (p 2 ^ 2) * (p 0 ^ 2)) + ((144/25) * (Real.sqrt 30 : ℂ) * (p 1 ^ 2) * (p 3 ^ 2) * (p 0 ^ 2)) + ((144/25) * (Real.sqrt 30 : ℂ) * (p 2 ^ 2) * (p 3 ^ 2) * (p 0 ^ 2)))

def greenCoefficient (p : Fin 4 → ℂ) (a b : Fin 70) : ℂ :=
  numerator p a b / denominator p

/-- The regular domain of the original rational source inverse. -/
abbrev RegularMomentum := {p : Fin 4 → ℂ // denominator p ≠ 0}

/-- Original action coefficient -1/2, with both independent real branches
already retained by SourceRealScalarFock.sourceMatrix. -/
def actualScalar61Tree (p : RegularMomentum) : Module.End ℂ (Fock Mode) :=
  ∑ a : Fin 70, ∑ b : Fin 70,
    ((-1/2 : ℂ) * greenCoefficient p.val a b) •
      LowEnergy.Fermion.normalProduct (sourceVertex a) (sourceVertex b)

theorem actualScalar61Tree_source (p : RegularMomentum) :
    actualScalar61Tree p = sourceCoherentTree (Finset.univ : Finset (Fin 70 × Fin 70))
      (fun ab => (-1/2 : ℂ) * greenCoefficient p.val ab.1 ab.2)
      (fun ab => sourceLeg ab.1) (fun ab => sourceLeg ab.2) := by
  simp only [actualScalar61Tree, sourceCoherentTree, Fintype.sum_prod_type,
    sourceTreeNormalProduct, sourceLeg_original]

/-- Complete original scalar61 exchange, with all four momentum parameters,
to every neutral occupation of the same full504 CAR carrier. -/
theorem actual_scalar61_candidate_neutral (p : RegularMomentum) (dual : Bool)
    (word : Occupation) (neutral : ∑ i ∈ word, modeWeight i = 0) :
    pairing (occupationBasis word)
      (actualScalar61Tree p (fiberCoordinates (candidate dual))) = 0 := by
  rw [actualScalar61Tree_source]
  exact actual_candidate_coherent_tree_selection _ _ _ _ dual word neutral

theorem actual_scalar61_candidate_pure_four (p : RegularMomentum) (dual : Bool)
    (word : Occupation) (pureFour : ∀ i ∈ word, modeWeight i = 0) :
    pairing (occupationBasis word)
      (actualScalar61Tree p (fiberCoordinates (candidate dual))) = 0 :=
  actual_scalar61_candidate_neutral p dual word (Finset.sum_eq_zero fun i hi => pureFour i hi)

end LowEnergy.MixedSpectatorScalar61Exchange
