import H0mework.Physics.Bell.Herald

import H0mework.Physics.RootRuntime.RecoveryConsumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell

open Matrix Stage9DEF State
open Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource
open StageNineExteriorMotherLieRepresentation StageNineHolonomicField
open SU7ExteriorMatterGaugeCovariantJet SU7MotherLieAlgebra SU7ExteriorMatterRepresentation
open scoped Kronecker ComplexOrder

noncomputable section

def rawPreparedVector (plus : Bool) (field : Source.OccupiedField)
    (point : BasePoint) : Source.Index → ℂ :=
  if plus then right 0 1 *ᵥ field point else field point

def runtimeProbability (plus : Bool) (point : BasePoint) (a b : Axis) (x y : Bool) : ℝ :=
  (vectorEvaluation (rawPreparedVector plus Runtime.tick.answer point)
    (outcomeEffect a b x y).matrix).re

def nextProbability (plus : Bool) (point : BasePoint) (a b : Axis) (x y : Bool) : ℝ :=
  (vectorEvaluation (rawPreparedVector plus Runtime.nextTick.answer point)
    (outcomeEffect a b x y).matrix).re

theorem runtime_probability (plus : Bool) (point : BasePoint) (a b : Axis) (x y : Bool) :
    runtimeProbability plus point a b x y = probability a (heraldAxis plus b) x y := by
  rw [runtimeProbability, Runtime.tick_vector]
  exact herald_probability plus point a b x y

theorem next_probability (plus : Bool) (point : BasePoint) (a b : Axis) (x y : Bool) :
    nextProbability plus point a b x y = probability a (heraldAxis plus b) x y := by
  rw [nextProbability, Runtime.nextTick_vector]
  exact herald_probability plus point a b x y

structure SameOccurrenceBellPrediction : Prop where
  earlier : Nonempty Recovery.StageOneThroughTenClosure
  activation : Runtime.SameOccurrenceActivation
  colorGenerated : ∀ x z, right x z = (-2 * Complex.I) •
    ((x : ℂ) • Algebra.colorAction 0 + (z : ℂ) • Algebra.colorAction 2)
  motherGenerated : ∀ direction row column,
    Algebra.colorAction direction row column =
      if row.1 = column.1 then sourceColorDoubletDual row.2
        (exteriorSpinorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction))
          (sourceColorDoubletMatter column.2)) else 0
  spinGenerated : ∀ x z, spinAxis x z = (-Complex.I) •
    ((x : ℂ) • spinRotation 0 + (z : ℂ) • spinRotation 2)
  commutes : ∀ ax az bx bz, left ax az * right bx bz = right bx bz * left ax az
  normalized : ∀ plus point,
    (∑ i, star (preparedVector plus point i) * preparedVector plus point i) = 1
  currentBorn : ∀ plus point a b x y,
    runtimeProbability plus point a b x y = probability a (heraldAxis plus b) x y
  nextBorn : ∀ plus point a b x y,
    nextProbability plus point a b x y = probability a (heraldAxis plus b) x y
  total : ∀ a b, ∑ x : Bool, ∑ y : Bool, probability a b x y = 1
  positive : ∀ a b x y, 0 ≤ probability a b x y
  bounded : ∀ a b x y, probability a b x y ≤ 1
  leftMarginal : ∀ a b x, ∑ y : Bool, probability a b x y = 1 / 2
  rightMarginal : ∀ a b y, ∑ x : Bool, probability a b x y = 1 / 2

theorem sameOccurrenceBellPrediction : SameOccurrenceBellPrediction :=
  { earlier := ⟨Recovery.stageOneThroughTenClosure⟩
    activation := Runtime.sameOccurrenceActivation
    colorGenerated := right_from_mother
    motherGenerated := Algebra.colorAction_from_mother
    spinGenerated := spinAxis_from_clifford
    commutes := joint_commutes
    normalized := preparedVector_normalized
    currentBorn := runtime_probability
    nextBorn := next_probability
    total := probability_normalized
    positive := probability_nonnegative
    bounded := probability_le_one
    leftMarginal := probability_left_marginal
    rightMarginal := probability_right_marginal }


end
end SaturationMonoid.PhysicsCore.Stage10.Bell
