import H0mework.Versions.AD.Physics.Bell.ReadoutEffects

/-!
# Finite one-step likelihood normalization for the generated Bell law

The denominator is always the original source-generated `effectProbability`. Legal forecasts
generate full-joint, two marginal and parity-conditional likelihood factors. Their fixed mixture
has algebraic source-weighted mean one. Strict source positivity is explicit; no probability table
or source normalization certificate is an input. This finite contract introduces no trial process.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutLikelihood

open ProofFreeRicherAnholonomicSource

noncomputable section

/-- A legal two-outcome statistical forecast. -/
structure BinaryForecast where
  weight : Bool → ℝ
  nonnegative : ∀ x, 0 ≤ weight x
  total : ∑ x : Bool, weight x = 1

/-- A legal four-outcome statistical forecast. -/
structure JointForecast where
  weight : Bool → Bool → ℝ
  nonnegative : ∀ x y, 0 ≤ weight x y
  total : ∑ x : Bool, ∑ y : Bool, weight x y = 1

structure Forecasters where
  full : JointForecast
  first : BinaryForecast
  second : BinaryForecast
  conditional : Bool → BinaryForecast

def leftMass (first second : CompactReadoutEffect) (plus x : Bool) : ℝ :=
  ∑ y : Bool, effectProbability first second plus x y

def rightMass (first second : CompactReadoutEffect) (plus y : Bool) : ℝ :=
  ∑ x : Bool, effectProbability first second plus x y

/-- Source probability of the parity `x xor y`, internally marginalized from the same joint law. -/
def parityMass (first second : CompactReadoutEffect) (plus parity : Bool) : ℝ :=
  ∑ x : Bool, effectProbability first second plus x (Bool.xor x parity)

def sourceMean (first second : CompactReadoutEffect) (plus : Bool)
    (factor : Bool → Bool → ℝ) : ℝ :=
  ∑ x : Bool, ∑ y : Bool, effectProbability first second plus x y * factor x y

def fullFactor (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (x y : Bool) : ℝ :=
  forecast.full.weight x y / effectProbability first second plus x y

def firstFactor (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (x : Bool) : ℝ :=
  forecast.first.weight x / leftMass first second plus x

def secondFactor (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (y : Bool) : ℝ :=
  forecast.second.weight y / rightMass first second plus y

/-- Conditional forecast is indexed by parity first and Alice's outcome second. -/
def conditionalFactor (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (x y : Bool) : ℝ :=
  (forecast.conditional (Bool.xor x y)).weight x /
    (effectProbability first second plus x y / parityMass first second plus (Bool.xor x y))

/-- Weight order: full joint one half, Alice/Bob/conditional each one sixth. -/
def mixtureFactor (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (x y : Bool) : ℝ :=
  fullFactor first second plus forecast x y / 2 +
    firstFactor first second plus forecast x / 6 +
    secondFactor first second plus forecast y / 6 +
    conditionalFactor first second plus forecast x y / 6

theorem left_mass_positive (first second : CompactReadoutEffect) (plus : Bool)
    (positive : ∀ x y, 0 < effectProbability first second plus x y) (x : Bool) :
    0 < leftMass first second plus x := by
  simp [leftMass]
  linarith [positive x false, positive x true]

theorem right_mass_positive (first second : CompactReadoutEffect) (plus : Bool)
    (positive : ∀ x y, 0 < effectProbability first second plus x y) (y : Bool) :
    0 < rightMass first second plus y := by
  simp [rightMass]
  linarith [positive false y, positive true y]

theorem parity_mass_positive (first second : CompactReadoutEffect) (plus : Bool)
    (positive : ∀ x y, 0 < effectProbability first second plus x y) (parity : Bool) :
    0 < parityMass first second plus parity := by
  cases parity <;> simp [parityMass] <;>
    linarith [positive false false, positive false true, positive true false, positive true true]

/-- Parity normalization consumes the already generated source normalization. -/
theorem parity_mass_normalized (first second : CompactReadoutEffect) (plus : Bool) :
    ∑ parity : Bool, parityMass first second plus parity = 1 := by
  simp [parityMass]
  have total := effect_probability_normalized first second plus
  simp at total
  linarith only [total]

theorem full_factor_nonnegative (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (positive : ∀ x y, 0 < effectProbability first second plus x y)
    (x y : Bool) : 0 ≤ fullFactor first second plus forecast x y :=
  div_nonneg (forecast.full.nonnegative x y) (positive x y).le

theorem first_factor_nonnegative (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (positive : ∀ x y, 0 < effectProbability first second plus x y)
    (x : Bool) : 0 ≤ firstFactor first second plus forecast x :=
  div_nonneg (forecast.first.nonnegative x) (left_mass_positive first second plus positive x).le

theorem second_factor_nonnegative (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (positive : ∀ x y, 0 < effectProbability first second plus x y)
    (y : Bool) : 0 ≤ secondFactor first second plus forecast y :=
  div_nonneg (forecast.second.nonnegative y) (right_mass_positive first second plus positive y).le

theorem conditional_factor_nonnegative (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (positive : ∀ x y, 0 < effectProbability first second plus x y)
    (x y : Bool) : 0 ≤ conditionalFactor first second plus forecast x y :=
  div_nonneg ((forecast.conditional (Bool.xor x y)).nonnegative x)
    (div_nonneg (positive x y).le
      (parity_mass_positive first second plus positive (Bool.xor x y)).le)

theorem mixture_factor_nonnegative (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (positive : ∀ x y, 0 < effectProbability first second plus x y)
    (x y : Bool) : 0 ≤ mixtureFactor first second plus forecast x y := by
  have full := full_factor_nonnegative first second plus forecast positive x y
  have firstLocal := first_factor_nonnegative first second plus forecast positive x
  have secondLocal := second_factor_nonnegative first second plus forecast positive y
  have conditional := conditional_factor_nonnegative first second plus forecast positive x y
  dsimp [mixtureFactor]
  positivity

theorem full_factor_mean (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (positive : ∀ x y, 0 < effectProbability first second plus x y) :
    sourceMean first second plus (fullFactor first second plus forecast) = 1 := by
  have cancel : ∀ x y, effectProbability first second plus x y *
      fullFactor first second plus forecast x y = forecast.full.weight x y := by
    intro x y
    dsimp [fullFactor]
    field_simp [ne_of_gt (positive x y)]
  simp only [sourceMean, cancel]
  exact forecast.full.total

theorem first_factor_mean (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (positive : ∀ x y, 0 < effectProbability first second plus x y) :
    sourceMean first second plus (fun x _ => firstFactor first second plus forecast x) = 1 := by
  simp only [sourceMean, firstFactor]
  calc
    (∑ x : Bool, ∑ y : Bool, effectProbability first second plus x y *
        (forecast.first.weight x / leftMass first second plus x)) =
        ∑ x : Bool, leftMass first second plus x *
          (forecast.first.weight x / leftMass first second plus x) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [leftMass, Finset.sum_mul]
    _ = ∑ x : Bool, forecast.first.weight x := by
      apply Finset.sum_congr rfl
      intro x _
      field_simp [ne_of_gt (left_mass_positive first second plus positive x)]
    _ = 1 := forecast.first.total

theorem second_factor_mean (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (positive : ∀ x y, 0 < effectProbability first second plus x y) :
    sourceMean first second plus (fun _ y => secondFactor first second plus forecast y) = 1 := by
  simp only [sourceMean, secondFactor]
  calc
    (∑ x : Bool, ∑ y : Bool, effectProbability first second plus x y *
        (forecast.second.weight y / rightMass first second plus y)) =
        ∑ y : Bool, rightMass first second plus y *
          (forecast.second.weight y / rightMass first second plus y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      simp only [rightMass, Finset.sum_mul]
    _ = ∑ y : Bool, forecast.second.weight y := by
      apply Finset.sum_congr rfl
      intro y _
      field_simp [ne_of_gt (right_mass_positive first second plus positive y)]
    _ = 1 := forecast.second.total

theorem sum_parity_reindex (f : Bool → Bool → ℝ) :
    (∑ x : Bool, ∑ y : Bool, f (Bool.xor x y) x) =
      ∑ parity : Bool, ∑ x : Bool, f parity x := by
  simp
  ring

theorem conditional_factor_cancel (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (positive : ∀ x y, 0 < effectProbability first second plus x y)
    (x y : Bool) : effectProbability first second plus x y *
      conditionalFactor first second plus forecast x y =
        parityMass first second plus (Bool.xor x y) *
          (forecast.conditional (Bool.xor x y)).weight x := by
  dsimp [conditionalFactor]
  field_simp [ne_of_gt (positive x y),
    ne_of_gt (parity_mass_positive first second plus positive (Bool.xor x y))]

theorem conditional_factor_mean (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (positive : ∀ x y, 0 < effectProbability first second plus x y) :
    sourceMean first second plus (conditionalFactor first second plus forecast) = 1 := by
  simp only [sourceMean, conditional_factor_cancel first second plus forecast positive]
  rw [sum_parity_reindex (fun parity x => parityMass first second plus parity *
    (forecast.conditional parity).weight x)]
  calc
    (∑ parity : Bool, ∑ x : Bool, parityMass first second plus parity *
        (forecast.conditional parity).weight x) = ∑ parity : Bool,
          parityMass first second plus parity := by
      apply Finset.sum_congr rfl
      intro parity _
      rw [← Finset.mul_sum, (forecast.conditional parity).total, mul_one]
    _ = 1 := parity_mass_normalized first second plus

theorem mixture_factor_mean (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (positive : ∀ x y, 0 < effectProbability first second plus x y) :
    sourceMean first second plus (mixtureFactor first second plus forecast) = 1 := by
  simp only [sourceMean, mixtureFactor, mul_add, ← mul_div_assoc,
    Finset.sum_add_distrib, ← Finset.sum_div]
  change sourceMean first second plus (fullFactor first second plus forecast) / 2 +
    sourceMean first second plus (fun x _ => firstFactor first second plus forecast x) / 6 +
    sourceMean first second plus (fun _ y => secondFactor first second plus forecast y) / 6 +
    sourceMean first second plus (conditionalFactor first second plus forecast) / 6 = 1
  rw [full_factor_mean first second plus forecast positive,
    first_factor_mean first second plus forecast positive,
    second_factor_mean first second plus forecast positive,
    conditional_factor_mean first second plus forecast positive]
  norm_num

theorem mixture_source_mean (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (positive : ∀ x y, 0 < effectProbability first second plus x y)
    (point : BasePoint) :
    (∑ x : Bool, ∑ y : Bool, effectSourceWeight first second plus point x y *
      mixtureFactor first second plus forecast x y) = 1 := by
  simp only [effect_source_probability]
  exact mixture_factor_mean first second plus forecast positive

theorem mixture_runtime_mean (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (positive : ∀ x y, 0 < effectProbability first second plus x y)
    (point : BasePoint) :
    (∑ x : Bool, ∑ y : Bool, effectRuntimeProbability first second plus point x y *
      mixtureFactor first second plus forecast x y) = 1 := by
  simp only [effect_runtime_probability]
  exact mixture_factor_mean first second plus forecast positive

theorem mixture_next_mean (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (positive : ∀ x y, 0 < effectProbability first second plus x y)
    (point : BasePoint) :
    (∑ x : Bool, ∑ y : Bool, effectNextProbability first second plus point x y *
      mixtureFactor first second plus forecast x y) = 1 := by
  simp only [effect_next_probability]
  exact mixture_factor_mean first second plus forecast positive

/-- Generated binary Jeffreys forecast with one half added to each past count. -/
def binaryJeffreysProbability (counts : Bool → ℕ) (x : Bool) : ℝ :=
  ((counts x : ℝ) + 1 / 2) / ((∑ outcome : Bool, (counts outcome : ℝ)) + 1)

theorem binary_jeffreys_denominator_positive (counts : Bool → ℕ) :
    0 < (∑ outcome : Bool, (counts outcome : ℝ)) + 1 := by
  have nonnegative : 0 ≤ ∑ outcome : Bool, (counts outcome : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  linarith only [nonnegative]

theorem binary_jeffreys_positive (counts : Bool → ℕ) (x : Bool) :
    0 < binaryJeffreysProbability counts x :=
  div_pos (by positivity) (binary_jeffreys_denominator_positive counts)

theorem binary_jeffreys_normalized (counts : Bool → ℕ) :
    ∑ x : Bool, binaryJeffreysProbability counts x = 1 := by
  simp only [binaryJeffreysProbability]
  rw [← Finset.sum_div]
  have numerator : (∑ x : Bool, ((counts x : ℝ) + 1 / 2)) =
      (∑ x : Bool, (counts x : ℝ)) + 1 := by simp; ring
  rw [numerator, div_self (ne_of_gt (binary_jeffreys_denominator_positive counts))]

def BinaryForecast.jeffreys (counts : Bool → ℕ) : BinaryForecast where
  weight := binaryJeffreysProbability counts
  nonnegative := fun x => (binary_jeffreys_positive counts x).le
  total := binary_jeffreys_normalized counts

/-- Generated four-outcome Jeffreys forecast with one half added to each past joint count. -/
def jointJeffreysProbability (counts : Bool → Bool → ℕ) (x y : Bool) : ℝ :=
  ((counts x y : ℝ) + 1 / 2) / ((∑ a : Bool, ∑ b : Bool, (counts a b : ℝ)) + 2)

theorem joint_jeffreys_denominator_positive (counts : Bool → Bool → ℕ) :
    0 < (∑ a : Bool, ∑ b : Bool, (counts a b : ℝ)) + 2 := by
  have nonnegative : 0 ≤ ∑ a : Bool, ∑ b : Bool, (counts a b : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  linarith only [nonnegative]

theorem joint_jeffreys_positive (counts : Bool → Bool → ℕ) (x y : Bool) :
    0 < jointJeffreysProbability counts x y :=
  div_pos (by positivity) (joint_jeffreys_denominator_positive counts)

theorem joint_jeffreys_normalized (counts : Bool → Bool → ℕ) :
    ∑ x : Bool, ∑ y : Bool, jointJeffreysProbability counts x y = 1 := by
  simp only [jointJeffreysProbability, ← Finset.sum_div]
  have numerator : (∑ x : Bool, ∑ y : Bool, ((counts x y : ℝ) + 1 / 2)) =
      (∑ x : Bool, ∑ y : Bool, (counts x y : ℝ)) + 2 := by simp; ring
  rw [numerator, div_self (ne_of_gt (joint_jeffreys_denominator_positive counts))]

def JointForecast.jeffreys (counts : Bool → Bool → ℕ) : JointForecast where
  weight := jointJeffreysProbability counts
  nonnegative := fun x y => (joint_jeffreys_positive counts x y).le
  total := joint_jeffreys_normalized counts

/-- Natural counts generate all legal forecasts for the statistical consumer. -/
def jeffreysForecasters (jointCounts : Bool → Bool → ℕ)
    (firstCounts secondCounts : Bool → ℕ) (conditionalCounts : Bool → Bool → ℕ) : Forecasters where
  full := JointForecast.jeffreys jointCounts
  first := BinaryForecast.jeffreys firstCounts
  second := BinaryForecast.jeffreys secondCounts
  conditional := fun parity => BinaryForecast.jeffreys (conditionalCounts parity)

/-- The finite normalization contract, indexed by the source parameters and legal forecasts. -/
structure OneStepNormalizer (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) : Prop where
  sourcePrediction : SameOccurrenceReadoutEffectPrediction
  sourceTotal : ∑ x : Bool, ∑ y : Bool, effectProbability first second plus x y = 1
  leftPositive : ∀ x, 0 < leftMass first second plus x
  rightPositive : ∀ y, 0 < rightMass first second plus y
  parityPositive : ∀ parity, 0 < parityMass first second plus parity
  parityTotal : ∑ parity : Bool, parityMass first second plus parity = 1
  fullMean : sourceMean first second plus (fullFactor first second plus forecast) = 1
  firstMean : sourceMean first second plus
    (fun x _ => firstFactor first second plus forecast x) = 1
  secondMean : sourceMean first second plus
    (fun _ y => secondFactor first second plus forecast y) = 1
  conditionalMean : sourceMean first second plus (conditionalFactor first second plus forecast) = 1
  mixturePositive : ∀ x y, 0 ≤ mixtureFactor first second plus forecast x y
  mixtureMean : sourceMean first second plus (mixtureFactor first second plus forecast) = 1
  sourceMeanAt : ∀ point, (∑ x : Bool, ∑ y : Bool,
    effectSourceWeight first second plus point x y * mixtureFactor first second plus forecast x y) = 1
  currentMeanAt : ∀ point, (∑ x : Bool, ∑ y : Bool,
    effectRuntimeProbability first second plus point x y *
      mixtureFactor first second plus forecast x y) = 1
  nextMeanAt : ∀ point, (∑ x : Bool, ∑ y : Bool,
    effectNextProbability first second plus point x y * mixtureFactor first second plus forecast x y) = 1

/-- Positive-interior one-step consumer of the exact generated source, not a trial-law premise. -/
theorem oneStepNormalizer (first second : CompactReadoutEffect) (plus : Bool)
    (forecast : Forecasters) (positive : ∀ x y, 0 < effectProbability first second plus x y) :
    OneStepNormalizer first second plus forecast :=
  { sourcePrediction := sameOccurrenceReadoutEffectPrediction
    sourceTotal := effect_probability_normalized first second plus
    leftPositive := left_mass_positive first second plus positive
    rightPositive := right_mass_positive first second plus positive
    parityPositive := parity_mass_positive first second plus positive
    parityTotal := parity_mass_normalized first second plus
    fullMean := full_factor_mean first second plus forecast positive
    firstMean := first_factor_mean first second plus forecast positive
    secondMean := second_factor_mean first second plus forecast positive
    conditionalMean := conditional_factor_mean first second plus forecast positive
    mixturePositive := mixture_factor_nonnegative first second plus forecast positive
    mixtureMean := mixture_factor_mean first second plus forecast positive
    sourceMeanAt := mixture_source_mean first second plus forecast positive
    currentMeanAt := mixture_runtime_mean first second plus forecast positive
    nextMeanAt := mixture_next_mean first second plus forecast positive }

end
end SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutLikelihood
