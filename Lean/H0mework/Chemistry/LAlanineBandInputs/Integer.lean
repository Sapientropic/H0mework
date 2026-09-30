import H0mework.Chemistry.LAlanineBandInputs.Common
import H0mework.Chemistry.LAlanineContinuousMatrix.IntegerGrid

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGeneratedInputs

open SourceSignedEvaluator SourceExponential SourceRectangle WholeBandSource WholeBandSaturation
open Lean Elab Term Command Inertia.SourceParsing

abbrev IntegerPair := Int × Int

elab "generateInputAlphaIntegers" : command => liftTermElabM do
  let some (.defnInfo info) := (← getEnv).find? ``rawExponents | throwError "original exponent data"
  let some rows ← Meta.getArrayLit? info.value | throwError "original exponent literals"
  unless info.safety == .safe && rows.size == 94 do throwError "original exponent census"
  let mut values : Array Int := #[]
  for row in rows do
    unless row.isAppOfArity ``Prod.mk 4 do throwError "source exponent pair"
    let some numerator ← Meta.getIntValue? row.getAppArgs[2]! | throwError "source exponent numerator"
    let some denominator ← Meta.getNatValue? row.getAppArgs[3]! | throwError "source exponent denominator"
    unless denominator > 0 do throwError "positive source exponent denominator"
    values := values.push ⌊scale * ((numerator : ℚ) / denominator)⌋
  WholeCellSource.declareSource `rawAlphaIntegers (toExpr values)

generateInputAlphaIntegers

noncomputable def alphaInteger (g : Group) : Int := rawAlphaIntegers[g.val]!

theorem alpha_point_exact (g : Group) :
    point (groupAlpha g) = integerInterval (alphaInteger g, alphaInteger g) := by
  fin_cases g <;> decide +kernel

def integerScale (n : Int) (a : IntegerPair) : IntegerPair :=
  (min (n*a.1) (n*a.2) / SourceIntegerGrid.denominator,
    -((-max (n*a.1) (n*a.2)) / SourceIntegerGrid.denominator))

theorem integerScale_commutes (n : Int) (a : IntegerPair) :
    integerInterval (integerScale n a) =
      mul (integerInterval (n,n)) (integerInterval a) := by
  have product (z : Int) : ((n : ℚ) / scale) * ((z : ℚ) / scale) = ((n*z : Int) : ℚ) / scale^2 := by
    push_cast
    ring
  simp only [mul, lowerCorner, upperCorner, integerInterval, product, min_self, max_self]
  rw [min_div_div_right (sq_nonneg scale), max_div_div_right (sq_nonneg scale),
    ← Int.cast_min, ← Int.cast_max,
    SourceIntegerGrid.roundDown_square_grid, SourceIntegerGrid.roundUp_square_grid]
  rfl

noncomputable def integerRadial (radii : Atom → IntegerPair) (g : Group) : IntegerPair :=
  integerScale (-alphaInteger g) (radii (groupAtom g))

theorem sharedRadial_integer (radii : Atom → IntegerPair) (g : Group) :
    sharedRadial (fun a => integerInterval (radii a)) g = integerInterval (integerRadial radii g) := by
  rw [sharedRadial, alpha_point_exact]
  have negative : neg (integerInterval (alphaInteger g, alphaInteger g)) =
      integerInterval (-alphaInteger g, -alphaInteger g) := by
    simp only [neg, integerInterval, Int.cast_neg, neg_div]
  rw [negative, ← integerScale_commutes]
  rfl

def reductionDenominator (k : Nat) : Int := (SourceIntegerGrid.denominator : Int) * 2^k

theorem reductionDenominator_positive (k : Nat) : 0 < reductionDenominator k := by
  unfold reductionDenominator SourceIntegerGrid.denominator
  positivity

theorem reductionDenominator_cast (k : Nat) :
    (reductionDenominator k : ℚ) = scale * 2^k := by
  simp only [reductionDenominator, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat,
    SourceIntegerGrid.denominator_cast]

theorem reduced_small_of_integer (n : Int) (k : Nat)
    (bound : 2*|n| ≤ reductionDenominator k) :
    |reducedArgument ((n : ℚ) / scale) k| ≤ 1/2 := by
  have positive : (0 : ℚ) < reductionDenominator k := by
    exact_mod_cast reductionDenominator_positive k
  have castBound : (2 : ℚ) * |(n : ℚ)| ≤ (reductionDenominator k : ℚ) := by exact_mod_cast bound
  rw [reducedArgument, div_div, ← reductionDenominator_cast, abs_div, abs_of_pos positive]
  apply (div_le_div_iff₀ positive (by norm_num : (0 : ℚ) < 2)).mpr
  simpa only [one_mul, mul_comm] using castBound

theorem reduced_upper_of_integer (n : Int) (k m : Nat) (mPositive : 0 < m)
    (bound : (m : Int)*n ≤ -7*reductionDenominator k) :
    reducedArgument ((n : ℚ) / scale) k ≤ (-7 : ℚ)/m := by
  have positive : (0 : ℚ) < reductionDenominator k := by
    exact_mod_cast reductionDenominator_positive k
  have denominatorPositive : (0 : ℚ) < m := by exact_mod_cast mPositive
  have castBound : (m : ℚ) * (n : ℚ) ≤ -7*(reductionDenominator k : ℚ) := by exact_mod_cast bound
  rw [reducedArgument, div_div, ← reductionDenominator_cast]
  apply (div_le_div_iff₀ positive denominatorPositive).mpr
  simpa only [mul_comm] using castBound

def IntegerReductions (a : IntegerPair) (r : Nat × Nat) : Prop :=
  2*|a.1| ≤ reductionDenominator r.1 ∧ 2*|a.2| ≤ reductionDenominator r.2

def IntegerSaturation (a : IntegerPair) (r : Nat × Nat) : Prop :=
  IntegerReductions a r ∧
  ((r.1 = 8 ∧ 16*a.1 ≤ -7*reductionDenominator r.1) ∨
    (9 ≤ r.1 ∧ 32*a.1 ≤ -7*reductionDenominator r.1)) ∧
  ((r.2 = 8 ∧ 16*a.2 ≤ -7*reductionDenominator r.2) ∨
    (9 ≤ r.2 ∧ 32*a.2 ≤ -7*reductionDenominator r.2))

instance (a : IntegerPair) (r : Nat × Nat) : Decidable (IntegerReductions a r) := by
  unfold IntegerReductions
  infer_instance

instance (a : IntegerPair) (r : Nat × Nat) : Decidable (IntegerSaturation a r) := by
  unfold IntegerSaturation
  infer_instance

theorem integerReductions_sound (a : IntegerPair) (r : Nat × Nat) (h : IntegerReductions a r) :
    ReductionConditions (integerInterval a) r :=
  ⟨reduced_small_of_integer a.1 r.1 h.1, reduced_small_of_integer a.2 r.2 h.2⟩

theorem integerSaturation_sound (a : IntegerPair) (r : Nat × Nat) (h : IntegerSaturation a r) :
    SaturationConditions (integerInterval a) r := by
  refine ⟨integerReductions_sound a r h.1, ?_, ?_⟩
  · rcases h.2.1 with ⟨eight, bound⟩ | ⟨later, bound⟩
    · exact Or.inl ⟨eight, reduced_upper_of_integer a.1 r.1 16 (by decide) bound⟩
    · exact Or.inr ⟨later, reduced_upper_of_integer a.1 r.1 32 (by decide) bound⟩
  · rcases h.2.2 with ⟨eight, bound⟩ | ⟨later, bound⟩
    · exact Or.inl ⟨eight, reduced_upper_of_integer a.2 r.2 16 (by decide) bound⟩
    · exact Or.inr ⟨later, reduced_upper_of_integer a.2 r.2 32 (by decide) bound⟩

end LAlanine40K2025.BasinRefinement.WholeBandGeneratedInputs
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
