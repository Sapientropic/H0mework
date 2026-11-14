import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Tactic.ComputeDegree

/-!
# Source-generated binary Kummer multiplication ladder

This module replaces the missing global Ward-identity layer by a binary Kummer ladder built
directly from the actual duplication and addition-and-subtraction polynomial maps.  Its output is
a pair of univariate homogeneous x-coordinate representatives for adjacent scalar multiples.
-/

open scoped Polynomial

noncomputable section

namespace SaturationMonoid.UniversalBSDGeneratedKummerLadder

open Polynomial

variable {R : Type*} [CommRing R]

/-- A homogeneous x-coordinate representative `(X : Z)`. -/
abbrev KummerXZ (R : Type*) [CommRing R] := Polynomial R × Polynomial R

/-- Representatives for two adjacent scalar multiples. -/
abbrev KummerAdjacent (R : Type*) [CommRing R] := KummerXZ R × KummerXZ R

/-- The point at infinity in Kummer x-coordinates. -/
noncomputable def kummerInfinity : KummerXZ R := (1, 0)

/-- The generic affine point in Kummer x-coordinates. -/
noncomputable def kummerIdentity : KummerXZ R := (X, 1)

/-- The homogeneous level-two x-coordinate map. -/
noncomputable def kummerDouble (W : WeierstrassCurve R) (P : KummerXZ R) : KummerXZ R :=
  (P.1 ^ 4 - C W.b₄ * P.1 ^ 2 * P.2 ^ 2 - C (2 * W.b₆) * P.1 * P.2 ^ 3 -
      C W.b₈ * P.2 ^ 4,
    C 4 * P.1 ^ 3 * P.2 + C W.b₂ * P.1 ^ 2 * P.2 ^ 2 +
      C (2 * W.b₄) * P.1 * P.2 ^ 3 + C W.b₆ * P.2 ^ 4)

/-- The odd differential-addition step.  For adjacent inputs representing `mP` and `(m+1)P`,
the output represents `(2m+1)P`; the known second output of `addSubMap` is `P` itself. -/
noncomputable def kummerOdd (W : WeierstrassCurve R)
    (P Q : KummerXZ R) : KummerXZ R :=
  let A := P.1 * Q.1
  let B := P.1 * Q.2 + P.2 * Q.1
  let C₀ := P.2 * Q.2
  let Z₀ := B ^ 2 - C 4 * A * C₀
  let T₀ := C 2 * B * A + C W.b₂ * A * C₀ + C W.b₄ * B * C₀ +
    C W.b₆ * C₀ ^ 2
  (T₀ - X * Z₀, Z₀)

/-- One binary Montgomery-ladder step on an adjacent pair. -/
noncomputable def kummerAdjacentStep (W : WeierstrassCurve R) (bit : Bool)
    (P : KummerAdjacent R) : KummerAdjacent R :=
  let even := kummerDouble W P.1
  let odd := kummerOdd W P.1 P.2
  let nextEven := kummerDouble W P.2
  if bit then (odd, nextEven) else (even, odd)

@[simp]
theorem kummerDouble_infinity (W : WeierstrassCurve R) :
    kummerDouble W (kummerInfinity : KummerXZ R) = kummerInfinity := by
  simp [kummerDouble, kummerInfinity]

@[simp]
theorem kummerOdd_infinity_identity (W : WeierstrassCurve R) :
    kummerOdd W (kummerInfinity : KummerXZ R) kummerIdentity = kummerIdentity := by
  simp [kummerOdd, kummerInfinity, kummerIdentity]
  change (2 : Polynomial R) * X - X = X
  ring

@[simp]
theorem kummerAdjacentStep_false_zero (W : WeierstrassCurve R) :
    kummerAdjacentStep W false
      ((kummerInfinity : KummerXZ R), kummerIdentity) =
        ((kummerInfinity : KummerXZ R), kummerIdentity) := by
  simp [kummerAdjacentStep]

/-- The generated representatives for `(nP,(n+1)P)`, defined by binary recursion. -/
noncomputable def generatedKummerAdjacent (W : WeierstrassCurve R) :
    ℕ → KummerAdjacent R :=
  Nat.binaryRec ((kummerInfinity : KummerXZ R), kummerIdentity)
    (fun bit _ P => kummerAdjacentStep W bit P)

/-- The generated x-coordinate representative for `nP`. -/
noncomputable def generatedKummerXZ (W : WeierstrassCurve R) (n : ℕ) : KummerXZ R :=
  (generatedKummerAdjacent W n).1

@[simp]
theorem generatedKummerAdjacent_zero (W : WeierstrassCurve R) :
    generatedKummerAdjacent W 0 =
      ((kummerInfinity : KummerXZ R), kummerIdentity) := rfl

theorem generatedKummerAdjacent_bit (W : WeierstrassCurve R) (bit : Bool) (n : ℕ) :
    generatedKummerAdjacent W (Nat.bit bit n) =
      kummerAdjacentStep W bit (generatedKummerAdjacent W n) := by
  unfold generatedKummerAdjacent
  rw [Nat.binaryRec_eq bit n (Or.inl (kummerAdjacentStep_false_zero W))]

@[simp]
theorem generatedKummerXZ_zero (W : WeierstrassCurve R) :
    generatedKummerXZ W 0 = kummerInfinity := rfl

@[simp]
theorem generatedKummerXZ_one (W : WeierstrassCurve R) :
    generatedKummerXZ W 1 = kummerIdentity := by
  rw [show 1 = Nat.bit true 0 by rfl, generatedKummerXZ,
    generatedKummerAdjacent_bit]
  simp [kummerAdjacentStep, kummerOdd, kummerInfinity, kummerIdentity, kummerDouble]
  change (2 : Polynomial R) * X - X = X
  ring

/-! ## Degree and leading-coefficient contract -/

/-- The exact infinity-normalized degree contract needed by reciprocal Hensel lifting. -/
structure KummerDegreeData (n : ℕ) (P : KummerXZ R) : Prop where
  numerator_degree : P.1.natDegree ≤ n ^ 2
  numerator_leading : P.1.coeff (n ^ 2) = 1
  denominator_degree : P.2.natDegree ≤ n ^ 2 - 1
  denominator_leading : P.2.coeff (n ^ 2 - 1) = (n : R) ^ 2

@[simp]
theorem kummerDegreeData_infinity :
    KummerDegreeData 0 (kummerInfinity : KummerXZ R) := by
  constructor <;> simp [kummerInfinity]

@[simp]
theorem kummerDegreeData_identity :
    KummerDegreeData 1 (kummerIdentity : KummerXZ R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [kummerIdentity] using (Polynomial.natDegree_X_le : (X : Polynomial R).natDegree ≤ 1)
  · simp [kummerIdentity]
  · simp [kummerIdentity]
  · simp [kummerIdentity]

theorem KummerDegreeData.double [IsDomain R] [CharZero R]
    (W : WeierstrassCurve R) {n : ℕ} {P : KummerXZ R}
    (h : KummerDegreeData n P) (hn : n ≠ 0) :
    KummerDegreeData (2 * n) (kummerDouble W P) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hsqpos : 0 < n ^ 2 := pow_pos hnpos 2
  have hncast : (n : R) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnumDegree : P.1.natDegree = n ^ 2 :=
    natDegree_eq_of_le_of_coeff_ne_zero h.numerator_degree
      (h.numerator_leading.trans_ne one_ne_zero)
  have hdenDegree : P.2.natDegree = n ^ 2 - 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero h.denominator_degree
      (h.denominator_leading.trans_ne (pow_ne_zero 2 hncast))
  have hnumLC : P.1.leadingCoeff = 1 := by
    rw [leadingCoeff, hnumDegree, h.numerator_leading]
  have hdenLC : P.2.leadingCoeff = (n : R) ^ 2 := by
    rw [leadingCoeff, hdenDegree, h.denominator_leading]
  have hdoubleSq : (2 * n) ^ 2 = 4 * n ^ 2 := by ring
  have hpredLt : n ^ 2 - 1 < n ^ 2 := Nat.sub_lt hsqpos Nat.zero_lt_one
  have hnumLower₂ : 4 * n ^ 2 ≠ 2 * n ^ 2 + 2 * (n ^ 2 - 1) := by omega
  have hnumLower₃ : 4 * n ^ 2 ≠ n ^ 2 + 3 * (n ^ 2 - 1) := by omega
  have hdenTop : 4 * n ^ 2 - 1 = 3 * n ^ 2 + (n ^ 2 - 1) := by omega
  constructor
  · dsimp only [kummerDouble]
    simp only [hdoubleSq]
    compute_degree
    all_goals omega
  · dsimp only [kummerDouble]
    simp only [hdoubleSq]
    compute_degree
    · simp [hnumDegree, hdenDegree, hnumLC, hdenLC, hnumLower₂, hnumLower₃]
      omega
    all_goals omega
  · dsimp only [kummerDouble]
    simp only [hdoubleSq]
    compute_degree
    all_goals omega
  · dsimp only [kummerDouble]
    simp only [hdoubleSq]
    compute_degree
    · simp [hnumDegree, hdenDegree, hnumLC, hdenLC, hdenTop]
      split_ifs <;> try omega
      ring
    all_goals omega

end SaturationMonoid.UniversalBSDGeneratedKummerLadder
