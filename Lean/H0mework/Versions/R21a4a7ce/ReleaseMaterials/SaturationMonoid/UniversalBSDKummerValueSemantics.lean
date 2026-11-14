import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDWeierstrassAddSubMapFullSemantics

/-!
# Value-level Kummer multiplication semantics

This file turns the full projective `addSubMap` theorem into scale-stable x-coordinate
doubling and differential-addition producers.  Polynomial ladders can consume these
mouths after proving their evaluation commutes with the value operations.
-/

noncomputable section

open scoped WeierstrassCurve.Projective

namespace SaturationMonoid.UniversalBSDKummerValueSemantics

open MvPolynomial
open WeierstrassCurve
open WeierstrassCurve.Affine
open SaturationMonoid.UniversalBSDWeierstrassAddSubMapFullSemantics

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- A field-valued homogeneous Kummer x-coordinate. -/
abbrev KummerValue (K : Type*) [Field K] := Fin 2 → K

/-- The symmetric-square projective triple attached to two homogeneous x-pairs. -/
def kummerSym2 (P Q : KummerValue K) : Fin 3 → K :=
  ![P 0 * Q 0, P 0 * Q 1 + P 1 * Q 0, P 1 * Q 1]

/-- Embed a homogeneous x-pair as the symmetric pair with infinity. -/
def kummerEmbed (P : KummerValue K) : Fin 3 → K := ![P 0, P 1, 0]

/-- Value-level homogeneous doubling, read from the first two coordinates of `addSubMap`. -/
noncomputable def kummerDoubleValue (P : KummerValue K) : KummerValue K :=
  ![(W.addSubMap 0).eval (kummerSym2 P P),
    (W.addSubMap 1).eval (kummerSym2 P P)]

/-- Recover the unknown x-coordinate from `sym2x(R,-Q)` when `x(Q)=x`. -/
def kummerExtractAt (x : K) (T : Fin 3 → K) : KummerValue K :=
  ![T 1 - x * T 2, T 2]

/-- Value-level differential addition with a fixed affine base x-coordinate. -/
noncomputable def kummerOddValue (x : K) (P Q : KummerValue K) : KummerValue K :=
  kummerExtractAt x (fun i => (W.addSubMap i).eval (kummerSym2 P Q))

/-- A homogeneous pair represents the actual x-coordinate of a point up to a unit scale. -/
def Represents (P : KummerValue K) (Q : W.toAffine.Point) : Prop :=
  ∃ u : Kˣ, P = (u : K) • Q.xRep

/-- Two value pairs representing adjacent scalar multiples of one actual base point. -/
def AdjacentRepresents [DecidableEq K] (base : W.toAffine.Point) (n : ℕ)
    (P : KummerValue K × KummerValue K) : Prop :=
  Represents W P.1 (n • base) ∧ Represents W P.2 ((n + 1) • base)

/-- Recover an explicit unit scale from equality in the projective quotient. -/
theorem exists_unit_smul_of_pointClass_eq {P Q : Fin 3 → K}
    (h : (⟦P⟧ : WeierstrassCurve.Projective.PointClass K) = ⟦Q⟧) :
    ∃ u : Kˣ, P = (u : K) • Q := by
  rcases Quotient.exact h with ⟨u, hu⟩
  exact ⟨u, hu.symm⟩

@[simp]
theorem kummerSym2_xRep (P Q : W.toAffine.Point) :
    kummerSym2 P.xRep Q.xRep = P.sym2x Q := by
  rcases P with (_ | ⟨x₁, y₁, h₁⟩) <;>
    rcases Q with (_ | ⟨x₂, y₂, h₂⟩) <;>
    simp [kummerSym2, WeierstrassCurve.Affine.Point.xRep,
      WeierstrassCurve.Affine.Point.sym2x]

@[simp]
theorem kummerEmbed_xRep (P : W.toAffine.Point) :
    kummerEmbed P.xRep = P.sym2x 0 := by
  rcases P with (_ | ⟨x, y, h⟩) <;>
    simp [kummerEmbed, WeierstrassCurve.Affine.Point.xRep,
      WeierstrassCurve.Affine.Point.sym2x]

/-- Symmetric-square coordinates are bilinear in the two homogeneous pairs. -/
theorem kummerSym2_smul (a b : K) (P Q : KummerValue K) :
    kummerSym2 (a • P) (b • Q) = (a * b) • kummerSym2 P Q := by
  funext i
  fin_cases i <;> simp [kummerSym2] <;> ring

/-- `addSubMap` is quadratic under scalar rescaling of its projective input. -/
theorem addSubMap_eval_smul (a : K) (T : Fin 3 → K) :
    (fun i => (W.addSubMap i).eval (a • T)) =
      a ^ 2 • (fun i => (W.addSubMap i).eval T) := by
  funext i
  fin_cases i <;> simp [WeierstrassCurve.addSubMap] <;> ring

/-- The embedded value-level double is exactly `addSubMap` on the diagonal
symmetric-square triple. -/
theorem kummerEmbed_doubleValue (P : KummerValue K) :
    kummerEmbed (kummerDoubleValue W P) =
      (fun i => (W.addSubMap i).eval (kummerSym2 P P)) := by
  funext i
  fin_cases i <;>
    simp [kummerEmbed, kummerDoubleValue, kummerSym2,
      WeierstrassCurve.addSubMap]
  all_goals ring

/-- Homogeneity of the value-level double. -/
theorem kummerDoubleValue_smul (a : K) (P : KummerValue K) :
    kummerDoubleValue W (a • P) = a ^ 4 • kummerDoubleValue W P := by
  funext i
  fin_cases i <;>
    simp [kummerDoubleValue, kummerSym2, WeierstrassCurve.addSubMap] <;>
    ring

/-- Extraction is linear in the symmetric-square triple. -/
theorem kummerExtractAt_smul (x a : K) (T : Fin 3 → K) :
    kummerExtractAt x (a • T) = a • kummerExtractAt x T := by
  funext i
  fin_cases i <;> simp [kummerExtractAt]
  all_goals ring

/-- Bihomogeneity of differential addition. -/
theorem kummerOddValue_smul (x a b : K) (P Q : KummerValue K) :
    kummerOddValue W x (a • P) (b • Q) =
      (a * b) ^ 2 • kummerOddValue W x P Q := by
  unfold kummerOddValue
  rw [kummerSym2_smul, addSubMap_eval_smul, kummerExtractAt_smul]

/-- Extraction from an actual pair `(R,-Q)` returns exactly `xRep R`. -/
theorem kummerExtractAt_sym2x_neg_base
    {x y : K} (h : W.toAffine.Nonsingular x y) (R : W.toAffine.Point) :
    kummerExtractAt x
      (R.sym2x (-WeierstrassCurve.Affine.Point.some x y h)) = R.xRep := by
  rcases R with (_ | ⟨r, s, hr⟩) <;>
    simp [kummerExtractAt, WeierstrassCurve.Affine.Point.xRep,
      WeierstrassCurve.Affine.Point.sym2x]

@[simp]
theorem represents_xRep (P : W.toAffine.Point) : Represents W P.xRep P := by
  exact ⟨1, by simp⟩

/-- Canonical actual doubling is represented by the value-level Kummer double,
including infinity and two-torsion. -/
theorem kummerDoubleValue_represents_xRep [DecidableEq K] [W.IsElliptic]
    (P : W.toAffine.Point) :
    Represents W (kummerDoubleValue W P.xRep) (P + P) := by
  have hproj := addSubMap_sym2x_projective W P P
  rcases exists_unit_smul_of_pointClass_eq hproj with ⟨u, hu⟩
  have heq3 : kummerEmbed (kummerDoubleValue W P.xRep) =
      (u : K) • kummerEmbed (P + P).xRep := by
    calc
      kummerEmbed (kummerDoubleValue W P.xRep) =
          (fun i => (W.addSubMap i).eval (kummerSym2 P.xRep P.xRep)) :=
        kummerEmbed_doubleValue W P.xRep
      _ = (fun i => (W.addSubMap i).eval (P.sym2x P)) := by
        rw [kummerSym2_xRep]
      _ = (u : K) • ((P + P).sym2x (P - P)) := hu
      _ = (u : K) • kummerEmbed (P + P).xRep := by
        rw [sub_self, kummerEmbed_xRep]
  refine ⟨u, ?_⟩
  funext i
  fin_cases i
  · simpa [kummerEmbed] using congrFun heq3 0
  · simpa [kummerEmbed] using congrFun heq3 1

/-- Doubling preserves actual representability for every homogeneous input scale. -/
theorem represents_kummerDoubleValue
    [DecidableEq K] [W.IsElliptic]
    {V : KummerValue K} {P : W.toAffine.Point}
    (hV : Represents W V P) :
    Represents W (kummerDoubleValue W V) (P + P) := by
  rcases hV with ⟨u, rfl⟩
  rcases kummerDoubleValue_represents_xRep W P with ⟨v, hv⟩
  refine ⟨u ^ 4 * v, ?_⟩
  rw [kummerDoubleValue_smul, hv]
  simp [smul_smul]

/-- Canonical differential addition represents `P+Q` whenever the other output
of the same occurrence is the negative fixed affine base point. -/
theorem kummerOddValue_represents_xRep
    [DecidableEq K] [W.IsElliptic]
    {x y : K} (hbase : W.toAffine.Nonsingular x y)
    (P Q : W.toAffine.Point)
    (hdiff : P - Q = -WeierstrassCurve.Affine.Point.some x y hbase) :
    Represents W (kummerOddValue W x P.xRep Q.xRep) (P + Q) := by
  have hproj := addSubMap_sym2x_projective W P Q
  rcases exists_unit_smul_of_pointClass_eq hproj with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  unfold kummerOddValue
  rw [kummerSym2_xRep, hu, kummerExtractAt_smul, hdiff,
    kummerExtractAt_sym2x_neg_base]

/-- Differential addition preserves representability under arbitrary unit scales. -/
theorem represents_kummerOddValue
    [DecidableEq K] [W.IsElliptic]
    {x y : K} (hbase : W.toAffine.Nonsingular x y)
    {V U : KummerValue K} {P Q : W.toAffine.Point}
    (hV : Represents W V P) (hU : Represents W U Q)
    (hdiff : P - Q = -WeierstrassCurve.Affine.Point.some x y hbase) :
    Represents W (kummerOddValue W x V U) (P + Q) := by
  rcases hV with ⟨a, rfl⟩
  rcases hU with ⟨b, rfl⟩
  rcases kummerOddValue_represents_xRep W hbase P Q hdiff with ⟨u, hu⟩
  refine ⟨(a * b) ^ 2 * u, ?_⟩
  rw [kummerOddValue_smul, hu]
  simp [smul_smul]

/-- One value-level binary ladder step. -/
noncomputable def kummerAdjacentValueStep (x : K) (bit : Bool)
    (P : KummerValue K × KummerValue K) : KummerValue K × KummerValue K :=
  let even := kummerDoubleValue W P.1
  let odd := kummerOddValue W x P.1 P.2
  let nextEven := kummerDoubleValue W P.2
  if bit then (odd, nextEven) else (even, odd)

/-- The binary step preserves the actual adjacent-multiple occurrence. -/
theorem adjacentRepresents_step
    [DecidableEq K] [W.IsElliptic]
    {x y : K} (hbase : W.toAffine.Nonsingular x y)
    (bit : Bool) (n : ℕ) (P : KummerValue K × KummerValue K)
    (hP : AdjacentRepresents W
      (WeierstrassCurve.Affine.Point.some x y hbase) n P) :
    AdjacentRepresents W (WeierstrassCurve.Affine.Point.some x y hbase)
      (Nat.bit bit n) (kummerAdjacentValueStep W x bit P) := by
  let base : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x y hbase
  rcases hP with ⟨hP₀, hP₁⟩
  have hdiff : n • base - (n + 1) • base = -base := by
    rw [add_nsmul, one_nsmul]
    abel
  have hdouble₀ := represents_kummerDoubleValue W hP₀
  have hodd₀ := represents_kummerOddValue W hbase hP₀ hP₁ hdiff
  have hdouble₁ := represents_kummerDoubleValue W hP₁
  have heven : n • base + n • base = (2 * n) • base := by
    calc
      n • base + n • base = 2 • (n • base) := (two_nsmul (n • base)).symm
      _ = (n * 2) • base := (mul_nsmul base n 2).symm
      _ = (2 * n) • base := by rw [Nat.mul_comm]
  have hodd : n • base + (n + 1) • base = (2 * n + 1) • base := by
    rw [← add_nsmul]
    congr 1
    omega
  have hnext : (n + 1) • base + (n + 1) • base = (2 * n + 2) • base := by
    calc
      (n + 1) • base + (n + 1) • base = 2 • ((n + 1) • base) :=
        (two_nsmul ((n + 1) • base)).symm
      _ = ((n + 1) * 2) • base := (mul_nsmul base (n + 1) 2).symm
      _ = (2 * (n + 1)) • base := by rw [Nat.mul_comm]
      _ = (2 * n + 2) • base := by congr 1
  have hdouble : Represents W (kummerDoubleValue W P.1) ((2 * n) • base) := by
    rw [← heven]
    exact hdouble₀
  have hodd' : Represents W (kummerOddValue W x P.1 P.2)
      ((2 * n + 1) • base) := by
    rw [← hodd]
    exact hodd₀
  have hnext' : Represents W (kummerDoubleValue W P.2) ((2 * n + 2) • base) := by
    rw [← hnext]
    exact hdouble₁
  cases bit
  · simpa [AdjacentRepresents, kummerAdjacentValueStep, Nat.bit, base] using
      And.intro hdouble hodd'
  · simpa [AdjacentRepresents, kummerAdjacentValueStep, Nat.bit, base] using
      And.intro hodd' hnext'

/-- Value-level infinity and generic affine identity representatives. -/
def kummerInfinityValue : KummerValue K := ![1, 0]

def kummerIdentityValue (x : K) : KummerValue K := ![x, 1]

@[simp]
theorem kummerDoubleValue_infinity :
    kummerDoubleValue W (kummerInfinityValue : KummerValue K) = kummerInfinityValue := by
  funext i
  fin_cases i <;>
    simp [kummerDoubleValue, kummerInfinityValue, kummerSym2,
      WeierstrassCurve.addSubMap]

@[simp]
theorem kummerOddValue_infinity_identity (x : K) :
    kummerOddValue W x (kummerInfinityValue : KummerValue K)
      (kummerIdentityValue x) = kummerIdentityValue x := by
  funext i
  fin_cases i <;>
    simp [kummerOddValue, kummerExtractAt, kummerInfinityValue,
      kummerIdentityValue, kummerSym2, WeierstrassCurve.addSubMap]
  all_goals ring

@[simp]
theorem kummerAdjacentValueStep_false_zero (x : K) :
    kummerAdjacentValueStep W x false
      ((kummerInfinityValue : KummerValue K), kummerIdentityValue x) =
        ((kummerInfinityValue : KummerValue K), kummerIdentityValue x) := by
  simp [kummerAdjacentValueStep]

/-- Source-generated value-level representatives for `(nP,(n+1)P)`. -/
noncomputable def generatedKummerAdjacentValue (x : K) :
    ℕ → KummerValue K × KummerValue K :=
  Nat.binaryRec
    ((kummerInfinityValue : KummerValue K), kummerIdentityValue x)
    (fun bit _ P => kummerAdjacentValueStep W x bit P)

@[simp]
theorem generatedKummerAdjacentValue_zero (x : K) :
    generatedKummerAdjacentValue W x 0 =
      ((kummerInfinityValue : KummerValue K), kummerIdentityValue x) := rfl

theorem generatedKummerAdjacentValue_bit (x : K) (bit : Bool) (n : ℕ) :
    generatedKummerAdjacentValue W x (Nat.bit bit n) =
      kummerAdjacentValueStep W x bit (generatedKummerAdjacentValue W x n) := by
  unfold generatedKummerAdjacentValue
  rw [Nat.binaryRec_eq bit n (Or.inl (kummerAdjacentValueStep_false_zero W x))]

/-- The generated value ladder represents every adjacent pair of actual multiples. -/
theorem generatedKummerAdjacentValue_represents
    [DecidableEq K] [W.IsElliptic]
    {x y : K} (hbase : W.toAffine.Nonsingular x y) (n : ℕ) :
    AdjacentRepresents W (WeierstrassCurve.Affine.Point.some x y hbase) n
      (generatedKummerAdjacentValue W x n) := by
  induction n using Nat.binaryRec with
  | zero =>
      refine ⟨?_, ?_⟩
      · refine ⟨1, ?_⟩
        simp [kummerInfinityValue, WeierstrassCurve.Affine.Point.xRep]
      · refine ⟨1, ?_⟩
        simp [kummerIdentityValue, WeierstrassCurve.Affine.Point.xRep]
  | bit bit n ih =>
      rw [generatedKummerAdjacentValue_bit]
      exact adjacentRepresents_step W hbase bit n _ ih

/-- The first projection is the generated x-representative for `[n]P`. -/
noncomputable def generatedKummerValue (x : K) (n : ℕ) : KummerValue K :=
  (generatedKummerAdjacentValue W x n).1

/-- Final value-level actual multiplication mouth. -/
theorem generatedKummerValue_represents
    [DecidableEq K] [W.IsElliptic]
    {x y : K} (hbase : W.toAffine.Nonsingular x y) (n : ℕ) :
    Represents W (generatedKummerValue W x n)
      (n • WeierstrassCurve.Affine.Point.some x y hbase) :=
  (generatedKummerAdjacentValue_represents W hbase n).1

end SaturationMonoid.UniversalBSDKummerValueSemantics
