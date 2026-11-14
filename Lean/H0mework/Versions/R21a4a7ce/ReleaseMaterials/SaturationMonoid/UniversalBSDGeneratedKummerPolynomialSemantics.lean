import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDGeneratedKummerLadder
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDKummerValueSemantics

/-!
# Evaluation semantics of the generated polynomial Kummer ladder

Polynomial evaluation commutes with every binary ladder operation, so the generated polynomial
pair is an actual homogeneous x-coordinate representative of scalar multiplication.
-/

open scoped Polynomial

noncomputable section

namespace SaturationMonoid.UniversalBSDGeneratedKummerPolynomialSemantics

open Polynomial
open SaturationMonoid.UniversalBSDGeneratedKummerLadder
open SaturationMonoid.UniversalBSDKummerValueSemantics

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- Evaluate a polynomial homogeneous x-pair at one affine x-coordinate. -/
def evalKummerXZ (x : K) (P : KummerXZ K) : KummerValue K :=
  ![P.1.eval x, P.2.eval x]

/-- Evaluate an adjacent polynomial pair componentwise. -/
def evalKummerAdjacent (x : K) (P : KummerAdjacent K) :
    KummerValue K × KummerValue K :=
  (evalKummerXZ x P.1, evalKummerXZ x P.2)

@[simp]
theorem evalKummerXZ_infinity (x : K) :
    evalKummerXZ x (kummerInfinity : KummerXZ K) = kummerInfinityValue := by
  funext i
  fin_cases i <;> simp [evalKummerXZ, kummerInfinity, kummerInfinityValue]

@[simp]
theorem evalKummerXZ_identity (x : K) :
    evalKummerXZ x (kummerIdentity : KummerXZ K) = kummerIdentityValue x := by
  funext i
  fin_cases i <;> simp [evalKummerXZ, kummerIdentity, kummerIdentityValue]

/-- Polynomial doubling evaluates to value-level Kummer doubling. -/
theorem evalKummerXZ_double (x : K) (P : KummerXZ K) :
    evalKummerXZ x (kummerDouble W P) =
      kummerDoubleValue W (evalKummerXZ x P) := by
  funext i
  fin_cases i <;>
    simp [evalKummerXZ, kummerDouble, kummerDoubleValue, kummerSym2,
      WeierstrassCurve.addSubMap] <;>
    ring

/-- Polynomial differential addition evaluates to the value-level odd step. -/
theorem evalKummerXZ_odd (x : K) (P Q : KummerXZ K) :
    evalKummerXZ x (kummerOdd W P Q) =
      kummerOddValue W x (evalKummerXZ x P) (evalKummerXZ x Q) := by
  funext i
  fin_cases i <;>
    simp [evalKummerXZ, kummerOdd, kummerOddValue, kummerExtractAt,
      kummerSym2, WeierstrassCurve.addSubMap]

/-- Evaluation commutes with one complete adjacent binary step. -/
theorem evalKummerAdjacent_step (x : K) (bit : Bool) (P : KummerAdjacent K) :
    evalKummerAdjacent x (kummerAdjacentStep W bit P) =
      kummerAdjacentValueStep W x bit (evalKummerAdjacent x P) := by
  cases bit <;>
    simp [evalKummerAdjacent, kummerAdjacentStep, kummerAdjacentValueStep,
      evalKummerXZ_double, evalKummerXZ_odd]

/-- Evaluation of the source-generated polynomial pair is exactly the value ladder. -/
theorem eval_generatedKummerAdjacent (x : K) (n : ℕ) :
    evalKummerAdjacent x (generatedKummerAdjacent W n) =
      generatedKummerAdjacentValue W x n := by
  induction n using Nat.binaryRec with
  | zero => simp [evalKummerAdjacent]
  | bit bit n ih =>
      rw [generatedKummerAdjacent_bit, generatedKummerAdjacentValue_bit,
        evalKummerAdjacent_step, ih]

/-- The evaluated first projection agrees with the generated value representative. -/
theorem eval_generatedKummerXZ (x : K) (n : ℕ) :
    evalKummerXZ x (generatedKummerXZ W n) = generatedKummerValue W x n := by
  unfold generatedKummerXZ generatedKummerValue
  have h := congrArg Prod.fst (eval_generatedKummerAdjacent W x n)
  simpa [evalKummerAdjacent] using h

/-- Final polynomial actual-multiplication mouth. -/
theorem generatedKummerXZ_eval_represents
    [DecidableEq K] [W.IsElliptic]
    {x y : K} (hbase : W.toAffine.Nonsingular x y) (n : ℕ) :
    Represents W (evalKummerXZ x (generatedKummerXZ W n))
      (n • WeierstrassCurve.Affine.Point.some x y hbase) := by
  rw [eval_generatedKummerXZ]
  exact generatedKummerValue_represents W hbase n

end SaturationMonoid.UniversalBSDGeneratedKummerPolynomialSemantics
