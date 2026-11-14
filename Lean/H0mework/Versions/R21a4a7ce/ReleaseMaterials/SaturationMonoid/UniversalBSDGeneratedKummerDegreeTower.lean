import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDGeneratedKummerOddDegree

/-!
# Full degree tower for the generated Kummer ladder
-/

open scoped Polynomial

noncomputable section

namespace SaturationMonoid.UniversalBSDGeneratedKummerLadder

variable {R : Type*} [CommRing R]

/-- Degree/leading-coefficient data for two adjacent generated levels. -/
def KummerAdjacentDegreeData (n : ℕ) (P : KummerAdjacent R) : Prop :=
  KummerDegreeData n P.1 ∧ KummerDegreeData (n + 1) P.2

/-- A nonzero binary ladder step preserves the adjacent degree contract. -/
theorem KummerAdjacentDegreeData.step [IsDomain R] [CharZero R]
    (W : WeierstrassCurve R) {n : ℕ} {P : KummerAdjacent R}
    (hn : n ≠ 0) (hP : KummerAdjacentDegreeData n P) (bit : Bool) :
    KummerAdjacentDegreeData (Nat.bit bit n) (kummerAdjacentStep W bit P) := by
  rcases hP with ⟨hP₀, hP₁⟩
  have hdouble₀ := hP₀.double W hn
  have hodd := hP₀.odd W hP₁ hn
  have hn1 : n + 1 ≠ 0 := Nat.succ_ne_zero n
  have hdouble₁ := hP₁.double W hn1
  cases bit
  · simpa [KummerAdjacentDegreeData, kummerAdjacentStep, Nat.bit] using
      And.intro hdouble₀ hodd
  · have hindex : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    simpa [KummerAdjacentDegreeData, kummerAdjacentStep, Nat.bit, hindex] using
      And.intro hodd hdouble₁

@[simp]
theorem generatedKummerAdjacent_degree_zero [IsDomain R] [CharZero R]
    (W : WeierstrassCurve R) :
    KummerAdjacentDegreeData 0 (generatedKummerAdjacent W 0) := by
  simp [KummerAdjacentDegreeData]

@[simp]
theorem generatedKummerAdjacent_degree_one [IsDomain R] [CharZero R]
    (W : WeierstrassCurve R) :
    KummerAdjacentDegreeData 1 (generatedKummerAdjacent W 1) := by
  rw [show 1 = Nat.bit true 0 by rfl, generatedKummerAdjacent_bit]
  have hdouble := KummerDegreeData.double W
    (kummerDegreeData_identity (R := R)) one_ne_zero
  simpa [KummerAdjacentDegreeData, kummerAdjacentStep] using
    And.intro (kummerDegreeData_identity (R := R)) hdouble

/-- Every generated adjacent pair carries the exact reciprocal degree normalization. -/
theorem generatedKummerAdjacent_degree [IsDomain R] [CharZero R]
    (W : WeierstrassCurve R) (n : ℕ) :
    KummerAdjacentDegreeData n (generatedKummerAdjacent W n) := by
  induction n using Nat.binaryRecFromOne with
  | zero => exact generatedKummerAdjacent_degree_zero W
  | one => exact generatedKummerAdjacent_degree_one W
  | bit bit n hn ih =>
      rw [generatedKummerAdjacent_bit]
      exact ih.step W hn bit

/-- Final all-level degree/leading-coefficient mouth for the first projection. -/
theorem generatedKummerXZ_degree [IsDomain R] [CharZero R]
    (W : WeierstrassCurve R) (n : ℕ) :
    KummerDegreeData n (generatedKummerXZ W n) :=
  (generatedKummerAdjacent_degree W n).1

end SaturationMonoid.UniversalBSDGeneratedKummerLadder
