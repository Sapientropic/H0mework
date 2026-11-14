import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDGeneratedKummerLadder

/-!
# Odd leading-term contract for the generated Kummer ladder
-/

open scoped Polynomial

noncomputable section

namespace SaturationMonoid.UniversalBSDGeneratedKummerLadder

open Polynomial

variable {R : Type*} [CommRing R]

theorem KummerDegreeData.odd [IsDomain R] [CharZero R]
    (W : WeierstrassCurve R) {n : ℕ} {P Q : KummerXZ R}
    (hP : KummerDegreeData n P) (hQ : KummerDegreeData (n + 1) Q)
    (hn : n ≠ 0) :
    KummerDegreeData (2 * n + 1) (kummerOdd W P Q) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hn1pos : 0 < n + 1 := Nat.zero_lt_succ n
  have hdpos : 0 < n ^ 2 := pow_pos hnpos 2
  have hepos : 0 < (n + 1) ^ 2 := pow_pos hn1pos 2
  have hncast : (n : R) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hn1cast : ((n + 1 : ℕ) : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hPXDegree : P.1.natDegree = n ^ 2 :=
    natDegree_eq_of_le_of_coeff_ne_zero hP.numerator_degree
      (hP.numerator_leading.trans_ne one_ne_zero)
  have hPZDegree : P.2.natDegree = n ^ 2 - 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero hP.denominator_degree
      (hP.denominator_leading.trans_ne (pow_ne_zero 2 hncast))
  have hQXDegree : Q.1.natDegree = (n + 1) ^ 2 :=
    natDegree_eq_of_le_of_coeff_ne_zero hQ.numerator_degree
      (hQ.numerator_leading.trans_ne one_ne_zero)
  have hQZDegree : Q.2.natDegree = (n + 1) ^ 2 - 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero hQ.denominator_degree
      (hQ.denominator_leading.trans_ne (pow_ne_zero 2 hn1cast))
  have hPXLC : P.1.leadingCoeff = 1 := by
    rw [leadingCoeff, hPXDegree, hP.numerator_leading]
  have hPZLC : P.2.leadingCoeff = (n : R) ^ 2 := by
    rw [leadingCoeff, hPZDegree, hP.denominator_leading]
  have hQXLC : Q.1.leadingCoeff = 1 := by
    rw [leadingCoeff, hQXDegree, hQ.numerator_leading]
  have hQZLC : Q.2.leadingCoeff = ((n + 1 : ℕ) : R) ^ 2 := by
    rw [leadingCoeff, hQZDegree, hQ.denominator_leading]
  have hPXne : P.1 ≠ 0 := leadingCoeff_ne_zero.mp
    (hPXLC.trans_ne one_ne_zero)
  have hPZne : P.2 ≠ 0 := leadingCoeff_ne_zero.mp
    (hPZLC.trans_ne (pow_ne_zero 2 hncast))
  have hQXne : Q.1 ≠ 0 := leadingCoeff_ne_zero.mp
    (hQXLC.trans_ne one_ne_zero)
  have hQZne : Q.2 ≠ 0 := leadingCoeff_ne_zero.mp
    (hQZLC.trans_ne (pow_ne_zero 2 hn1cast))
  let A : R[X] := P.1 * Q.1
  let B : R[X] := P.1 * Q.2 + P.2 * Q.1
  let C₀ : R[X] := P.2 * Q.2
  let Z₀ : R[X] := B ^ 2 - C 4 * A * C₀
  let T₀ : R[X] := C 2 * B * A + C W.b₂ * A * C₀ + C W.b₄ * B * C₀ +
    C W.b₆ * C₀ ^ 2
  have hleftDegree : n ^ 2 + ((n + 1) ^ 2 - 1) = n ^ 2 + (n + 1) ^ 2 - 1 := by
    omega
  have hrightDegree : (n ^ 2 - 1) + (n + 1) ^ 2 = n ^ 2 + (n + 1) ^ 2 - 1 := by
    omega
  have hALeading : A.leadingCoeff = 1 := by
    simp [A, hPXLC, hQXLC]
  have hADegree : A.natDegree = n ^ 2 + (n + 1) ^ 2 := by
    dsimp only [A]
    rw [natDegree_mul hPXne hQXne, hPXDegree, hQXDegree]
  have hBLeftDegree : (P.1 * Q.2).natDegree = n ^ 2 + (n + 1) ^ 2 - 1 := by
    rw [natDegree_mul hPXne hQZne, hPXDegree, hQZDegree, hleftDegree]
  have hBRightDegree : (P.2 * Q.1).natDegree = n ^ 2 + (n + 1) ^ 2 - 1 := by
    rw [natDegree_mul hPZne hQXne, hPZDegree, hQXDegree, hrightDegree]
  have hBcoeff : B.coeff (n ^ 2 + (n + 1) ^ 2 - 1) =
      (n : R) ^ 2 + ((n + 1 : ℕ) : R) ^ 2 := by
    have hleftcoeff : (P.1 * Q.2).coeff (n ^ 2 + (n + 1) ^ 2 - 1) =
        (P.1 * Q.2).leadingCoeff := by rw [← hBLeftDegree, coeff_natDegree]
    have hrightcoeff : (P.2 * Q.1).coeff (n ^ 2 + (n + 1) ^ 2 - 1) =
        (P.2 * Q.1).leadingCoeff := by rw [← hBRightDegree, coeff_natDegree]
    dsimp only [B]
    rw [coeff_add, hleftcoeff, hrightcoeff]
    simp [hPXLC, hPZLC, hQXLC, hQZLC]
    ring
  have hBcoeff_ne : B.coeff (n ^ 2 + (n + 1) ^ 2 - 1) ≠ 0 := by
    rw [hBcoeff]
    norm_cast
    omega
  have hBdegree_le : B.natDegree ≤ n ^ 2 + (n + 1) ^ 2 - 1 := by
    dsimp only [B]
    calc
      (P.1 * Q.2 + P.2 * Q.1).natDegree ≤
          max (P.1 * Q.2).natDegree (P.2 * Q.1).natDegree := natDegree_add_le _ _
      _ = n ^ 2 + (n + 1) ^ 2 - 1 := by rw [hBLeftDegree, hBRightDegree, max_self]
  have hBDegree : B.natDegree = n ^ 2 + (n + 1) ^ 2 - 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero hBdegree_le hBcoeff_ne
  have hBLeading : B.leadingCoeff = (n : R) ^ 2 + ((n + 1 : ℕ) : R) ^ 2 := by
    rw [leadingCoeff, hBDegree, hBcoeff]
  have hCLeading : C₀.leadingCoeff = (n : R) ^ 2 * ((n + 1 : ℕ) : R) ^ 2 := by
    simp [C₀, hPZLC, hQZLC]
  have hCDegree : C₀.natDegree = n ^ 2 + (n + 1) ^ 2 - 2 := by
    have harith : (n ^ 2 - 1) + ((n + 1) ^ 2 - 1) =
        n ^ 2 + (n + 1) ^ 2 - 2 := by
      have hdone : 1 ≤ n ^ 2 := hdpos
      have heone : 1 ≤ (n + 1) ^ 2 := hepos
      omega
    dsimp only [C₀]
    rw [natDegree_mul hPZne hQZne, hPZDegree, hQZDegree]
    exact harith
  have hoddDegree : (2 * n + 1) ^ 2 = 2 * (n ^ 2 + (n + 1) ^ 2) - 1 := by
    have hle : 1 ≤ 2 * (n ^ 2 + (n + 1) ^ 2) := by omega
    symm
    apply (Nat.sub_eq_iff_eq_add' hle).2
    ring
  have hsumTwo : 2 ≤ n ^ 2 + (n + 1) ^ 2 := by omega
  have hAne : A ≠ 0 := by
    dsimp only [A]
    exact mul_ne_zero hPXne hQXne
  have hBne : B ≠ 0 := by
    intro hzero
    apply hBcoeff_ne
    rw [hzero]
    simp
  have hCne : C₀ ≠ 0 := by
    dsimp only [C₀]
    exact mul_ne_zero hPZne hQZne
  have hfour : (4 : R) ≠ 0 := by norm_num
  have hBsqDegree : (B ^ 2).natDegree = (2 * n + 1) ^ 2 - 1 := by
    rw [natDegree_pow, hBDegree]
    omega
  have hACDegree : (A * C₀).natDegree = (2 * n + 1) ^ 2 - 1 := by
    rw [natDegree_mul hAne hCne, hADegree, hCDegree]
    omega
  have hFourACDegree : (C 4 * A * C₀).natDegree = (2 * n + 1) ^ 2 - 1 := by
    rw [show C 4 * A * C₀ = C 4 * (A * C₀) by ring,
      natDegree_C_mul hfour, hACDegree]
  have hBsqCoeff : (B ^ 2).coeff ((2 * n + 1) ^ 2 - 1) = B.leadingCoeff ^ 2 := by
    rw [← hBsqDegree, coeff_natDegree, leadingCoeff_pow]
  have hFourACCoeff : (C 4 * A * C₀).coeff ((2 * n + 1) ^ 2 - 1) =
      4 * A.leadingCoeff * C₀.leadingCoeff := by
    rw [← hFourACDegree, coeff_natDegree]
    simp [leadingCoeff_mul]
  have hZcoeff : Z₀.coeff ((2 * n + 1) ^ 2 - 1) =
      ((2 * n + 1 : ℕ) : R) ^ 2 := by
    dsimp only [Z₀]
    rw [coeff_sub, hBsqCoeff, hFourACCoeff, hBLeading, hALeading, hCLeading]
    push_cast
    ring
  have hZcoeff_ne : Z₀.coeff ((2 * n + 1) ^ 2 - 1) ≠ 0 := by
    rw [hZcoeff]
    exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (2 * n)))
  have hZdegree_le : Z₀.natDegree ≤ (2 * n + 1) ^ 2 - 1 := by
    dsimp only [Z₀]
    calc
      (B ^ 2 - C 4 * A * C₀).natDegree ≤
          max (B ^ 2).natDegree (C 4 * A * C₀).natDegree := natDegree_sub_le _ _
      _ = (2 * n + 1) ^ 2 - 1 := by rw [hBsqDegree, hFourACDegree, max_self]
  have hZDegree : Z₀.natDegree = (2 * n + 1) ^ 2 - 1 := by
    exact natDegree_eq_of_le_of_coeff_ne_zero hZdegree_le hZcoeff_ne
  have hZLeading : Z₀.leadingCoeff = ((2 * n + 1 : ℕ) : R) ^ 2 := by
    rw [leadingCoeff, hZDegree, hZcoeff]
  have hZne : Z₀ ≠ 0 := leadingCoeff_ne_zero.mp
    (hZLeading.trans_ne
      (pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (2 * n)))))
  have htwo : (2 : R) ≠ 0 := by norm_num
  have hBADegree : (B * A).natDegree = (2 * n + 1) ^ 2 := by
    rw [natDegree_mul hBne hAne, hBDegree, hADegree]
    omega
  have hTwoBADegree : (C 2 * B * A).natDegree = (2 * n + 1) ^ 2 := by
    rw [show C 2 * B * A = C 2 * (B * A) by ring,
      natDegree_C_mul htwo, hBADegree]
  have hTwoBACoeff : (C 2 * B * A).coeff ((2 * n + 1) ^ 2) =
      2 * B.leadingCoeff * A.leadingCoeff := by
    rw [← hTwoBADegree, coeff_natDegree]
    simp [leadingCoeff_mul]
  have hB2AC_lt : (C W.b₂ * A * C₀).natDegree < (2 * n + 1) ^ 2 := by
    calc
      (C W.b₂ * A * C₀).natDegree ≤ (A * C₀).natDegree := by
        rw [show C W.b₂ * A * C₀ = C W.b₂ * (A * C₀) by ring]
        exact natDegree_C_mul_le _ _
      _ = (2 * n + 1) ^ 2 - 1 := hACDegree
      _ < (2 * n + 1) ^ 2 := Nat.sub_lt (pow_pos (by omega) 2) Nat.zero_lt_one
  have hB4BC_lt : (C W.b₄ * B * C₀).natDegree < (2 * n + 1) ^ 2 := by
    calc
      (C W.b₄ * B * C₀).natDegree ≤ (B * C₀).natDegree := by
        rw [show C W.b₄ * B * C₀ = C W.b₄ * (B * C₀) by ring]
        exact natDegree_C_mul_le _ _
      _ ≤ B.natDegree + C₀.natDegree := natDegree_mul_le
      _ < (2 * n + 1) ^ 2 := by rw [hBDegree, hCDegree]; omega
  have hB6CC_lt : (C W.b₆ * C₀ ^ 2).natDegree < (2 * n + 1) ^ 2 := by
    calc
      (C W.b₆ * C₀ ^ 2).natDegree ≤ (C₀ ^ 2).natDegree := natDegree_C_mul_le _ _
      _ = 2 * C₀.natDegree := natDegree_pow C₀ 2
      _ < (2 * n + 1) ^ 2 := by rw [hCDegree]; omega
  have hTcoeff : T₀.coeff ((2 * n + 1) ^ 2) =
      2 * ((n : R) ^ 2 + ((n + 1 : ℕ) : R) ^ 2) := by
    dsimp only [T₀]
    simp only [coeff_add, hTwoBACoeff,
      coeff_eq_zero_of_natDegree_lt hB2AC_lt,
      coeff_eq_zero_of_natDegree_lt hB4BC_lt,
      coeff_eq_zero_of_natDegree_lt hB6CC_lt, add_zero]
    rw [hBLeading, hALeading]
    ring
  have hTcoeff_ne : T₀.coeff ((2 * n + 1) ^ 2) ≠ 0 := by
    rw [hTcoeff]
    norm_cast
    omega
  have hTdegree_le : T₀.natDegree ≤ (2 * n + 1) ^ 2 := by
    dsimp only [T₀]
    refine (natDegree_add_le _ _).trans (max_le ?_ hB6CC_lt.le)
    refine (natDegree_add_le _ _).trans (max_le ?_ hB4BC_lt.le)
    exact (natDegree_add_le _ _).trans (max_le hTwoBADegree.le hB2AC_lt.le)
  have hTDegree : T₀.natDegree = (2 * n + 1) ^ 2 :=
    natDegree_eq_of_le_of_coeff_ne_zero hTdegree_le hTcoeff_ne
  have hXZDegree : (X * Z₀).natDegree = (2 * n + 1) ^ 2 := by
    rw [natDegree_X_mul hZne, hZDegree]
    have hpos : 0 < (2 * n + 1) ^ 2 := pow_pos (by omega) 2
    omega
  have hXZcoeff : (X * Z₀).coeff ((2 * n + 1) ^ 2) =
      ((2 * n + 1 : ℕ) : R) ^ 2 := by
    rw [← hXZDegree, coeff_natDegree, leadingCoeff_mul, leadingCoeff_X, one_mul,
      hZLeading]
  have hNcoeff : (T₀ - X * Z₀).coeff ((2 * n + 1) ^ 2) = 1 := by
    rw [coeff_sub, hTcoeff, hXZcoeff]
    push_cast
    ring
  have hNdegree_le : (T₀ - X * Z₀).natDegree ≤ (2 * n + 1) ^ 2 := by
    calc
      (T₀ - X * Z₀).natDegree ≤ max T₀.natDegree (X * Z₀).natDegree :=
        natDegree_sub_le _ _
      _ = (2 * n + 1) ^ 2 := by rw [hTDegree, hXZDegree, max_self]
  dsimp only [kummerOdd]
  change KummerDegreeData (2 * n + 1) (T₀ - X * Z₀, Z₀)
  exact ⟨hNdegree_le, hNcoeff, hZdegree_le, hZcoeff⟩

end SaturationMonoid.UniversalBSDGeneratedKummerLadder
