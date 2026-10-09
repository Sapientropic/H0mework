import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Envelope

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceGaussianModel SourceExponential
open GaussianPair Laplace.Axis
noncomputable section

theorem sPairAttenuation_pos (left right : Term) :
    0 < sPairAttenuation left right := by
  unfold sPairAttenuation
  exact Finset.prod_pos (fun i _ => Real.exp_pos _)

theorem axisMoment_cast (na nb : ℕ) (dA dB beta : ℚ) :
    (axisMoment na nb dA dB beta : ℝ) =
      ∑ i ∈ Finset.range (na+1), ∑ j ∈ Finset.range (nb+1),
        (Nat.choose na i : ℝ) * (dA:ℝ)^(na-i) * (Nat.choose nb j : ℝ) *
          (dB:ℝ)^(nb-j) * (gaussMoment (i+j) beta : ℝ) := by
  unfold axisMoment
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]

theorem axis_pow_exp_le (na nb : ℕ) (y : ℝ) (dA dB beta : ℚ)
    (hy : 0 ≤ y) (hdA : 0 ≤ dA) (hdB : 0 ≤ dB) (hbeta : 0 < beta) :
    (y + (dA:ℝ))^na * (y + (dB:ℝ))^nb * Real.exp (-(beta:ℝ) * y^2) ≤
      (axisMoment na nb dA dB beta : ℝ) := by
  rw [add_pow, add_pow, Finset.sum_mul_sum]
  rw [Finset.sum_mul]
  rw [axisMoment_cast]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  have hcoef : (0 : ℝ) ≤ (Nat.choose na i : ℝ) * (dA:ℝ)^(na-i) *
      (Nat.choose nb j : ℝ) * (dB:ℝ)^(nb-j) := by positivity
  have hmom : y^(i+j) * Real.exp (-(beta:ℝ) * y^2) ≤
      (gaussMoment (i+j) beta : ℝ) := by
    have g := gauss_moment_bound (i+j) beta hbeta y
    rwa [abs_of_nonneg hy] at g
  calc (y^i * (dA:ℝ)^(na-i) * (Nat.choose na i : ℝ)) *
        (y^j * (dB:ℝ)^(nb-j) * (Nat.choose nb j : ℝ)) *
        Real.exp (-(beta:ℝ) * y^2)
      = ((Nat.choose na i : ℝ) * (dA:ℝ)^(na-i) *
          (Nat.choose nb j : ℝ) * (dB:ℝ)^(nb-j)) *
          (y^(i+j) * Real.exp (-(beta:ℝ) * y^2)) := by ring
    _ ≤ (Nat.choose na i : ℝ) * (dA:ℝ)^(na-i) * (Nat.choose nb j : ℝ) *
          (dB:ℝ)^(nb-j) * (gaussMoment (i+j) beta : ℝ) :=
        mul_le_mul_of_nonneg_left hmom hcoef

theorem pairMu_real (a b : Term) :
    (pairMu a b : ℝ) = (a.exponent : ℝ) * (b.exponent : ℝ) /
      ((a.exponent : ℝ) + (b.exponent : ℝ)) := by
  simp only [pairMu, pairRate, Rat.cast_div, Rat.cast_mul, Rat.cast_add]

theorem pairRate_real (a b : Term) :
    (pairRate a b : ℝ) = (a.exponent : ℝ) + (b.exponent : ℝ) :=
  Rat.cast_add a.exponent b.exponent

theorem pairDistSq_real (a b : Term) :
    (pairDistSq a b : ℝ) = ((a.centre 0 : ℝ) - (b.centre 0 : ℝ))^2 +
      ((a.centre 1 : ℝ) - (b.centre 1 : ℝ))^2 +
      ((a.centre 2 : ℝ) - (b.centre 2 : ℝ))^2 := by
  simp only [pairDistSq, Rat.cast_add, Rat.cast_sub, Rat.cast_pow]

theorem centre_halved (α β A B : ℝ) (h : (0:ℝ) < α + β) :
    GaussianPair.centre (α/2) (β/2) A B = GaussianPair.centre α β A B := by
  unfold GaussianPair.centre
  have h1 : α/2 + β/2 ≠ 0 := by linarith
  have h2 : α + β ≠ 0 := ne_of_gt h
  field_simp

theorem halvedCoefficient_real (a b : Term) :
    (halvedCoefficient a b : ℝ) =
      |(a.weight : ℝ) * (b.weight : ℝ)| *
        (expUp (pairMu a b * pairDistSq a b / 2) : ℝ) *
        (pairMomentProduct a b : ℝ) := by
  simp only [halvedCoefficient, Rat.cast_mul, Rat.cast_abs]

theorem pairMu_halved_real (a b : Term)
    (h : (0:ℝ) < (a.exponent : ℝ) + (b.exponent : ℝ)) :
    ((a.exponent : ℝ)/2)*((b.exponent : ℝ)/2)/
      (((a.exponent : ℝ)/2)+((b.exponent : ℝ)/2)) = (pairMu a b : ℝ)/2 := by
  rw [pairMu_real]
  have h1 : (a.exponent : ℝ)/2 + (b.exponent : ℝ)/2 ≠ 0 := by linarith
  have h2 : (a.exponent : ℝ) + (b.exponent : ℝ) ≠ 0 := ne_of_gt h
  field_simp

theorem pairMomentProduct_cast (a b : Term) :
    (pairMomentProduct a b : ℝ) =
      (pairAxisMoment a b 0 : ℝ) * (pairAxisMoment a b 1 : ℝ) *
        (pairAxisMoment a b 2 : ℝ) := by
  simp only [pairMomentProduct, Rat.cast_mul]

theorem axisShape_abs_le (a b : Term) (axis : Fin 3) (x : ℝ)
    (ha : 0 < a.exponent) (hb : 0 < b.exponent) :
    |axisShape a b axis x| ≤
      (pairAxisMoment a b axis : ℝ) *
        Real.exp (-(pairMu a b : ℝ) *
          ((a.centre axis : ℝ) - (b.centre axis : ℝ))^2) *
        Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) *
          (x - (pairCentre a b axis : ℝ))^2) := by
  have hbeta : (0 : ℚ) < pairRate a b / 2 :=
    div_pos (pairRate_pos a b ha hb) (by norm_num)
  set P : ℝ := (pairCentre a b axis : ℝ) with hPdef
  have hP : P =
      GaussianPair.centre (a.exponent : ℝ) (b.exponent : ℝ)
        (a.centre axis : ℝ) (b.centre axis : ℝ) := by
    rw [hPdef]
    exact pairCentre_real a b axis
  have hdA : |P - (a.centre axis : ℝ)| =
      ((|pairCentre a b axis - a.centre axis| : ℚ) : ℝ) := by
    rw [hPdef, ← Rat.cast_sub, Rat.cast_abs]
  have hdB : |P - (b.centre axis : ℝ)| =
      ((|pairCentre a b axis - b.centre axis| : ℚ) : ℝ) := by
    rw [hPdef, ← Rat.cast_sub, Rat.cast_abs]
  have hy : 0 ≤ |x - P| := abs_nonneg _
  have triA : |x - (a.centre axis : ℝ)| ≤
      |x - P| + ((|pairCentre a b axis - a.centre axis| : ℚ) : ℝ) := by
    have e : x - (a.centre axis : ℝ) =
        (x - P) + (P - (a.centre axis : ℝ)) := by ring
    calc |x - (a.centre axis : ℝ)| = |(x - P) + (P - (a.centre axis : ℝ))| := by
          rw [e]
      _ ≤ |x - P| + |P - (a.centre axis : ℝ)| := abs_add_le _ _
      _ = _ := by rw [hdA]
  have triB : |x - (b.centre axis : ℝ)| ≤
      |x - P| + ((|pairCentre a b axis - b.centre axis| : ℚ) : ℝ) := by
    have e : x - (b.centre axis : ℝ) =
        (x - P) + (P - (b.centre axis : ℝ)) := by ring
    calc |x - (b.centre axis : ℝ)| = |(x - P) + (P - (b.centre axis : ℝ))| := by
          rw [e]
      _ ≤ |x - P| + |P - (b.centre axis : ℝ)| := abs_add_le _ _
      _ = _ := by rw [hdB]
  have powA : |x - (a.centre axis : ℝ)|^(a.powers axis) ≤
      (|x - P| + ((|pairCentre a b axis - a.centre axis| : ℚ) : ℝ))^(a.powers axis) :=
    pow_le_pow_left₀ (abs_nonneg _) triA _
  have powB : |x - (b.centre axis : ℝ)|^(b.powers axis) ≤
      (|x - P| + ((|pairCentre a b axis - b.centre axis| : ℚ) : ℝ))^(b.powers axis) :=
    pow_le_pow_left₀ (abs_nonneg _) triB _
  have hsplit : Real.exp (-((a.exponent : ℝ) + (b.exponent : ℝ)) *
        (x - P)^2) =
      Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) * (x - P)^2) *
      Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) * (x - P)^2) := by
    have hcast : ((a.exponent : ℝ) + (b.exponent : ℝ)) = (pairRate a b : ℝ) := by
      exact_mod_cast (pairRate_real a b).symm
    rw [hcast, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hmoment : |x - (a.centre axis : ℝ)|^(a.powers axis) *
        |x - (b.centre axis : ℝ)|^(b.powers axis) *
        Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) * (x - P)^2) ≤
      (pairAxisMoment a b axis : ℝ) := by
    have hyc : (x - P)^2 = |x - P|^2 := (sq_abs _).symm
    rw [hyc]
    calc |x - (a.centre axis : ℝ)|^(a.powers axis) *
          |x - (b.centre axis : ℝ)|^(b.powers axis) *
          Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) * |x - P|^2)
        ≤ (|x - P| + (|pairCentre a b axis - a.centre axis| : ℚ))^(a.powers axis) *
          (|x - P| + (|pairCentre a b axis - b.centre axis| : ℚ))^(b.powers axis) *
          Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) * |x - P|^2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul powA powB
              (pow_nonneg (abs_nonneg _) _)
              (pow_nonneg (le_trans (abs_nonneg _) triA) _))
            (Real.exp_pos _).le
      _ ≤ (axisMoment (a.powers axis) (b.powers axis)
            |pairCentre a b axis - a.centre axis|
            |pairCentre a b axis - b.centre axis| (pairRate a b / 2) : ℝ) :=
          axis_pow_exp_le (a.powers axis) (b.powers axis) |x - P| _ _
            (pairRate a b / 2) hy (abs_nonneg _) (abs_nonneg _) hbeta
      _ = (pairAxisMoment a b axis : ℝ) := rfl
  unfold axisShape
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow,
    abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  rw [← neg_mul, ← pairMu_real a b, ← hP]
  rw [hsplit]
  calc |x - (a.centre axis : ℝ)|^(a.powers axis) *
        |x - (b.centre axis : ℝ)|^(b.powers axis) *
        Real.exp (-(pairMu a b : ℝ) *
          ((a.centre axis : ℝ) - (b.centre axis : ℝ))^2) *
        (Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) * (x - P)^2) *
        Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) * (x - P)^2))
      = (|x - (a.centre axis : ℝ)|^(a.powers axis) *
          |x - (b.centre axis : ℝ)|^(b.powers axis) *
          Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) * (x - P)^2)) *
        (Real.exp (-(pairMu a b : ℝ) *
          ((a.centre axis : ℝ) - (b.centre axis : ℝ))^2) *
        Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) * (x - P)^2)) := by ring
    _ ≤ (pairAxisMoment a b axis : ℝ) *
        (Real.exp (-(pairMu a b : ℝ) *
          ((a.centre axis : ℝ) - (b.centre axis : ℝ))^2) *
        Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) * (x - P)^2)) :=
        mul_le_mul_of_nonneg_right hmoment
          (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = _ := by ring

theorem sPairRate_absTerm (a b : Term) :
    sPairRate (absTerm a) (absTerm b) = sPairRate a b := rfl

theorem sPairCentre_absTerm (a b : Term) :
    sPairCentre (absTerm a) (absTerm b) = sPairCentre a b := rfl

theorem sPairAttenuation_absTerm (a b : Term) :
    sPairAttenuation (absTerm a) (absTerm b) = sPairAttenuation a b := rfl

theorem sPairCoefficient_absTerm (a b : Term) :
    sPairCoefficient (absTerm a) (absTerm b) =
      |(a.weight : ℝ) * (b.weight : ℝ)| * sPairAttenuation a b := by
  unfold sPairCoefficient
  rw [absTerm_weight, absTerm_weight, Rat.cast_abs, Rat.cast_abs, ← abs_mul]
  rw [sPairAttenuation_absTerm]

theorem sPairAttenuation_eq_exp (a b : Term) :
    sPairAttenuation a b =
      Real.exp (-(pairMu a b : ℝ) * (pairDistSq a b : ℝ)) := by
  unfold sPairAttenuation
  rw [← Real.exp_sum]
  congr 1
  simp_rw [← neg_mul]
  rw [← Finset.mul_sum]
  congr 1
  · simp only [sPairRate]
    rw [pairMu_real]
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two]
    rw [pairDistSq_real]
    ring

theorem sPairAttenuation_le_expUp (a b : Term)
    (ha : 0 ≤ a.exponent) (hb : 0 ≤ b.exponent) :
    sPairAttenuation a b ≤ (expUp (pairMu a b * pairDistSq a b) : ℝ) := by
  rw [sPairAttenuation_eq_exp, neg_mul, ← Rat.cast_mul]
  exact expUp_spec _ (mul_nonneg (pairMu_nonneg a b ha hb)
    (pairDistSq_nonneg a b))

theorem sPairRate_halved (a b : Term) :
    sPairRate (halvedLeft a b) (halvedRight a b) =
      ((pairRate a b / 2 : ℚ) : ℝ) := by
  unfold sPairRate
  rw [halvedLeft_exponent, halvedRight_exponent]
  rw [show ((a.exponent / 2 : ℚ) : ℝ) = (a.exponent : ℝ)/2 by push_cast; ring]
  rw [show ((b.exponent / 2 : ℚ) : ℝ) = (b.exponent : ℝ)/2 by push_cast; ring]
  rw [show ((pairRate a b / 2 : ℚ) : ℝ) = (pairRate a b : ℝ)/2 by
    push_cast; ring]
  rw [pairRate_real]
  ring

theorem sPairCentre_halved (a b : Term)
    (h : (0:ℝ) < (a.exponent : ℝ) + (b.exponent : ℝ)) (axis : Fin 3) :
    sPairCentre (halvedLeft a b) (halvedRight a b) axis =
      (pairCentre a b axis : ℝ) := by
  simp only [sPairCentre]
  rw [halvedLeft_exponent, halvedRight_exponent,
    halvedLeft_centre, halvedRight_centre]
  rw [show ((a.exponent / 2 : ℚ) : ℝ) = (a.exponent : ℝ)/2 by push_cast; ring]
  rw [show ((b.exponent / 2 : ℚ) : ℝ) = (b.exponent : ℝ)/2 by push_cast; ring]
  rw [centre_halved _ _ _ _ h, pairCentre_real]

theorem sPairAttenuation_halved (a b : Term)
    (h : (0:ℝ) < (a.exponent : ℝ) + (b.exponent : ℝ)) :
    sPairAttenuation (halvedLeft a b) (halvedRight a b) =
      Real.exp (-(pairMu a b : ℝ)/2 * (pairDistSq a b : ℝ)) := by
  simp only [sPairAttenuation, sPairRate]
  rw [halvedLeft_exponent, halvedRight_exponent,
    halvedLeft_centre, halvedRight_centre]
  rw [show ((a.exponent / 2 : ℚ) : ℝ) = (a.exponent : ℝ)/2 by push_cast; ring]
  rw [show ((b.exponent / 2 : ℚ) : ℝ) = (b.exponent : ℝ)/2 by push_cast; ring]
  rw [← Real.exp_sum]
  congr 1
  simp_rw [← neg_mul]
  rw [← Finset.mul_sum]
  congr 1
  · rw [pairMu_halved_real a b h]
    ring
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two]
    rw [pairDistSq_real]
    ring

theorem sPairCoefficient_halved (a b : Term)
    (h : (0:ℝ) < (a.exponent : ℝ) + (b.exponent : ℝ)) :
    sPairCoefficient (halvedLeft a b) (halvedRight a b) =
      (halvedCoefficient a b : ℝ) *
        Real.exp (-(pairMu a b : ℝ)/2 * (pairDistSq a b : ℝ)) := by
  simp only [sPairCoefficient]
  rw [sPairAttenuation_halved a b h, halvedLeft_weight, halvedRight_weight,
    Rat.cast_one, mul_one]

theorem sPairAttenuation_halved_le (a b : Term)
    (ha : 0 ≤ a.exponent) (hb : 0 ≤ b.exponent)
    (_h : (0:ℝ) < (a.exponent : ℝ) + (b.exponent : ℝ)) :
    Real.exp (-(pairMu a b : ℝ)/2 * (pairDistSq a b : ℝ)) ≤
      (expUp (pairMu a b * pairDistSq a b / 2) : ℝ) := by
  have hT : (0:ℚ) ≤ pairMu a b * pairDistSq a b / 2 :=
    div_nonneg (mul_nonneg (pairMu_nonneg a b ha hb)
      (pairDistSq_nonneg a b)) (by norm_num)
  have hcast : (-(pairMu a b : ℝ)/2 * (pairDistSq a b : ℝ)) =
      (-(pairMu a b * pairDistSq a b / 2 : ℚ) : ℝ) := by
    push_cast
    rw [pairMu_real, pairDistSq_real]
    ring
  rw [hcast]
  exact expUp_spec _ hT

theorem sPairCoefficient_envelope_nonneg (a b : Term)
    (ha : 0 < a.exponent) (hb : 0 < b.exponent) :
    0 ≤ sPairCoefficient (pairEnvelope a b).1 (pairEnvelope a b).2 := by
  unfold pairEnvelope
  by_cases hs : pairSTerms a b
  · rw [if_pos hs]
    show 0 ≤ sPairCoefficient (absTerm a) (absTerm b)
    rw [sPairCoefficient_absTerm]
    exact mul_nonneg (abs_nonneg _) (sPairAttenuation_pos a b).le
  · rw [if_neg hs]
    show 0 ≤ sPairCoefficient (halvedLeft a b) (halvedRight a b)
    rw [sPairCoefficient_halved a b (by
      rw [← pairRate_real]; exact_mod_cast pairRate_pos a b ha hb)]
    exact mul_nonneg
      (by exact_mod_cast halvedCoefficient_nonneg a b ha.le hb.le)
      (Real.exp_pos _).le

theorem sPairCoefficient_envelope_le (a b : Term)
    (ha : 0 < a.exponent) (hb : 0 < b.exponent) :
    sPairCoefficient (pairEnvelope a b).1 (pairEnvelope a b).2 ≤
      (pairKappa a b : ℝ) := by
  unfold pairEnvelope pairKappa
  by_cases hs : pairSTerms a b
  · rw [if_pos hs, if_pos hs]
    show sPairCoefficient (absTerm a) (absTerm b) ≤
      ((|a.weight * b.weight| * expUp (pairMu a b * pairDistSq a b) : ℚ) : ℝ)
    rw [sPairCoefficient_absTerm]
    push_cast
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact sPairAttenuation_le_expUp a b ha.le hb.le
  · rw [if_neg hs, if_neg hs]
    show sPairCoefficient (halvedLeft a b) (halvedRight a b) ≤
      ((halvedCoefficient a b * expUp (pairMu a b * pairDistSq a b / 2) : ℚ) : ℝ)
    rw [sPairCoefficient_halved a b (by
      rw [← pairRate_real]; exact_mod_cast pairRate_pos a b ha hb)]
    push_cast
    apply mul_le_mul_of_nonneg_left _ (by
      exact_mod_cast halvedCoefficient_nonneg a b ha.le hb.le)
    exact sPairAttenuation_halved_le a b ha.le hb.le (by
      rw [← pairRate_real]; exact_mod_cast pairRate_pos a b ha hb)

theorem pairShape_abs_le_envelope (a b : Term) (x : Point)
    (ha : 0 < a.exponent) (hb : 0 < b.exponent) :
    |pairShape a b x| ≤
      pairShape (pairEnvelope a b).1 (pairEnvelope a b).2 x := by
  have hrateR : (0 : ℝ) < (a.exponent : ℝ) + (b.exponent : ℝ) := by
    rw [← pairRate_real]
    exact_mod_cast pairRate_pos a b ha hb
  unfold pairEnvelope
  by_cases hs : pairSTerms a b
  · rw [if_pos hs]
    obtain ⟨hla, hrb⟩ := hs
    show |pairShape a b x| ≤ pairShape (absTerm a) (absTerm b) x
    have hLa : sPowers (absTerm a) := fun _ => rfl
    have hRb : sPowers (absTerm b) := fun _ => rfl
    rw [s_pair_shape a b x hla hrb, s_pair_shape (absTerm a) (absTerm b) x hLa hRb]
    rw [show (∏ axis : Fin 3, Real.exp (-(sPairRate (absTerm a) (absTerm b)) *
        (x axis - sPairCentre (absTerm a) (absTerm b) axis)^2)) =
        ∏ axis : Fin 3, Real.exp (-(sPairRate a b) *
        (x axis - sPairCentre a b axis)^2) from rfl]
    rw [sPairCoefficient_absTerm]
    unfold sPairCoefficient
    rw [abs_mul, abs_of_pos (Finset.prod_pos fun i _ => Real.exp_pos _),
      abs_mul, abs_of_pos (sPairAttenuation_pos a b)]
  · rw [if_neg hs]
    show |pairShape a b x| ≤ pairShape (halvedLeft a b) (halvedRight a b) x
    have hLs : sPowers (halvedLeft a b) := fun _ => rfl
    have hRs : sPowers (halvedRight a b) := fun _ => rfl
    rw [s_pair_shape (halvedLeft a b) (halvedRight a b) x hLs hRs]
    have hprodEnv : (∏ axis : Fin 3, Real.exp (-(sPairRate (halvedLeft a b)
        (halvedRight a b)) *
        (x axis - sPairCentre (halvedLeft a b) (halvedRight a b) axis)^2)) =
        ∏ axis : Fin 3, Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) *
        (x axis - (pairCentre a b axis : ℝ))^2) := by
      apply Finset.prod_congr rfl
      intro axis _
      rw [sPairRate_halved, sPairCentre_halved a b hrateR axis]
    have hCoefEnv : sPairCoefficient (halvedLeft a b) (halvedRight a b) =
        (halvedCoefficient a b : ℝ) *
          Real.exp (-(pairMu a b : ℝ)/2 * (pairDistSq a b : ℝ)) :=
      sPairCoefficient_halved a b hrateR
    rw [hCoefEnv, hprodEnv]
    have hprods : |axisShape a b 0 (x 0)| * |axisShape a b 1 (x 1)| *
        |axisShape a b 2 (x 2)| =
        ∏ axis : Fin 3, |axisShape a b axis (x axis)| := by
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.succ_zero_eq_one,
        Fin.succ_one_eq_two]
      ring
    have hle : (∏ axis : Fin 3, |axisShape a b axis (x axis)|) ≤
        ∏ axis : Fin 3, ((pairAxisMoment a b axis : ℝ) *
          Real.exp (-(pairMu a b : ℝ) *
            ((a.centre axis : ℝ) - (b.centre axis : ℝ))^2) *
          Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) *
            (x axis - (pairCentre a b axis : ℝ))^2)) :=
      Finset.prod_le_prod (fun i _ => abs_nonneg _)
        (fun i _ => axisShape_abs_le a b i (x i) ha hb)
    have hdist : (∏ axis : Fin 3, ((pairAxisMoment a b axis : ℝ) *
          Real.exp (-(pairMu a b : ℝ) *
            ((a.centre axis : ℝ) - (b.centre axis : ℝ))^2) *
          Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) *
            (x axis - (pairCentre a b axis : ℝ))^2))) =
        (∏ axis : Fin 3, (pairAxisMoment a b axis : ℝ)) *
        (∏ axis : Fin 3, Real.exp (-(pairMu a b : ℝ) *
          ((a.centre axis : ℝ) - (b.centre axis : ℝ))^2)) *
        (∏ axis : Fin 3, Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) *
          (x axis - (pairCentre a b axis : ℝ))^2)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have hMprod : (∏ axis : Fin 3, (pairAxisMoment a b axis : ℝ)) =
        (pairMomentProduct a b : ℝ) := by
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.succ_zero_eq_one,
        Fin.succ_one_eq_two]
      rw [pairMomentProduct_cast]
      ring
    have hE1 : (∏ axis : Fin 3, Real.exp (-(pairMu a b : ℝ) *
        ((a.centre axis : ℝ) - (b.centre axis : ℝ))^2)) =
        Real.exp (-(pairMu a b : ℝ) * (pairDistSq a b : ℝ)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [← Finset.mul_sum]
      congr 1
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
        Fin.succ_one_eq_two]
      rw [pairDistSq_real]
      ring
    have hHalf : Real.exp (-(pairMu a b : ℝ) * (pairDistSq a b : ℝ)) ≤
        (expUp (pairMu a b * pairDistSq a b / 2) : ℝ) *
        Real.exp (-(pairMu a b : ℝ)/2 * (pairDistSq a b : ℝ)) := by
      have hexp2 : Real.exp (-(pairMu a b : ℝ) * (pairDistSq a b : ℝ)) =
          Real.exp (-(pairMu a b * pairDistSq a b / 2 : ℚ) : ℝ) *
          Real.exp (-(pairMu a b * pairDistSq a b / 2 : ℚ) : ℝ) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        rw [pairMu_real, pairDistSq_real]
        ring
      have hcast : (-(pairMu a b : ℝ)/2 * (pairDistSq a b : ℝ)) =
          (-(pairMu a b * pairDistSq a b / 2 : ℚ) : ℝ) := by
        push_cast
        rw [pairMu_real, pairDistSq_real]
        ring
      rw [hexp2, hcast]
      exact mul_le_mul_of_nonneg_right
        (expUp_spec _ (div_nonneg (mul_nonneg (pairMu_nonneg a b ha.le hb.le)
          (pairDistSq_nonneg a b)) (by norm_num))) (Real.exp_pos _).le
    unfold pairShape
    rw [abs_mul, abs_mul, abs_mul]
    calc |(a.weight : ℝ) * (b.weight : ℝ)| * |axisShape a b 0 (x 0)| *
          |axisShape a b 1 (x 1)| * |axisShape a b 2 (x 2)|
        = |(a.weight : ℝ) * (b.weight : ℝ)| *
          ∏ axis : Fin 3, |axisShape a b axis (x axis)| := by
          rw [← hprods]
          ring
      _ ≤ |(a.weight : ℝ) * (b.weight : ℝ)| *
          ∏ axis : Fin 3, ((pairAxisMoment a b axis : ℝ) *
            Real.exp (-(pairMu a b : ℝ) *
              ((a.centre axis : ℝ) - (b.centre axis : ℝ))^2) *
            Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) *
              (x axis - (pairCentre a b axis : ℝ))^2)) :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ = |(a.weight : ℝ) * (b.weight : ℝ)| * ((pairMomentProduct a b : ℝ) *
          Real.exp (-(pairMu a b : ℝ) * (pairDistSq a b : ℝ)) *
          ∏ axis : Fin 3, Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) *
            (x axis - (pairCentre a b axis : ℝ))^2)) := by
          rw [hdist, hMprod, hE1]
      _ ≤ |(a.weight : ℝ) * (b.weight : ℝ)| * ((pairMomentProduct a b : ℝ) *
          ((expUp (pairMu a b * pairDistSq a b / 2) : ℝ) *
          Real.exp (-(pairMu a b : ℝ)/2 * (pairDistSq a b : ℝ))) *
          ∏ axis : Fin 3, Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) *
            (x axis - (pairCentre a b axis : ℝ))^2)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply mul_le_mul_of_nonneg_right _
            (Finset.prod_nonneg fun i _ => (Real.exp_pos _).le)
          exact mul_le_mul_of_nonneg_left hHalf (by
            exact_mod_cast pairMomentProduct_nonneg a b)
      _ = ((halvedCoefficient a b : ℝ) *
          Real.exp (-(pairMu a b : ℝ)/2 * (pairDistSq a b : ℝ))) *
          ∏ axis : Fin 3, Real.exp (-((pairRate a b / 2 : ℚ) : ℝ) *
            (x axis - (pairCentre a b axis : ℝ))^2) := by
          rw [halvedCoefficient_real]
          ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
