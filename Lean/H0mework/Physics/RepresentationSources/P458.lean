/-
  Proposition 458: anomaly equations force the Standard-Model hypercharge
  ratios, up to the expected `uᶜ/dᶜ` exchange.

  P457 proves that the finite Weyl-multiplet carrier is anomaly-free.  This
  file proves the converse algebraic pressure in the same fixed multiplet
  shape: once the electron-conjugate charge is normalized to `1`, the anomaly
  equations leave only two solutions.  They differ only by swapping the two
  color-singlet conjugate labels `uᶜ` and `dᶜ`; an orientation condition
  (`uᶜ < dᶜ`) selects the conventional Standard-Model branch.

  Boundary: this is uniqueness of hypercharge ratios for the fixed
  `(Q,uᶜ,dᶜ,L,eᶜ)` multiplet shape.  It is not yet a theorem that SU(7)
  uniquely produces that multiplet shape.
-/

import H0mework.Physics.RepresentationSources.P457

namespace SaturationMonoid
namespace StandardModelConstraint
namespace RunningSigmaBeta

/-! ## Abstract one-generation hypercharge equations -/

/-- A rational hypercharge assignment on the fixed one-generation
`(Q,uᶜ,dᶜ,L,eᶜ)` multiplet shape. -/
structure OneGenerationHyperchargeAssignment where
  q : ℚ
  u : ℚ
  d : ℚ
  l : ℚ
  e : ℚ

namespace OneGenerationHyperchargeAssignment

/-- `[SU(3)]²U(1)` anomaly equation in cleared-denominator form. -/
def colorAnomalyFree (Y : OneGenerationHyperchargeAssignment) : Prop :=
  2 * Y.q + Y.u + Y.d = 0

/-- `[SU(2)]²U(1)` anomaly equation in cleared-denominator form. -/
def weakAnomalyFree (Y : OneGenerationHyperchargeAssignment) : Prop :=
  3 * Y.q + Y.l = 0

/-- Gravitational-`U(1)` anomaly equation. -/
def gravitationalAnomalyFree (Y : OneGenerationHyperchargeAssignment) : Prop :=
  6 * Y.q + 3 * Y.u + 3 * Y.d + 2 * Y.l + Y.e = 0

/-- Cubic `U(1)³` anomaly equation. -/
def cubicAnomalyFree (Y : OneGenerationHyperchargeAssignment) : Prop :=
  6 * Y.q ^ 3 + 3 * Y.u ^ 3 + 3 * Y.d ^ 3 + 2 * Y.l ^ 3 + Y.e ^ 3 = 0

/-- The conventional Standard-Model hypercharge assignment. -/
def standardModel : OneGenerationHyperchargeAssignment where
  q := 1 / 6
  u := -(2 / 3)
  d := 1 / 3
  l := -(1 / 2)
  e := 1

/-- The same solution with the two color-singlet conjugate labels exchanged. -/
def swappedSinglets : OneGenerationHyperchargeAssignment where
  q := 1 / 6
  u := 1 / 3
  d := -(2 / 3)
  l := -(1 / 2)
  e := 1

/-- The Standard-Model assignment satisfies the four anomaly equations. -/
theorem standardModel_anomaly_free :
    colorAnomalyFree standardModel ∧
      weakAnomalyFree standardModel ∧
      gravitationalAnomalyFree standardModel ∧
      cubicAnomalyFree standardModel := by
  norm_num [standardModel, colorAnomalyFree, weakAnomalyFree,
    gravitationalAnomalyFree, cubicAnomalyFree]

/-- The swapped-singlet assignment also satisfies the four anomaly equations;
anomaly cancellation alone does not distinguish the two singlet labels. -/
theorem swappedSinglets_anomaly_free :
    colorAnomalyFree swappedSinglets ∧
      weakAnomalyFree swappedSinglets ∧
      gravitationalAnomalyFree swappedSinglets ∧
      cubicAnomalyFree swappedSinglets := by
  norm_num [swappedSinglets, colorAnomalyFree, weakAnomalyFree,
    gravitationalAnomalyFree, cubicAnomalyFree]

/-- Linear anomaly equations plus `e=1` force `q=1/6`. -/
theorem q_eq_one_six_of_linear_anomalies
    {Y : OneGenerationHyperchargeAssignment}
    (hc : colorAnomalyFree Y)
    (hw : weakAnomalyFree Y)
    (hg : gravitationalAnomalyFree Y)
    (he : Y.e = 1) :
    Y.q = 1 / 6 := by
  unfold colorAnomalyFree at hc
  unfold weakAnomalyFree at hw
  unfold gravitationalAnomalyFree at hg
  linarith

/-- Linear anomaly equations plus `e=1` force `l=-1/2`. -/
theorem l_eq_neg_half_of_linear_anomalies
    {Y : OneGenerationHyperchargeAssignment}
    (hc : colorAnomalyFree Y)
    (hw : weakAnomalyFree Y)
    (hg : gravitationalAnomalyFree Y)
    (he : Y.e = 1) :
    Y.l = -(1 / 2) := by
  have hq := q_eq_one_six_of_linear_anomalies hc hw hg he
  unfold weakAnomalyFree at hw
  linarith

/-- Linear anomaly equations plus `e=1` force `u+d=-1/3`. -/
theorem u_add_d_eq_neg_third_of_linear_anomalies
    {Y : OneGenerationHyperchargeAssignment}
    (hc : colorAnomalyFree Y)
    (hw : weakAnomalyFree Y)
    (hg : gravitationalAnomalyFree Y)
    (he : Y.e = 1) :
    Y.u + Y.d = -(1 / 3) := by
  have hq := q_eq_one_six_of_linear_anomalies hc hw hg he
  unfold colorAnomalyFree at hc
  linarith

/-- The cubic anomaly, after the linear equations and `e=1`, leaves only
`u=1/3` or `u=-2/3`. -/
theorem u_branch_of_anomalies
    {Y : OneGenerationHyperchargeAssignment}
    (hc : colorAnomalyFree Y)
    (hw : weakAnomalyFree Y)
    (hg : gravitationalAnomalyFree Y)
    (hcu : cubicAnomalyFree Y)
    (he : Y.e = 1) :
    Y.u = 1 / 3 ∨ Y.u = -(2 / 3) := by
  have hq := q_eq_one_six_of_linear_anomalies hc hw hg he
  have hl := l_eq_neg_half_of_linear_anomalies hc hw hg he
  have hud := u_add_d_eq_neg_third_of_linear_anomalies hc hw hg he
  have hd : Y.d = -(1 / 3) - Y.u := by
    linarith
  unfold cubicAnomalyFree at hcu
  have hprod : (Y.u - 1 / 3) * (Y.u + 2 / 3) = 0 := by
    rw [hq, hl, hd, he] at hcu
    nlinarith
  rcases mul_eq_zero.mp hprod with hleft | hright
  · left
    linarith
  · right
    linarith

/-- Normalized anomaly equations determine the hypercharge assignment up to
exchanging `uᶜ` and `dᶜ`. -/
theorem normalized_anomaly_solution_two_branches
    {Y : OneGenerationHyperchargeAssignment}
    (hc : colorAnomalyFree Y)
    (hw : weakAnomalyFree Y)
    (hg : gravitationalAnomalyFree Y)
    (hcu : cubicAnomalyFree Y)
    (he : Y.e = 1) :
    Y = standardModel ∨ Y = swappedSinglets := by
  have hq := q_eq_one_six_of_linear_anomalies hc hw hg he
  have hl := l_eq_neg_half_of_linear_anomalies hc hw hg he
  have hud := u_add_d_eq_neg_third_of_linear_anomalies hc hw hg he
  rcases u_branch_of_anomalies hc hw hg hcu he with hu | hu
  · right
    have hd : Y.d = -(2 / 3) := by linarith
    cases Y
    simp [swappedSinglets] at hq hl he hu hd ⊢
    exact ⟨hq, hu, hd, hl, he⟩
  · left
    have hd : Y.d = 1 / 3 := by linarith
    cases Y
    simp [standardModel] at hq hl he hu hd ⊢
    exact ⟨hq, hu, hd, hl, he⟩

/-- With the orientation `uᶜ < dᶜ`, the normalized anomaly solution is exactly
the conventional Standard-Model hypercharge assignment. -/
theorem normalized_oriented_anomaly_solution_eq_standardModel
    {Y : OneGenerationHyperchargeAssignment}
    (hc : colorAnomalyFree Y)
    (hw : weakAnomalyFree Y)
    (hg : gravitationalAnomalyFree Y)
    (hcu : cubicAnomalyFree Y)
    (he : Y.e = 1)
    (horient : Y.u < Y.d) :
    Y = standardModel := by
  rcases normalized_anomaly_solution_two_branches hc hw hg hcu he with hsm | hswap
  · exact hsm
  · rw [hswap] at horient
    norm_num [swappedSinglets] at horient

end OneGenerationHyperchargeAssignment

end RunningSigmaBeta
end StandardModelConstraint
end SaturationMonoid
