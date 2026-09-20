import Mathlib.Tactic
import H0mework.Realization.Relations.P526

/-!
# Proposition 527: four-source closure for the alpha_s residual producer

P520 defines the exact alpha-level residual target `89/10000` and transports it
to the inverse-coupling correction `-89000/128511`.

P521 proves the conservation/necessity side: a successful producer cannot leave
all physical source contributions zero.

This file makes the producer surface closed under exactly the four roadmap
source families:

* SU(7) breaking;
* threshold effects;
* three-loop RG;
* Higgs / extra representations.

The point is not yet to compute the four numbers.  The point is to make the
independent physical calculation target a finite, exhaustive Lean carrier:
once these four independently supplied contributions sum to the alpha-level
gap, all downstream inverse-coordinate and displayed-alpha closure follows.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open scoped BigOperators

/-! ## Exhaustive four-source carrier -/

/-- THEOREM 1: the four alpha_s residual source families form a finite
exhaustive carrier. -/
instance alphaStrongResidualSourceFintype :
    Fintype AlphaStrongResidualSource where
  elems :=
    {AlphaStrongResidualSource.su7Breaking,
      AlphaStrongResidualSource.threshold,
      AlphaStrongResidualSource.threeLoopRG,
      AlphaStrongResidualSource.higgsExtraRepresentation}
  complete := by
    intro s
    cases s <;> simp

/-- THEOREM 2: every source is one of the four roadmap families. -/
theorem alphaStrongResidualSource_exhaustive
    (s : AlphaStrongResidualSource) :
    s = .su7Breaking ∨
      s = .threshold ∨
        s = .threeLoopRG ∨
          s = .higgsExtraRepresentation := by
  cases s <;> simp

/-- THEOREM 3: for any contribution function, summing over the finite source
carrier is exactly the explicit four-term roadmap sum. -/
theorem alphaStrongResidualSource_univ_sum
    (c : AlphaStrongResidualSource -> ℚ) :
    (∑ s : AlphaStrongResidualSource, c s) =
      c .su7Breaking +
        c .threshold +
          c .threeLoopRG +
            c .higgsExtraRepresentation := by
  have huniv :
      (Finset.univ : Finset AlphaStrongResidualSource) =
        {AlphaStrongResidualSource.su7Breaking,
          AlphaStrongResidualSource.threshold,
          AlphaStrongResidualSource.threeLoopRG,
          AlphaStrongResidualSource.higgsExtraRepresentation} := by
    ext s
    cases s <;> simp
  rw [huniv]
  simp
  ring

namespace AlphaStrongResidualGapProducer

/-- THEOREM 4: the producer's explicit four-term gap is the sum over the
exhaustive finite source carrier. -/
theorem producedGap_eq_univ_sum
    (P : AlphaStrongResidualGapProducer) :
    P.producedGap =
      ∑ s : AlphaStrongResidualSource, P.contribution s := by
  rw [alphaStrongResidualSource_univ_sum]
  rfl

end AlphaStrongResidualGapProducer

/-! ## Independent-source closure certificate -/

/-- A closed four-source alpha_s residual receipt.

Each field is intended to be supplied by an independent physical calculation.
The single glue condition is the total alpha-level gap. -/
structure AlphaStrongFourSourceClosureReceipt where
  su7_breaking : ℚ
  threshold : ℚ
  three_loop_rg : ℚ
  higgs_extra_representation : ℚ
  total_gap :
    su7_breaking + threshold + three_loop_rg + higgs_extra_representation =
      alphaStrongTwoLoopSMDisplayedGap ℚ

namespace AlphaStrongFourSourceClosureReceipt

/-- The contribution function induced by a four-source closure receipt. -/
def contribution (R : AlphaStrongFourSourceClosureReceipt) :
    AlphaStrongResidualSource -> ℚ
  | .su7Breaking => R.su7_breaking
  | .threshold => R.threshold
  | .threeLoopRG => R.three_loop_rg
  | .higgsExtraRepresentation => R.higgs_extra_representation

/-- THEOREM 5: a four-source closure receipt induces the P520 residual-gap
producer. -/
def toGapProducer
    (R : AlphaStrongFourSourceClosureReceipt) :
    AlphaStrongResidualGapProducer where
  contribution := R.contribution
  total_gap := by
    simpa [contribution] using R.total_gap

/-- THEOREM 6: the finite-carrier sum of the four independently supplied
sources is exactly the alpha-level residual target. -/
theorem univ_sum_eq_gap
    (R : AlphaStrongFourSourceClosureReceipt) :
    (∑ s : AlphaStrongResidualSource, R.contribution s) =
      alphaStrongTwoLoopSMDisplayedGap ℚ := by
  rw [alphaStrongResidualSource_univ_sum]
  simpa [contribution] using R.total_gap

/-- THEOREM 7: the four-source closure receipt transports to the exact
inverse-coupling correction `-89000/128511`. -/
theorem inverseCorrection_eq_target
    (R : AlphaStrongFourSourceClosureReceipt) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource, R.contribution s) =
      alphaStrongResidualInverseCorrectionNeeded ℚ := by
  rw [R.univ_sum_eq_gap,
    alphaStrongResidualInverseCorrection_eq_inverseGapImage]

/-- THEOREM 8: the four-source closure receipt closes the displayed strong
coupling after inverse-coordinate transport. -/
theorem closes_displayedAlpha
    (R : AlphaStrongFourSourceClosureReceipt) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (∑ s : AlphaStrongResidualSource, R.contribution s)) =
      alphaStrongDisplayed ℚ := by
  rw [R.inverseCorrection_eq_target]
  exact alphaStrongResidualInverseCorrection_closes_displayedAlpha

/-- THEOREM 9: every four-source closure receipt has a strictly positive
source contribution somewhere. -/
theorem exists_positive_source
    (R : AlphaStrongFourSourceClosureReceipt) :
    ∃ s : AlphaStrongResidualSource, 0 < R.contribution s :=
  R.toGapProducer.exists_positive_source

end AlphaStrongFourSourceClosureReceipt

/-- Compact receipt for the closed four-source alpha_s residual producer
surface. -/
structure AlphaStrongFourSourceClosureCertificate where
  source_exhaustive :
    ∀ s : AlphaStrongResidualSource,
      s = .su7Breaking ∨
        s = .threshold ∨
          s = .threeLoopRG ∨
            s = .higgsExtraRepresentation
  finite_sum :
    ∀ c : AlphaStrongResidualSource -> ℚ,
      (∑ s : AlphaStrongResidualSource, c s) =
        c .su7Breaking +
          c .threshold +
            c .threeLoopRG +
              c .higgsExtraRepresentation
  closure_to_inverse_target :
    ∀ R : AlphaStrongFourSourceClosureReceipt,
      inverseCorrectionFromAlphaGap
          (alphaStrongTwoLoopSMOutput ℚ)
          (∑ s : AlphaStrongResidualSource, R.contribution s) =
        alphaStrongResidualInverseCorrectionNeeded ℚ
  closure_to_displayed_alpha :
    ∀ R : AlphaStrongFourSourceClosureReceipt,
      (1 : ℚ) /
          (alphaStrongTwoLoopSMOutputInverse ℚ +
            inverseCorrectionFromAlphaGap
              (alphaStrongTwoLoopSMOutput ℚ)
              (∑ s : AlphaStrongResidualSource, R.contribution s)) =
        alphaStrongDisplayed ℚ

/-- THEOREM 10: the closed four-source alpha_s residual producer certificate. -/
theorem alphaStrongFourSourceClosureCertificate :
    AlphaStrongFourSourceClosureCertificate where
  source_exhaustive := alphaStrongResidualSource_exhaustive
  finite_sum := alphaStrongResidualSource_univ_sum
  closure_to_inverse_target := fun R => R.inverseCorrection_eq_target
  closure_to_displayed_alpha := fun R => R.closes_displayedAlpha

end StandardModelConstraint
end SaturationMonoid
