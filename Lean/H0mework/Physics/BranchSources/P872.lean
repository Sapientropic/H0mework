import H0mework.Arithmetic.PrimeShadow.P871

/-!
# Proposition 872: global SU(7) branching-spectrum law

P871 shows that the per-fiber P870 generator is still Goldbach-strength.  The
reason is structural: the conclusion is hidden in an existential support cell
on each even fiber.

This file removes that existential packaging.  A global branching-spectrum law
is a pair of total SU(7) spectrum weight functions, together with two explicit
laws:

* the spectrum weights project to prime edges;
* the spectrum weights balance the even color-loop fiber.

It still has Goldbach strength, but the obligation is no longer hidden inside a
`Nonempty` support package.  The next producer has to generate these two laws
from the actual SU(7) representation spectrum.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Global spectrum law -/

/-- A global SU(7) branching-spectrum law for all even fibers.

The `leftWeight` / `rightWeight` fields are raw natural weights.  Primality and
balance are law fields, not pre-stored `PrimeExponent` data. -/
structure SU7GlobalBranchingSpectrumLaw where
  branch : (n : ℕ) -> 2 ≤ n -> SU3FlagSchubertCell
  leftWeight : (n : ℕ) -> 2 ≤ n -> ℕ
  rightWeight : (n : ℕ) -> 2 ≤ n -> ℕ
  leftPrime :
    ∀ n : ℕ, ∀ hn : 2 ≤ n, Nat.Prime (leftWeight n hn)
  rightPrime :
    ∀ n : ℕ, ∀ hn : 2 ≤ n, Nat.Prime (rightWeight n hn)
  balance :
    ∀ n : ℕ, ∀ hn : 2 ≤ n,
      2 * n = leftWeight n hn + rightWeight n hn

/-- The raw spectrum cell selected by a global law on one even fiber. -/
def spectrumCell_of_globalLaw
    (L : SU7GlobalBranchingSpectrumLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    SU7BranchingSpectrumCell n where
  branch := L.branch n hn
  leftWeight := L.leftWeight n hn
  rightWeight := L.rightWeight n hn

/-- THEOREM 1: the global law supplies the prime projection for its selected
raw spectrum cell. -/
theorem spectrumCellPrimeProjection_of_globalLaw
    (L : SU7GlobalBranchingSpectrumLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    SU7SpectrumCellPrimeProjection
      (spectrumCell_of_globalLaw L n hn) := by
  exact ⟨L.leftPrime n hn, L.rightPrime n hn⟩

/-- THEOREM 2: the global law supplies zero raw residual for its selected
spectrum cell. -/
theorem spectrumCell_rawResidual_zero_of_globalLaw
    (L : SU7GlobalBranchingSpectrumLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    (spectrumCell_of_globalLaw L n hn).rawResidual = 0 := by
  change (((L.leftWeight n hn + L.rightWeight n hn : ℕ) : ℤ) -
      ((2 * n : ℕ) : ℤ) = 0)
  have hbal : 2 * n = L.leftWeight n hn + L.rightWeight n hn :=
    L.balance n hn
  omega

/-! ## Global law produces P870 generator -/

/-- THEOREM 3: a global spectrum law computes the per-fiber raw spectrum
generator, with no per-fiber existential search. -/
def spectrumGenerator_of_globalLaw
    (L : SU7GlobalBranchingSpectrumLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    SU7BranchingSpectrumGenerator n :=
  let C := spectrumCell_of_globalLaw L n hn
  { family :=
      { spectrumCells := [C]
        representationWeight := fun _ => 1 }
    primeProjectionLaw := by
      intro D hD _hwt
      have hcell : D = C := by
        simpa using hD
      subst D
      exact spectrumCellPrimeProjection_of_globalLaw L n hn
    supportCell := C
    support_mem := by simp
    support_weight_positive := by simp
    support_rawResidual_zero :=
      spectrumCell_rawResidual_zero_of_globalLaw L n hn }

/-- THEOREM 4: a global spectrum law produces P870's every-even-fiber
generator. -/
theorem spectrumGeneratorEveryEvenFiber_of_globalLaw
    (L : SU7GlobalBranchingSpectrumLaw) :
    SU7BranchingSpectrumGeneratorEveryEvenFiber := by
  intro n hn
  exact ⟨spectrumGenerator_of_globalLaw L n hn⟩

/-- THEOREM 5: a global spectrum law produces the downstream Goldbach readout.
-/
theorem evenGoldbach_of_globalLaw
    (L : SU7GlobalBranchingSpectrumLaw) :
    EvenGoldbachStatement :=
  evenGoldbach_of_spectrumGenerator
    (spectrumGeneratorEveryEvenFiber_of_globalLaw L)

/-! ## Goldbach constructs such a global law by choice -/

/-- THEOREM 6: ordinary Goldbach supplies a global spectrum law by choosing
one prime pair per even fiber.  This theorem records the exact remaining
strength of the global law. -/
def globalLaw_of_evenGoldbach
    (H : EvenGoldbachStatement) :
    SU7GlobalBranchingSpectrumLaw where
  branch := fun _ _ => SU3FlagSchubertCell.e
  leftWeight := fun n hn =>
    (Classical.choose (H n hn)).1
  rightWeight := fun n hn =>
    (Classical.choose (Classical.choose_spec (H n hn))).1
  leftPrime := by
    intro n hn
    exact (Classical.choose (H n hn)).2
  rightPrime := by
    intro n hn
    exact (Classical.choose (Classical.choose_spec (H n hn))).2
  balance := by
    intro n hn
    exact Classical.choose_spec (Classical.choose_spec (H n hn))

/-- THEOREM 7: the global SU(7) branching-spectrum law is exactly
Goldbach-strength until its two law fields are produced from representation
theory. -/
theorem globalBranchingSpectrumLaw_iff_evenGoldbach :
    Nonempty SU7GlobalBranchingSpectrumLaw ↔ EvenGoldbachStatement := by
  constructor
  · intro hL
    rcases hL with ⟨L⟩
    exact evenGoldbach_of_globalLaw L
  · intro H
    exact ⟨globalLaw_of_evenGoldbach H⟩

/-! ## Certificate -/

/-- P872 certificate: per-fiber existential support has been replaced by a
global spectrum law.  The exact remaining producer debt is to derive the
prime-projection and balance fields from SU(7) representation theory. -/
structure GlobalBranchingSpectrumLawCertificate where
  law_to_generator :
    SU7GlobalBranchingSpectrumLaw ->
      SU7BranchingSpectrumGeneratorEveryEvenFiber
  law_to_goldbach :
    SU7GlobalBranchingSpectrumLaw -> EvenGoldbachStatement
  goldbach_to_law :
    EvenGoldbachStatement -> SU7GlobalBranchingSpectrumLaw
  iff_statement :
    Nonempty SU7GlobalBranchingSpectrumLaw ↔ EvenGoldbachStatement

def globalBranchingSpectrumLawCertificate :
    GlobalBranchingSpectrumLawCertificate where
  law_to_generator := spectrumGeneratorEveryEvenFiber_of_globalLaw
  law_to_goldbach := evenGoldbach_of_globalLaw
  goldbach_to_law := globalLaw_of_evenGoldbach
  iff_statement := globalBranchingSpectrumLaw_iff_evenGoldbach


end
end StandardModelConstraint
end SaturationMonoid
