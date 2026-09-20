import H0mework.Arithmetic.PrimeShadow.P870

/-!
# Proposition 871: the P870 spectrum generator is still Goldbach-strength

P870 removed `PrimeExponent` from the raw SU(7) spectrum cell.  This file checks
whether that move is already enough.

It is not.

Because the per-fiber generator still stores both:

* a support cell with raw residual zero;
* a projection law proving the support weights are prime,

the every-even-fiber statement is still equivalent to ordinary even Goldbach.
This theorem prevents the next step from mistaking a shifted proof obligation
for an independent producer.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Goldbach constructs the current P870 spectrum generator -/

/-- A one-cell raw SU(7) spectrum generator from a Goldbach prime pair. -/
def spectrumGenerator_of_goldbachPair
    {n : ℕ} (p q : PrimeExponent)
    (hsum : 2 * n = p.1 + q.1) :
    SU7BranchingSpectrumGenerator n :=
  let cell : SU7BranchingSpectrumCell n :=
    { branch := SU3FlagSchubertCell.e
      leftWeight := p.1
      rightWeight := q.1 }
  { family :=
      { spectrumCells := [cell]
        representationWeight := fun _ => 1 }
    primeProjectionLaw := by
      intro C hC _hwt
      have hcell : C = cell := by
        simpa using hC
      subst C
      exact ⟨p.2, q.2⟩
    supportCell := cell
    support_mem := by simp
    support_weight_positive := by simp
    support_rawResidual_zero := by
      change ((p.1 + q.1 : ℤ) - (2 * n : ℤ) = 0)
      omega }

/-- THEOREM 1: ordinary even Goldbach produces the current P870 spectrum
generator on every even fiber. -/
theorem spectrumGeneratorEveryEvenFiber_of_evenGoldbach
    (H : EvenGoldbachStatement) :
    SU7BranchingSpectrumGeneratorEveryEvenFiber := by
  intro n hn
  rcases H n hn with ⟨p, q, hsum⟩
  exact ⟨spectrumGenerator_of_goldbachPair p q hsum⟩

/-- THEOREM 2: the current P870 spectrum-generator target is exactly
Goldbach-strength. -/
theorem spectrumGeneratorEveryEvenFiber_iff_evenGoldbach :
    SU7BranchingSpectrumGeneratorEveryEvenFiber ↔
      EvenGoldbachStatement := by
  constructor
  · exact evenGoldbach_of_spectrumGenerator
  · exact spectrumGeneratorEveryEvenFiber_of_evenGoldbach

/-! ## Certificate -/

/-- P871 certificate: removing `PrimeExponent` from the cell was necessary but
not sufficient.  The remaining existential support/projection package is still
equivalent to Goldbach. -/
structure SpectrumGeneratorGoldbachStrengthCertificate : Prop where
  goldbach_to_spectrum_generator :
    EvenGoldbachStatement ->
      SU7BranchingSpectrumGeneratorEveryEvenFiber
  spectrum_generator_to_goldbach :
    SU7BranchingSpectrumGeneratorEveryEvenFiber ->
      EvenGoldbachStatement
  iff_statement :
    SU7BranchingSpectrumGeneratorEveryEvenFiber ↔
      EvenGoldbachStatement

def spectrumGeneratorGoldbachStrengthCertificate :
    SpectrumGeneratorGoldbachStrengthCertificate where
  goldbach_to_spectrum_generator :=
    spectrumGeneratorEveryEvenFiber_of_evenGoldbach
  spectrum_generator_to_goldbach :=
    evenGoldbach_of_spectrumGenerator
  iff_statement :=
    spectrumGeneratorEveryEvenFiber_iff_evenGoldbach


end
end StandardModelConstraint
end SaturationMonoid
