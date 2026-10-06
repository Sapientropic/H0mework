import H0mework.Physics.MotherLaws.CurrentConsumer
import H0mework.Physics.MotherLaws.RestrictionConsumer
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherConductorOperands

open MotherClosedRestrictions MotherStreamLaws Topology

noncomputable section

def testSamples (test : SchwartzMap ℝ ℂ) : Stream :=
  pairStream (fun n => (test (((Encodable.decode (α := ℚ) n).getD 0 : ℚ) : ℝ)).re)
    (fun n => (test (((Encodable.decode (α := ℚ) n).getD 0 : ℚ) : ℝ)).im)

def testRead (samples : Stream) : ℝ → ℂ :=
  Rat.isDenseEmbedding_coe_real.isDenseInducing.extend
    (fun q => ⟨firstStream samples (Encodable.encode q),
      lastStream samples (Encodable.encode q)⟩)

theorem test_recovered (test : SchwartzMap ℝ ℂ) :
    testRead (testSamples test) = test := by
  apply Rat.isDenseEmbedding_coe_real.isDenseInducing.extend_unique
    (g := fun x => test x) _ test.continuous
  intro q
  simp only [testSamples, first_pair, last_pair, Encodable.encodek, Option.getD_some]

/-- Full coefficient and test samples, with the original finite address and scale. -/
def samples (coefficients : ℕ → ℝ) (test : SchwartzMap ℝ ℂ)
    (scale : ℝ) (cutoff : ℕ) (increment : Bool) : Stream
  | 0 => cutoff
  | 1 => if increment then 1 else 0
  | 2 => scale
  | address + 3 => pairStream coefficients (testSamples test) address

def tail (samples : Stream) : Stream := fun address => samples (address + 3)

def coefficientsRead (samples : Stream) : ℕ → ℝ := firstStream (tail samples)

def functionRead (samples : Stream) : ℝ → ℂ := testRead (lastStream (tail samples))

def encode (coefficients : ℕ → ℝ) (test : SchwartzMap ℝ ℂ)
    (scale : ℝ) (cutoff : ℕ) (increment : Bool) : MotherStreamFormation.Carrier :=
  CurrentSampleAction.readInverse (samples coefficients test scale cutoff increment)

theorem read_encode (coefficients : ℕ → ℝ) (test : SchwartzMap ℝ ℂ)
    (scale : ℝ) (cutoff : ℕ) (increment : Bool) :
    MotherStreamFormation.read (encode coefficients test scale cutoff increment) =
      samples coefficients test scale cutoff increment :=
  CurrentSampleAction.read_readInverse _

theorem operands_recovered (coefficients : ℕ → ℝ) (test : SchwartzMap ℝ ℂ)
    (scale : ℝ) (cutoff : ℕ) (increment : Bool) :
    let raw := MotherStreamFormation.read (encode coefficients test scale cutoff increment)
    coefficientsRead raw = coefficients ∧ functionRead raw = test ∧
      raw 2 = scale ∧ Nat.floor (raw 0) = cutoff ∧
      (raw 1 ≠ 0 ↔ increment = true) := by
  dsimp only
  rw [read_encode]
  have tail_eq : tail (samples coefficients test scale cutoff increment) =
      pairStream coefficients (testSamples test) := rfl
  simp only [coefficientsRead, functionRead, tail_eq, first_pair, last_pair,
    test_recovered, samples, Nat.floor_natCast, true_and]
  cases increment <;> simp

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherConductorOperands
