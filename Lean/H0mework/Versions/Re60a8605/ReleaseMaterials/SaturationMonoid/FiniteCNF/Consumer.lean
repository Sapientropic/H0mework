import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Action
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointMarginal
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Pruned
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Encoding
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FaceReduction

/-!
# Direct consumers of the original CNF marginal source

The generated marginal mass is the original zero coefficient and projected
uniform-source mass. The source-support decision program consumes the same
Boolean answer, including through the fixed parser on every bit string.
-/

namespace SaturationMonoid.ComplexityProjection.SATSource

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedFiniteEffectiveCoefficient

/-- The generated joint clause contraction preserves the full original zero projector. -/
theorem zeroProjector_subsumption {n : Nat} (formula : CNFFormula n) :
    zeroProjector (Subsumption.reduce formula) = zeroProjector formula := by
  apply LinearMap.ext
  intro source
  funext assignment
  simp only [zeroProjector_apply, Subsumption.reduce_eval]

theorem cleanReadout_eq_coefficient {n : Nat} (formula : CNFFormula n) :
    SATJoint.cleanReadout formula =
      (effectiveCoefficient (violationCount formula) 0 : ℤ) := by
  rw [SATJoint.cleanReadout_eq_count, effectiveCoefficient_eq_card_filter]
  simp only [violationCount_eq_zero_iff_eval]
  rfl

theorem cleanReadout_pos_iff_satisfiable {n : Nat} (formula : CNFFormula n) :
    0 < SATJoint.cleanReadout formula ↔ CNFSatisfiable formula := by
  rw [cleanReadout_eq_coefficient, Int.natCast_pos]
  exact effectiveCoefficient_pos_iff_satisfiable formula

theorem faceReadout_eq_coefficient {n : Nat} (formula : CNFFormula n) :
    SATJoint.faceReadout formula =
      (effectiveCoefficient (violationCount formula) 0 : ℤ) := by
  rw [SATJoint.faceReadout_eq_count, effectiveCoefficient_eq_card_filter]
  simp only [violationCount_eq_zero_iff_eval]
  rfl

theorem faceReadout_pos_iff_satisfiable {n : Nat} (formula : CNFFormula n) :
    0 < SATJoint.faceReadout formula ↔ CNFSatisfiable formula := by
  rw [faceReadout_eq_coefficient, Int.natCast_pos]
  exact effectiveCoefficient_pos_iff_satisfiable formula

/-- Actual marginal integration preserves the original zero-energy multiplicity. -/
theorem marginalReadout_eq_coefficient {n : Nat} (formula : CNFFormula n) :
    SATJoint.marginalReadout formula =
      (effectiveCoefficient (violationCount formula) 0 : ℤ) := by
  rw [SATJoint.marginalReadout_eq_count, effectiveCoefficient_eq_card_filter]
  simp only [violationCount_eq_zero_iff_eval]
  rfl

theorem marginalReadout_eq_projected_mass {n : Nat} (formula : CNFFormula n) :
    (SATJoint.marginalReadout formula : ℚ) =
      sourceMass n (zeroProjector formula (uniformSeed n)) := by
  rw [marginalReadout_eq_coefficient, sourceMass_zeroProjector_eq_coefficient]
  simp only [Int.cast_natCast]

theorem marginalReadout_pos_iff_satisfiable {n : Nat} (formula : CNFFormula n) :
    0 < SATJoint.marginalReadout formula ↔ CNFSatisfiable formula := by
  rw [marginalReadout_eq_coefficient, Int.natCast_pos]
  exact effectiveCoefficient_pos_iff_satisfiable formula

theorem marginalReadout_eq_zero_iff_unsatisfiable {n : Nat} (formula : CNFFormula n) :
    SATJoint.marginalReadout formula = 0 ↔ ¬ CNFSatisfiable formula := by
  rw [marginalReadout_eq_coefficient, Int.natCast_eq_zero]
  exact effectiveCoefficient_eq_zero_iff_unsatisfiable formula

/-- The source-support Boolean program agrees with the generated scalar's sign. -/
theorem decideSource_eq_marginalDecision {n : Nat} (formula : CNFFormula n) :
    Shared.decideSource formula = decide (0 < SATJoint.marginalReadout formula) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Shared.decideSource_correct, decide_eq_true_eq,
    marginalReadout_pos_iff_satisfiable]

namespace Encoding

theorem decideBits_eq_cleanDecision (bits : List Bool) :
    decideBits bits =
      match parse bits with
      | none => false
      | some input => decide (0 < SATJoint.cleanReadout input.2) := by
  cases parsed : parse bits with
  | none => simp [decideBits, parsed]
  | some input =>
      simp only [decideBits, parsed]
      apply Bool.eq_iff_iff.mpr
      simp only [Dense.decideFormula_correct, decide_eq_true_eq,
        cleanReadout_pos_iff_satisfiable]

theorem decideBits_eq_faceDecision (bits : List Bool) :
    decideBits bits =
      match parse bits with
      | none => false
      | some input => decide (0 < SATJoint.faceReadout input.2) := by
  cases parsed : parse bits with
  | none => simp [decideBits, parsed]
  | some input =>
      simp only [decideBits, parsed]
      apply Bool.eq_iff_iff.mpr
      simp only [Dense.decideFormula_correct, decide_eq_true_eq,
        faceReadout_pos_iff_satisfiable]

theorem decideBits_iff_rootVerify (bits : List Bool) :
    decideBits bits = true ↔
      ∃ input : Input, parse bits = some input ∧
        ∃ assignment : Nat → Bool,
          CNFSATVerify input.2 (CNFSATNode.root input.1) assignment := by
  rw [decideBits_correct]
  simp only [cnfRoot_hasWitness_iff_satisfiable]

/-- Execute the source-support algorithm after the same fixed parser. -/
def decideSourceBits (bits : List Bool) : Bool :=
  match parse bits with
  | none => false
  | some input => Shared.decideSource input.2

theorem decideSourceBits_eq_decideBits (bits : List Bool) :
    decideSourceBits bits = decideBits bits := by
  cases parsed : parse bits with
  | none => simp only [decideSourceBits, decideBits, parsed]
  | some input =>
      simp only [decideSourceBits, decideBits, parsed]
      apply Bool.eq_iff_iff.mpr
      rw [Shared.decideSource_correct, Dense.decideFormula_correct]

/-- Every bit string reaches the same marginal source or the parser's invalid branch. -/
theorem decideSourceBits_eq_marginalDecision (bits : List Bool) :
    decideSourceBits bits =
      match parse bits with
      | none => false
      | some input => decide (0 < SATJoint.marginalReadout input.2) := by
  cases parsed : parse bits with
  | none => simp only [decideSourceBits, parsed]
  | some input =>
      simpa only [decideSourceBits, parsed] using decideSource_eq_marginalDecision input.2

theorem decideSourceBits_yes_iff (bits : List Bool) :
    decideSourceBits bits = true ↔
      ∃ input : Input, parse bits = some input ∧ 0 < SATJoint.marginalReadout input.2 := by
  rw [decideSourceBits_eq_decideBits, decideBits_correct]
  simp only [marginalReadout_pos_iff_satisfiable]

theorem decideSourceBits_no_iff (bits : List Bool) :
    decideSourceBits bits = false ↔
      parse bits = none ∨
        ∃ input : Input, parse bits = some input ∧ SATJoint.marginalReadout input.2 = 0 := by
  cases parsed : parse bits with
  | none => simp [decideSourceBits, parsed]
  | some input =>
      simp only [decideSourceBits, parsed, Shared.decideSource_no,
        marginalReadout_eq_zero_iff_unsatisfiable, Option.some.injEq,
        Option.some_ne_none, false_or]
      constructor
      · intro unsatisfiable
        exact ⟨input, rfl, unsatisfiable⟩
      · rintro ⟨other, same, unsatisfiable⟩
        subst other
        exact unsatisfiable

end Encoding
end SaturationMonoid.ComplexityProjection.SATSource
