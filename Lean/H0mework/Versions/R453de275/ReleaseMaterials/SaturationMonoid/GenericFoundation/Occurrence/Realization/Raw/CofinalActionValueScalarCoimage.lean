import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionValuePairingDescent
import H0mework.Realization.Perfectification.ScalarCoimage

/-! The actual receipt evaluator generates its value-ring scalar extension and coimage.
These formal coefficient words are algebraic readouts of the same occurrence,
not new events or a physical action. The old integer words embed exactly. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction

open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open SourceGeneratedScalarPerfectification

noncomputable section
variable {D : Dynamics.{0}} {Carrier : Type} [CommRing Carrier]

abbrev ValueWords (law : Law D Carrier) := law.Generator →₀ Carrier

def integerToValueWords (law : Law D Carrier) :
    (law.Generator →₀ ℤ) →ₗ[ℤ] ValueWords law :=
  Finsupp.linearCombination ℤ fun generator => Finsupp.single generator (1 : Carrier)

def valueWordEvaluation (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    ValueWords law →ₗ[Carrier] Carrier :=
  Finsupp.linearCombination Carrier
    (law.evaluatorAt (receiptFromCompiler (D := D) occurrence)).root

def valueWordPairing (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    ValueWords law →ₗ[Carrier] Module.Dual Carrier (ValueWords law) :=
  LinearMap.mk₂ Carrier
    (fun left right => valueWordEvaluation law occurrence left *
      valueWordEvaluation law occurrence right)
    (by intro left₁ left₂ right; simp [map_add, add_mul])
    (by intro coefficient left right; simp [map_smul]; ring)
    (by intro left right₁ right₂; rw [map_add, mul_add])
    (by intro coefficient left right; simp [map_smul]; ring)

theorem integerToValueWords_single (law : Law D Carrier)
    (generator : law.Generator) (coefficient : ℤ) :
    integerToValueWords law (Finsupp.single generator coefficient) =
      Finsupp.single generator (coefficient : Carrier) := by
  simp [integerToValueWords, Finsupp.linearCombination_single]

theorem valueWordEvaluation_integer_square
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state)
    (word : law.Generator →₀ ℤ) :
    valueWordEvaluation law occurrence (integerToValueWords law word) =
      ((faithfulLaw law).faithfulAt occurrence).freeEvaluation word := by
  induction word using Finsupp.induction_linear with
  | zero => exact (map_zero _).symm
  | add left right left_ih right_ih =>
      simp only [map_add, left_ih, right_ih]
      exact (map_add _ left right).symm
  | single generator coefficient =>
      rw [integerToValueWords_single]
      simp only [valueWordEvaluation, Finsupp.linearCombination_single]
      change (coefficient : Carrier) *
        (law.evaluatorAt (receiptFromCompiler (D := D) occurrence)).root generator =
          ((faithfulLaw law).faithfulAt occurrence).freeEvaluation
            (Finsupp.single generator coefficient)
      have source := ((faithfulLaw law).faithfulAt occurrence).freeEvaluation_single
        generator coefficient
      change _ = coefficient •
        (law.evaluatorAt (receiptFromCompiler (D := D) occurrence)).root generator
        at source
      rw [source, zsmul_eq_mul]

theorem valueWordPairing_integer_square
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state)
    (left right : law.Generator →₀ ℤ) :
    valueWordPairing law occurrence (integerToValueWords law left)
      (integerToValueWords law right) = valuePairing law occurrence left right := by
  change valueWordEvaluation law occurrence (integerToValueWords law left) *
      valueWordEvaluation law occurrence (integerToValueWords law right) = _
  rw [valueWordEvaluation_integer_square, valueWordEvaluation_integer_square]
  rfl

abbrev valueWordCoimage (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :=
  SourceGeneratedScalarPerfectification.PerfectificationCarrier
    (valueWordPairing law occurrence)

theorem valueWord_coimage_embedding_square
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    (SourceGeneratedScalarPerfectification.dualEmbedding
      (valueWordPairing law occurrence)).comp
      (SourceGeneratedScalarPerfectification.canonicalMap
        (valueWordPairing law occurrence)) =
      valueWordPairing law occurrence :=
  SourceGeneratedScalarPerfectification.dualEmbedding_comp_canonicalMap _

theorem valueWordPairing_self_zero_iff [IsReduced Carrier]
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state)
    (word : ValueWords law) :
    valueWordPairing law occurrence word word = 0 ↔
      valueWordEvaluation law occurrence word = 0 := by
  change valueWordEvaluation law occurrence word *
      valueWordEvaluation law occurrence word = 0 ↔ _
  constructor
  · intro zero
    apply IsReduced.eq_zero
    exact IsNilpotent.mk _ 2 (by simpa only [pow_two] using zero)
  · intro zero
    rw [zero, zero_mul]

theorem valueWordPairing_kernel_eq_evaluation_kernel [IsReduced Carrier]
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    LinearMap.ker (valueWordPairing law occurrence) =
      LinearMap.ker (valueWordEvaluation law occurrence) := by
  ext word
  change valueWordPairing law occurrence word = 0 ↔
    valueWordEvaluation law occurrence word = 0
  constructor
  · intro zero
    have atWord := LinearMap.congr_fun zero word
    exact (valueWordPairing_self_zero_iff law occurrence word).mp atWord
  · intro zero
    apply LinearMap.ext
    intro right
    change valueWordEvaluation law occurrence word *
      valueWordEvaluation law occurrence right = 0
    rw [zero, zero_mul]

def valueWordCoimageRecovery [IsReduced Carrier]
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    valueWordCoimage law occurrence →ₗ[Carrier] Carrier :=
  SourceGeneratedScalarPerfectification.canonicalFactor
    (valueWordPairing law occurrence)
    (valueWordEvaluation law occurrence)
    (valueWordPairing_kernel_eq_evaluation_kernel law occurrence).le

theorem valueWordCoimageRecovery_integer_source [IsReduced Carrier]
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state)
    (word : law.Generator →₀ ℤ) :
    valueWordCoimageRecovery law occurrence
        (SourceGeneratedScalarPerfectification.canonicalMap
          (valueWordPairing law occurrence) (integerToValueWords law word)) =
      ((faithfulLaw law).faithfulAt occurrence).freeEvaluation word := by
  rw [← valueWordEvaluation_integer_square law occurrence word]
  exact LinearMap.congr_fun
    (SourceGeneratedScalarPerfectification.canonicalFactor_comp
      (valueWordPairing law occurrence) (valueWordEvaluation law occurrence)
      (valueWordPairing_kernel_eq_evaluation_kernel law occurrence).le) _

end
end RawGeneratedRoot.CofinalAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
