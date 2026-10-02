import H0mework.Physics.MotherLaws.CompletionDensity
import H0mework.Physics.MotherLaws.CompletionRange
import H0mework.Versions.R2.Physics.MotherLaws.FiniteEvaluation

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLawCompletion

open Set UniformSpace MotherFamilyOccurrence
open Stage9C.Revision
open scoped Topology

noncomputable section

theorem finiteLaw_eq_polynomial (n m : ℕ) (visit : MotherVisit) :
    MotherFiniteLaws.finiteLaw n m visit =
      readPolynomials n m (MotherFiniteLaws.polynomial n m visit) := by
  ext input output
  exact MotherFiniteLaws.eval_polynomial n m visit input output

theorem finiteLaw_dense (n m : ℕ) : DenseRange (MotherFiniteLaws.finiteLaw n m) := by
  intro f
  apply closure_mono (s := Set.range (readPolynomials n m)) ?_ (polynomials_dense n m f)
  rintro _ ⟨p, rfl⟩
  obtain ⟨code, generated⟩ := MotherFiniteLaws.every_polynomial p
  refine ⟨SpinPair.visit (10 + code), ?_⟩
  rw [finiteLaw_eq_polynomial, generated]

/-- The finite source-law range is fixed before any target law or process. -/
abbrev Raw (n m : ℕ) := RangeCompletion.Raw (MotherFiniteLaws.finiteLaw n m)
abbrev Law (n m : ℕ) := Completion (Raw n m)

def lawRead (n m : ℕ) : Law n m → C((Fin n → ℝ), (Fin m → ℝ)) :=
  RangeCompletion.lawRead (MotherFiniteLaws.finiteLaw n m)

theorem lawRead_surjective (n m : ℕ) : Function.Surjective (lawRead n m) :=
  RangeCompletion.lawRead_surjective _ (finiteLaw_dense n m)

theorem lawRead_uniformEmbedding (n m : ℕ) : IsUniformEmbedding (lawRead n m) :=
  RangeCompletion.lawRead_uniformEmbedding _

def eval (n m : ℕ) (law : Law n m) (input : Fin n → ℝ) : Fin m → ℝ :=
  Completion.extension (fun raw : Raw n m => raw.val input) law

theorem eval_eq (n m : ℕ) (law : Law n m) (input : Fin n → ℝ) :
    eval n m law input = lawRead n m law input :=
  RangeCompletion.eval_eq _ law input

theorem eval_jointly_continuous (n m : ℕ) :
    Continuous (fun pair : Law n m × (Fin n → ℝ) => eval n m pair.1 pair.2) :=
  RangeCompletion.eval_jointly_continuous _

def ofVisit (n m : ℕ) (visit : MotherVisit) : Law n m :=
  (⟨MotherFiniteLaws.finiteLaw n m visit, ⟨visit, rfl⟩⟩ : Raw n m)

theorem ofVisit_read (n m : ℕ) (visit : MotherVisit) :
    lawRead n m (ofVisit n m visit) = MotherFiniteLaws.finiteLaw n m visit :=
  RangeCompletion.lawRead_coe _ _

theorem ofVisit_eval (n m : ℕ) (visit : MotherVisit) (input : Fin n → ℝ) :
    eval n m (ofVisit n m visit) input = MotherFiniteLaws.eval n m visit input := by
  rw [eval_eq, ofVisit_read]
  rfl

theorem every_continuous_law (n m : ℕ) (target : C((Fin n → ℝ), (Fin m → ℝ))) :
    ∃! law : Law n m, lawRead n m law = target := by
  obtain ⟨law, generated⟩ := lawRead_surjective n m target
  exact ⟨law, generated, fun other same =>
    (lawRead_uniformEmbedding n m).injective (same.trans generated.symm)⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLawCompletion
