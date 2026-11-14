import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionValueScalarCoimage
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionValuePairingDescentControl

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction.Regression

noncomputable section

private abbrev nilIntegerWord : nilAction.Generator →₀ ℤ :=
  Finsupp.single () (1 : ℤ)

private theorem nil_value_word_pairing_zero :
    valueWordPairing nilAction (emitted toggle true)
      (integerToValueWords nilAction nilIntegerWord) = 0 := by
  apply LinearMap.ext
  intro right
  have rightRepr : right = Finsupp.single () (right ()) := by
    apply Finsupp.ext
    intro generator
    cases generator
    simp
  rw [rightRepr]
  change valueWordEvaluation nilAction (emitted toggle true)
      (integerToValueWords nilAction nilIntegerWord) *
    valueWordEvaluation nilAction (emitted toggle true)
      (Finsupp.single () (right ())) = 0
  have leftRead : valueWordEvaluation nilAction (emitted toggle true)
      (integerToValueWords nilAction nilIntegerWord) = (2 : ZMod 4) := by
    rw [valueWordEvaluation_integer_square]
    exact (generated_single_equation nilAction true () 1).1
  have rightRead : valueWordEvaluation nilAction (emitted toggle true)
      (Finsupp.single () (right ())) = (right ()) * (2 : ZMod 4) := by
    simp [valueWordEvaluation, nilAction]
    rfl
  rw [leftRead, rightRead]
  have nil : (2 : ZMod 4) * 2 = 0 := by decide
  calc
    (2 : ZMod 4) * (right () * 2) = (right ()) * (2 * 2) := by ring
    _ = 0 := by rw [nil, mul_zero]

theorem nil_value_coimage_no_free_recovery :
    (¬ ∃ recover : valueWordCoimage nilAction (emitted toggle true) → ZMod 4,
      ∀ word : ValueWords nilAction,
        recover (SourceGeneratedScalarPerfectification.canonicalMap
          (valueWordPairing nilAction (emitted toggle true)) word) =
          valueWordEvaluation nilAction (emitted toggle true) word) ∧
    HEq (((valuePairingRoot nilAction).toLedgerRoot.generatedLedgerAt true
        ).entryDisposition (entry toggle true))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred true rfl rfl (Nat.le_refl _) :
          LedgerEntryEvolutionAt (network toggle) (entry toggle true) (entry toggle true))) ∧
    ((valuePairingRoot nilAction).toRoot.evolutionAt true).nextCurrent? = some true := by
  have noRecovery : ¬ ∃ recover : valueWordCoimage nilAction (emitted toggle true) → ZMod 4,
      ∀ word : ValueWords nilAction,
        recover (SourceGeneratedScalarPerfectification.canonicalMap
          (valueWordPairing nilAction (emitted toggle true)) word) =
          valueWordEvaluation nilAction (emitted toggle true) word := by
    rintro ⟨recover, all⟩
    have zero : SourceGeneratedScalarPerfectification.canonicalMap
        (valueWordPairing nilAction (emitted toggle true))
          (integerToValueWords nilAction nilIntegerWord) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact nil_value_word_pairing_zero
    have atWord := all (integerToValueWords nilAction nilIntegerWord)
    have atZero := all 0
    rw [zero] at atWord
    have readTwo : valueWordEvaluation nilAction (emitted toggle true)
        (integerToValueWords nilAction nilIntegerWord) = (2 : ZMod 4) := by
      rw [valueWordEvaluation_integer_square]
      exact (generated_single_equation nilAction true () 1).1
    rw [readTwo] at atWord
    have readZero : valueWordEvaluation nilAction (emitted toggle true) 0 = 0 :=
      map_zero _
    rw [map_zero, readZero] at atZero
    exact (by decide : (2 : ZMod 4) ≠ 0) (atWord.symm.trans atZero)
  have old := generated_value_pairing_ledger_next nilAction true
  exact ⟨noRecovery, old.2.2.1, old.2.2.2⟩

theorem generator_value_coimage_recovers_one_original_row_next :
    valueWordCoimageRecovery generatorOnlyAction (emitted toggle true)
        (SourceGeneratedScalarPerfectification.canonicalMap
          (valueWordPairing generatorOnlyAction (emitted toggle true))
          (integerToValueWords generatorOnlyAction (Finsupp.single () (1 : ℤ)))) = 1 ∧
    valueWordPairing generatorOnlyAction (emitted toggle true)
        (integerToValueWords generatorOnlyAction (Finsupp.single () (1 : ℤ)))
        (integerToValueWords generatorOnlyAction (Finsupp.single () (1 : ℤ))) = 1 ∧
    HEq (((valuePairingRoot generatorOnlyAction).toLedgerRoot.generatedLedgerAt true
        ).entryDisposition (entry toggle true))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred true rfl rfl (Nat.le_refl _) :
          LedgerEntryEvolutionAt (network toggle) (entry toggle true) (entry toggle true))) ∧
    ((valuePairingRoot generatorOnlyAction).toRoot.evolutionAt true).nextCurrent? =
      some true := by
  have old := generator_nonzero_pairing_descends_original_row_next
  have readOne : valueWordCoimageRecovery generatorOnlyAction (emitted toggle true)
      (SourceGeneratedScalarPerfectification.canonicalMap
        (valueWordPairing generatorOnlyAction (emitted toggle true))
        (integerToValueWords generatorOnlyAction (Finsupp.single () (1 : ℤ)))) = 1 := by
    rw [valueWordCoimageRecovery_integer_source]
    have source := (generated_single_equation generatorOnlyAction true () 1).1
    change ((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)
      ).freeEvaluation (Finsupp.single () 1) = 1 at source
    exact source
  have pairingOne : valueWordPairing generatorOnlyAction (emitted toggle true)
      (integerToValueWords generatorOnlyAction (Finsupp.single () (1 : ℤ)))
      (integerToValueWords generatorOnlyAction (Finsupp.single () (1 : ℤ))) = 1 :=
    (valueWordPairing_integer_square generatorOnlyAction (emitted toggle true)
      (Finsupp.single () 1) (Finsupp.single () 1)).trans old.2.1
  exact ⟨readOne, pairingOne, old.2.2.2.1, old.2.2.2.2⟩

end
end RawGeneratedRoot.CofinalAction.Regression
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
