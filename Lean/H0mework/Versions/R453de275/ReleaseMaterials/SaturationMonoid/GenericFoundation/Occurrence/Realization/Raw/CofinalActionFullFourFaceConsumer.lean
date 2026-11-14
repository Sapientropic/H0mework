import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionFullFourFace
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionScalarPairingNonzeroControl

/-!
# The original nonzero relation survives the complete four-face source

The true Boolean event evaluates an actual relation to one. Its quotient
completion kills that boundary, but the source's complete free lattice gives
the existing four-face producer a nonzero evaluation and coimage class. The
old unsound residual remains installed at that same event, with its old row
and generated next. This distinguishes full-source structure from an invalid
quotient compression without selecting a target pairing or positive branch.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction.Regression

open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

noncomputable section

private abbrev relationWord : FreeLattice action := Finsupp.single () (1 : ℤ)

theorem true_full_free_pairing_one :
    freeSourcePairing action (emitted toggle true)
      relationWord relationWord = 1 := by
  change ((faithfulLaw action).faithfulAt (emitted toggle true)).freeEvaluation
      relationWord *
    ((faithfulLaw action).faithfulAt (emitted toggle true)).freeEvaluation
      relationWord = 1
  have evaluated :
      ((faithfulLaw action).faithfulAt (emitted toggle true)).freeEvaluation
        relationWord = 1 := true_actual_equation
  calc
    _ = (1 : ℤ) * 1 := congrArg₂ (· * ·) evaluated evaluated
    _ = 1 := by norm_num

/-- The full source-generated coimage retains the relation value erased by
the separate completion quotient, while the original root records exactly
why descent fails. -/
theorem true_full_fourface_excludes_quotient_collapse :
    let generated := fullGenerated action true
    generated.embedding (generated.canonical relationWord) relationWord = 1 ∧
    generated.canonical relationWord ≠ 0 ∧
    trueHistory.completionProjection
      (installedRelationAction action (emitted toggle true) trueRelation) = 0 ∧
    (¬ ∃ factor : trueHistory.CompletionCarrier →+ ℤ,
      ∀ value : trueHistory.generatorClosure,
        factor (trueHistory.completionProjection value) =
          ((faithfulLaw action).faithfulAt (emitted toggle true)).freeEvaluation
            value.1) ∧
    ∃ obstruction : GeneratedUnsoundRelationObstructionAt
        ((faithfulLaw action).faithfulAt (emitted toggle true)),
      ∃ coordinate : GeneratedRelationResidualCoordinateAt
          ((faithfulLaw action).faithfulAt (emitted toggle true)),
        HEq ((fullRoot action).source.projectionLaw.outcomeAt
            ((residualToFullInstallation action).embed (.component PUnit.unit))
            ((fullRoot action).emitted true))
          ((residualRoot action).source.projectionLaw.outcomeAt
            (.component PUnit.unit) ((residualRoot action).emitted true)) ∧
        (residualRoot action).source.projectionLaw.outcomeAt
            (.component PUnit.unit) ((residualRoot action).emitted true) =
          .inl ⟨PUnit.unit, .unsound obstruction coordinate⟩ ∧
        coordinate.coordinate ≠ 0 ∧
        HEq (((fullRoot action).toLedgerRoot.generatedLedgerAt true
            ).entryDisposition (entry toggle true))
          (LedgerEntryDispositionAt.evolved
            (LedgerEntryEvolutionAt.transferred true
              rfl rfl (Nat.le_refl _) :
                LedgerEntryEvolutionAt (network toggle)
                  (entry toggle true) (entry toggle true))) ∧
        ((fullRoot action).toRoot.evolutionAt true).nextCurrent? =
          some true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, row, next⟩ :=
    full_faces_original_receipt_ledger_next action true
  have dual := full_dual_equation action true
  have value : (fullGenerated action true).embedding
      ((fullGenerated action true).canonical relationWord) relationWord = 1 := by
    have atWord := LinearMap.congr_fun dual relationWord
    have atPair := LinearMap.congr_fun atWord relationWord
    change (fullGenerated action true).embedding
      ((fullGenerated action true).canonical relationWord) relationWord =
        freeSourcePairing action (emitted toggle true)
          relationWord relationWord at atPair
    exact atPair.trans true_full_free_pairing_one
  have retained : (fullGenerated action true).canonical relationWord ≠ 0 := by
    intro vanished
    rw [vanished, map_zero] at value
    norm_num at value
  obtain ⟨obstruction, coordinate, oldResidual, nonzero, _row, _next⟩ :=
    true_event_installed_unsound
  refine ⟨value, retained, true_relation_installed_boundary.2,
    true_no_descended_evaluator, obstruction, coordinate,
    (residualToFullInstallation action).outcome_heq (emitted toggle true)
      (.component PUnit.unit), oldResidual, nonzero, ?_, ?_⟩
  · exact row
  · exact next

private abbrev generatorWord : FreeLattice generatorOnlyAction :=
  Finsupp.single () (1 : ℤ)

private def generatorVector : generatorHistory.generatorClosure :=
  ⟨generatorWord, generator_single_in_closure⟩

/-- In the separate sound law epoch, the full free pairing is nonzero and
agrees exactly with the original quotient pairing. The existing four-face
coimage consumes that same value, original row and next. -/
theorem generator_sound_full_fourface_square :
    ∃ soundness : GeneratedRelationSoundnessAt
        ((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)),
      freeSourcePairing generatorOnlyAction (emitted toggle true)
          generatorWord generatorWord =
        rankOnePairing
          (((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)
            ).completionEvaluation soundness)
          generatorClass generatorClass ∧
      (fullGenerated generatorOnlyAction true).embedding
        ((fullGenerated generatorOnlyAction true).canonical generatorWord)
          generatorWord = 1 ∧
      (fullRoot generatorOnlyAction).source.projectionLaw.outcomeAt
          (.component PUnit.unit)
          ((fullRoot generatorOnlyAction).emitted true) =
        .inl ⟨PUnit.unit,
          freeSourcePairing generatorOnlyAction (emitted toggle true)⟩ ∧
      HEq (((fullRoot generatorOnlyAction).toLedgerRoot.generatedLedgerAt true
          ).entryDisposition (entry toggle true))
        (LedgerEntryDispositionAt.evolved
          (LedgerEntryEvolutionAt.transferred true
            rfl rfl (Nat.le_refl _) :
              LedgerEntryEvolutionAt (network toggle)
                (entry toggle true) (entry toggle true))) ∧
      ((fullRoot generatorOnlyAction).toRoot.evolutionAt true).nextCurrent? =
        some true := by
  obtain ⟨soundness, _installed, one, _oldRow, _oldNext⟩ :=
    generator_nonzero_pairing_original_row_next
  have square := free_pairing_quotient_square generatorOnlyAction
    (emitted toggle true) soundness generatorVector generatorVector
  have sourceSquare :
      freeSourcePairing generatorOnlyAction (emitted toggle true)
          generatorWord generatorWord =
        rankOnePairing
          (((faithfulLaw generatorOnlyAction).faithfulAt (emitted toggle true)
            ).completionEvaluation soundness)
          generatorClass generatorClass := by
    exact square.symm
  have sourceOne : freeSourcePairing generatorOnlyAction (emitted toggle true)
      generatorWord generatorWord = 1 := sourceSquare.trans one
  have generatedOne :
      (fullGenerated generatorOnlyAction true).embedding
        ((fullGenerated generatorOnlyAction true).canonical generatorWord)
          generatorWord = 1 := by
    have atWord := LinearMap.congr_fun
      (full_dual_equation generatorOnlyAction true) generatorWord
    have atPair := LinearMap.congr_fun atWord generatorWord
    change (fullGenerated generatorOnlyAction true).embedding
        ((fullGenerated generatorOnlyAction true).canonical generatorWord)
          generatorWord =
        freeSourcePairing generatorOnlyAction (emitted toggle true)
          generatorWord generatorWord at atPair
    exact atPair.trans sourceOne
  obtain ⟨_, _, _, _, _, _, _, _, _, _, installed, _, row, next⟩ :=
    full_faces_original_receipt_ledger_next generatorOnlyAction true
  exact ⟨soundness, sourceSquare, generatedOne, installed, row, next⟩

#print axioms true_full_fourface_excludes_quotient_collapse
#print axioms generator_sound_full_fourface_square

end
end RawGeneratedRoot.CofinalAction.Regression
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
