import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionValuePairing
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionRegression
set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.Regression
noncomputable section
abbrev nilAction : Law toggle (ZMod 4) where
  Generator := Unit
  rootExposureAt := action.rootExposureAt
  rootExposure_root := action.rootExposure_root
  seedAt := action.seedAt
  continuationAt := action.continuationAt
  evaluatorAt := fun _ => RootedAccountedUnfolding.zero (fun _ : Unit => (2 : ZMod 4))

private abbrev word : nilAction.Generator →₀ ℤ := Finsupp.single () 1

theorem integral_actual_pairing_one :
    valuePairing action (emitted toggle true)
      (Finsupp.single () (1 : ℤ)) (Finsupp.single () (1 : ℤ)) = 1 := by
  change ((faithfulLaw action).faithfulAt (emitted toggle true)).freeEvaluation
      (Finsupp.single () (1 : ℤ)) *
    ((faithfulLaw action).faithfulAt (emitted toggle true)).freeEvaluation
      (Finsupp.single () (1 : ℤ)) = 1
  rw [true_actual_equation]
  norm_num

theorem nil_actual_nonzero :
    ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation word ≠ 0 := by
  have generated := (generated_single_equation nilAction true () 1).1
  change ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation word =
    (1 : ℤ) • (2 : ZMod 4) at generated
  rw [generated]
  change (2 : ZMod 4) ≠ 0
  decide

theorem nil_pairing_invisible :
    ∀ right : nilAction.Generator →₀ ℤ,
      valuePairing nilAction (emitted toggle true) word right = 0 := by
  intro right
  have rightWord : right = Finsupp.single () (right ()) := by
    apply Finsupp.ext
    intro generator
    cases generator
    simp
  rw [rightWord]
  have left := (generated_single_equation nilAction true () 1).1
  have value := (generated_single_equation nilAction true () (right ())).1
  change ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation word =
    (1 : ℤ) • (2 : ZMod 4) at left
  change ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation
    (Finsupp.single () (right ())) = (right ()) • (2 : ZMod 4) at value
  change ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation word *
    ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation
      (Finsupp.single () (right ())) = 0
  rw [left, value]
  simp only [zsmul_eq_mul]
  have nil : (2 : ZMod 4) * 2 = 0 := by decide
  calc
    (2 : ZMod 4) * (↑(right ()) * 2) = ↑(right ()) * (2 * 2) := by ring
    _ = 0 := by rw [nil, mul_zero]

/-- The same actual event and old row retain a nonzero source that a
nonreduced value pairing erases on every right word. -/
theorem nilpotent_pairing_loss_original_row_next :
    ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation word ≠ 0 ∧
    (∀ right : nilAction.Generator →₀ ℤ,
      valuePairing nilAction (emitted toggle true) word right = 0) ∧
    (valuePairingRoot nilAction).source.projectionLaw.outcomeAt
        (.component PUnit.unit) ((valuePairingRoot nilAction).emitted true) =
      .inl ⟨PUnit.unit, valuePairing nilAction (emitted toggle true)⟩ ∧
    HEq (((valuePairingRoot nilAction).toLedgerRoot.generatedLedgerAt true
        ).entryDisposition (entry toggle true))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred true rfl rfl (Nat.le_refl _) :
          LedgerEntryEvolutionAt (network toggle)
            (entry toggle true) (entry toggle true))) ∧
    ((valuePairingRoot nilAction).toRoot.evolutionAt true).nextCurrent? =
      some true := by
  have generated := generated_value_pairing_ledger_next nilAction true
  exact ⟨nil_actual_nonzero, nil_pairing_invisible,
    generated.1, generated.2.2.1, generated.2.2.2⟩

theorem integral_actual_pairing_distinguishes_zero :
    valuePairing action (emitted toggle true)
        (Finsupp.single () (1 : ℤ)) ≠
      valuePairing action (emitted toggle true) 0 := by
  intro same
  have atWord := LinearMap.congr_fun same (Finsupp.single () (1 : ℤ))
  rw [map_zero] at atWord
  exact one_ne_zero (integral_actual_pairing_one.symm.trans atWord)

theorem integral_actual_pairing_recovers_one :
    valuePairingRangeRecovery action (emitted toggle true)
        ⟨valuePairing action (emitted toggle true)
            (Finsupp.single () (1 : ℤ)),
          ⟨Finsupp.single () (1 : ℤ), rfl⟩⟩ = 1 := by
  exact (valuePairingRangeRecovery_actual action (emitted toggle true)
    (Finsupp.single () (1 : ℤ))).trans true_actual_equation

theorem nilpotent_pairing_fibre_strict :
    valuePairing nilAction (emitted toggle true) word =
        valuePairing nilAction (emitted toggle true) 0 ∧
      ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation word ≠
        ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation 0 := by
  constructor
  · apply LinearMap.ext
    intro right
    rw [nil_pairing_invisible right, map_zero, LinearMap.zero_apply]
  · rw [map_zero]
    exact nil_actual_nonzero

theorem nilpotent_no_full_pairing_recovery
    (recover : ((nilAction.Generator →₀ ℤ) →ₗ[ℤ] ZMod 4) → ZMod 4) :
    ¬ ∀ candidate : nilAction.Generator →₀ ℤ,
      recover (valuePairing nilAction (emitted toggle true) candidate) =
        ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation
          candidate := by
  intro all
  have strict := nilpotent_pairing_fibre_strict
  have sameValue :
      ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation word =
        ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation 0 :=
    (all word).symm.trans ((congrArg recover strict.1).trans (all 0))
  exact strict.2 sameValue

theorem nilpotent_source_annihilator_original_row_next :
    ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation word ∈
        valuePairingAnnihilator nilAction (emitted toggle true) ∧
    ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation word ≠ 0 ∧
    (valuePairingRoot nilAction).source.projectionLaw.outcomeAt
        (.component PUnit.unit) ((valuePairingRoot nilAction).emitted true) =
      .inl ⟨PUnit.unit, valuePairing nilAction (emitted toggle true)⟩ ∧
    HEq (((valuePairingRoot nilAction).toLedgerRoot.generatedLedgerAt true
        ).entryDisposition (entry toggle true))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred true rfl rfl (Nat.le_refl _) :
          LedgerEntryEvolutionAt (network toggle)
            (entry toggle true) (entry toggle true))) ∧
    ((valuePairingRoot nilAction).toRoot.evolutionAt true).nextCurrent? =
      some true := by
  have paid := nilpotent_pairing_loss_original_row_next
  have invisible :
      ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation word ∈
        valuePairingAnnihilator nilAction (emitted toggle true) := by
    change ∀ right : nilAction.Generator →₀ ℤ,
      ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation word *
        ((faithfulLaw nilAction).faithfulAt (emitted toggle true)).freeEvaluation right = 0
    exact paid.2.1
  exact ⟨invisible, paid.1, paid.2.2.1, paid.2.2.2.1, paid.2.2.2.2⟩
end
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.Regression
