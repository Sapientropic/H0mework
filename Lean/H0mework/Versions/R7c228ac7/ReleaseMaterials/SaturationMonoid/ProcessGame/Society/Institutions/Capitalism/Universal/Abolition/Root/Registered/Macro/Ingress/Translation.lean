import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Shape

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private def CompleteRows {A B : WorldRelationNetwork} (map : TypedSemanticWorldNetworkTranslationAt A B) : Prop :=
  (∀ support row, (map.oldOpenLedger support).forward ((map.oldOpenLedger support).backward row) = row) ∧
  (∀ support row, map.responsibility.forward row.1 = ((map.oldOpenLedger support).forward row).1)

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (epochDepth epochCount : Nat)

private theorem extension_complete {A B : WorldRelationNetwork}
    (map : TypedSemanticWorldNetworkTranslationAt A B) (complete : CompleteRows map)
    (before : (Financial.process input).GeneratedState) (claim : Financial.IssuedClaim input) :
    CompleteRows (Epoch.Finance.World.translation input epochDepth epochCount before claim map) := by
  constructor
  · rintro ⟨support, state⟩ ⟨responsibility, opened⟩
    cases responsibility with
    | inl original =>
        change oldEntry ((map.oldOpenLedger support).forward
          ((map.oldOpenLedger support).backward ⟨original, opened⟩)) = _
        rw [complete.1]
        rfl
    | inr debt => cases state with
        | none => exact opened.elim
        | some state => rfl
  · rintro ⟨support, state⟩ ⟨responsibility, opened⟩
    cases responsibility with
    | inl original => exact congrArg Sum.inl (complete.2 support ⟨original, opened⟩)
    | inr debt => cases state with
        | none => exact opened.elim
        | some state => rfl

private theorem fold_complete {A B : WorldRelationNetwork}
    (map : TypedSemanticWorldNetworkTranslationAt A B) (complete : CompleteRows map)
    {current : ResponsibilityState (Financial.vocabulary input)}
    (run : (Financial.process input).Run (.empty (Financial.vocabulary input)) current) :
    CompleteRows (Epoch.Finance.World.foldTranslation input epochDepth epochCount map run) := by
  induction run with
  | nil => exact complete
  | step prior edge inherited =>
      cases edge with
      | admit claim => exact extension_complete input epochDepth epochCount _ inherited _ claim
      | cross _ _ _ _ => exact inherited
      | reopen _ _ _ impossible => exact impossible.elim

private theorem shape_complete {native : Financial.Installation.NativeFrame input}
    (shape : Epoch.Finance.Installation.Shape input native) :
    CompleteRows (shape.translation input epochDepth epochCount) := by
  induction shape with
  | base start positive =>
      exact fold_complete input epochDepth epochCount _ ⟨fun _ _ => rfl, fun _ _ => rfl⟩ start.account.generated
  | born prior registered inherited => exact extension_complete input epochDepth epochCount _ inherited _ registered.claim

variable (sourceDepth sourceCount : Nat)

abbrev sourceTranslation := Epoch.Finance.Installation.Generated.translation input epochDepth epochCount sourceDepth sourceCount

theorem translated_ledger_has_no_fresh_rows
    (support : (Financial.Installation.Runtime.frames input sourceDepth sourceCount).native.N.Support)
    (row : OpenResponsibilityAt ((Epoch.Finance.Installation.Generated.shape input sourceDepth sourceCount).world input epochDepth epochCount)
      ((sourceTranslation input epochDepth epochCount sourceDepth sourceCount).support.forward support)) :
    ((sourceTranslation input epochDepth epochCount sourceDepth sourceCount).oldOpenLedger support).forward
      (((sourceTranslation input epochDepth epochCount sourceDepth sourceCount).oldOpenLedger support).backward row) = row :=
  (shape_complete input epochDepth epochCount (Epoch.Finance.Installation.Generated.shape input sourceDepth sourceCount)).1 support row

theorem translated_responsibility_is_the_original_row
    (support : (Financial.Installation.Runtime.frames input sourceDepth sourceCount).native.N.Support)
    (row : OpenResponsibilityAt (Financial.Installation.Runtime.frames input sourceDepth sourceCount).native.N support) :
    (sourceTranslation input epochDepth epochCount sourceDepth sourceCount).responsibility.forward row.1 =
      (((sourceTranslation input epochDepth epochCount sourceDepth sourceCount).oldOpenLedger support).forward row).1 :=
  (shape_complete input epochDepth epochCount (Epoch.Finance.Installation.Generated.shape input sourceDepth sourceCount)).2 support row

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.translated_ledger_has_no_fresh_rows
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.translated_responsibility_is_the_original_row
