import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Ledger
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History.Native
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.Entry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open Capitalism.Universal.Root.Financial.Installation (KeepsKeys)

abbrev Whole (N : WorldRelationNetwork) (before after : N.Support) :=
  { ledger : LedgerWriteEvolutionAt N ⟨before⟩ ⟨after⟩ // KeepsKeys ledger }

def Whole.rebase {N : WorldRelationNetwork} {s t s' t' : N.Support}
    (before : s = s') (after : t = t') (write : Whole N s t) : Whole N s' t' := by
  cases before
  cases after
  exact write

theorem Whole.rebase_destination {N : WorldRelationNetwork} {s t s' t' : N.Support}
    (before : s = s') (after : t = t') (write : Whole N s t) :
    HEq (write.rebase before after).val.destination write.val.destination := by
  cases before
  cases after
  rfl

theorem destination_congr {N : WorldRelationNetwork} {s t s' t' : N.Support}
    (before : s = s') (after : t = t')
    (left : LedgerWriteEvolutionAt N ⟨s⟩ ⟨t⟩) (right : LedgerWriteEvolutionAt N ⟨s'⟩ ⟨t'⟩)
    (same : HEq left.destination right.destination)
    (entry : OpenResponsibilityAt N s) (other : OpenResponsibilityAt N s') (origin : HEq entry other) :
    HEq (left.destination entry).1 (right.destination other).1 := by
  cases before
  cases after
  rw [eq_of_heq same, eq_of_heq origin]

namespace Whole

def jointStep {N : WorldRelationNetwork} {law : DebtActivationLaw}
    {s t : N.Support} {before after : law.DebtState} (original : Whole N s t)
    (owner : OpenResponsibilityAt N s) (step : law.StepAt before after) :
    Whole (ExtendedNetwork N law) (s, some before) (t, some after) := by
  refine ⟨jointStepLedgerEvolution original.val owner step, ?_, ?_⟩
  · rintro ⟨key, opened⟩
    cases key with
    | inl key => exact congrArg Sum.inl (original.property.1 ⟨key, opened⟩)
    | inr id => rcases opened with ⟨⟨same⟩⟩; subst id; rfl
  · rintro ⟨key, opened⟩
    cases key with
    | inl key => exact congrArg Sum.inl (original.property.2 ⟨key, opened⟩)
    | inr id => rcases opened with ⟨⟨same⟩⟩; subst id; rfl

end Whole

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport
