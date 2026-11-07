import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Native
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Keys
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.NativeEvolution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Financial.Installation (KeepsKeys)

noncomputable section

private theorem cast_target_keys {N : WorldRelationNetwork}
    (source left right : N.Support) (same : left = right)
    (evolution : LedgerWriteEvolutionAt N ⟨source⟩ ⟨left⟩) (keys : KeepsKeys evolution) :
    KeepsKeys (Eq.mp (congrArg (fun support => LedgerWriteEvolutionAt N ⟨source⟩ ⟨support⟩) same) evolution) := by
  cases same
  exact keys

private theorem joint_keys {N : WorldRelationNetwork} {law : DebtActivationLaw}
    {before after : N.Support} {source target : law.DebtState}
    (base : LedgerWriteEvolutionAt N ⟨before⟩ ⟨after⟩)
    (owner : OpenResponsibilityAt N before) (step : law.StepAt source target)
    (keys : KeepsKeys base) : KeepsKeys (jointStepLedgerEvolution base owner step) := by
  constructor
  · rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl old => exact congrArg Sum.inl (keys.1 ⟨old, opened⟩)
    | inr debt => rcases opened with ⟨⟨same⟩⟩; subst debt; rfl
  · rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl old => exact congrArg Sum.inl (keys.2 ⟨old, opened⟩)
    | inr debt => rcases opened with ⟨⟨same⟩⟩; subst debt; rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (prior : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (current : Current input depth count anchor)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start current)

def baseEvolution : LedgerWriteEvolutionAt world ⟨oldSupport prior current⟩
    ⟨(targetSupport prior current registered).1⟩ :=
  Eq.mp (congrArg (fun support => LedgerWriteEvolutionAt world ⟨oldSupport prior current⟩ ⟨support⟩)
    (the_complete_old_support_is_the_same_source_target prior current registered).symm)
    (Accounting.nativeEvolution input depth count prefixLimit renewalLimit oldPast start prior current)

theorem baseEvolution_keys : KeepsKeys (baseEvolution prior current registered) :=
  cast_target_keys _ _ _ (the_complete_old_support_is_the_same_source_target prior current registered).symm
    (Accounting.nativeEvolution input depth count prefixLimit renewalLimit oldPast start prior current)
    (Accounting.nativeEvolutionWithKeys input depth count prefixLimit renewalLimit oldPast start prior current).property

/-- One source event updates all old rows and spends the pending admission
capacity; the native account contains exactly the original single admit. -/
def firstWrite : LedgerWriteEvolutionAt (N prior current registered)
    ⟨initialSupport prior current registered⟩ ⟨targetSupport prior current registered⟩ :=
  jointStepLedgerEvolution (baseEvolution prior current registered)
    (Accounting.owner input depth count prior current) (firstStep current registered).step

theorem firstWrite_keys : KeepsKeys (firstWrite prior current registered) :=
  joint_keys _ _ _ (baseEvolution_keys prior current registered)

theorem the_first_write_keeps_every_original_key_claim_and_budget
    (entry : OpenResponsibilityAt world (oldSupport prior current)) :
    ((firstWrite prior current registered).destination (oldEntry (law := law current registered) (state? := some .pending) entry)).1.1 = .inl entry.1 ∧
      ((firstWrite prior current registered).destination (oldEntry (law := law current registered) (state? := some .pending) entry)).1.claim = .inl entry.claim ∧
      ((firstWrite prior current registered).destination (oldEntry (law := law current registered) (state? := some .pending) entry)).1.progressBudget ≤ entry.progressBudget := by
  refine ⟨(firstWrite_keys prior current registered).1 _, ?_, ?_⟩
  · exact ((firstWrite prior current registered).destination _).2.toDebtLineage.claim_eq.symm
  · exact ((firstWrite prior current registered).destination _).2.progressBudget_not_refilled

theorem the_born_row_is_the_source_generated_strict_first_write :
    ((firstWrite prior current registered).destination
      (debtEntry (N := world) (law := law current registered) (oldSupport prior current) .pending)).1 =
        debtEntry (N := world) (law := law current registered) (targetSupport prior current registered).1
          (firstStep current registered).target ∧
      ((firstWrite prior current registered).destination
        (debtEntry (N := world) (law := law current registered) (oldSupport prior current) .pending)).1.progressBudget <
        (debtEntry (N := world) (law := law current registered) (oldSupport prior current) .pending).progressBudget :=
  ⟨rfl, jointStepLedgerEvolution_debt_strict _ _ _⟩

#print axioms firstWrite
#print axioms firstWrite_keys
#print axioms the_first_write_keeps_every_original_key_claim_and_budget
#print axioms the_born_row_is_the_source_generated_strict_first_write

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born
