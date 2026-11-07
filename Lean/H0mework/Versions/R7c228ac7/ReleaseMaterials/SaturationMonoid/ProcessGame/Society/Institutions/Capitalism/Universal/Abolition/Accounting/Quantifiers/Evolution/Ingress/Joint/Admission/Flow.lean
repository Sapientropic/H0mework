import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission.Keys

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (grossClaim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def evolution : (phase : Bool) → LedgerWriteEvolutionAt (N seed grossClaim)
    ⟨support seed grossClaim phase⟩ ⟨support seed grossClaim true⟩
  | false => firstWrite seed grossClaim
  | true => LedgerWriteEvolutionAt.identity _

theorem fibres : ∀ current key, Subsingleton ((N seed grossClaim).OpenAt current key) :=
  Abolition.Root.Epoch.Finance.Future.Structure.extended_subsingleton (law seed grossClaim) (Rebase.fibres seed grossClaim)

theorem entries_finite (phase : Bool) : Finite (OpenResponsibilityAt (N seed grossClaim) (support seed grossClaim phase)) := by
  cases phase with
  | false =>
      exact Abolition.Root.Epoch.Finance.Future.Finiteness.active_finite _
        (Rebase.stage_entries_finite seed grossClaim Rebase.Stage.entered)
  | true =>
      have finite : Finite (OpenResponsibilityAt (oldN seed grossClaim)
          (sourceSuccessor seed grossClaim).targetOccurrence.1) :=
        (the_old_side_of_the_declaration_already_uses_the_same_shared_pointer seed grossClaim).symm ▸
          Rebase.stage_entries_finite seed grossClaim Rebase.Stage.declared
      exact Abolition.Root.Epoch.Finance.Future.Finiteness.active_finite _ finite

def flow : Abolition.Accounting.Root.Compiler.Flow (N seed grossClaim) where
  Current := Bool
  initial := false
  support := support seed grossClaim
  next := fun _ => true
  writes := fun phase => !phase
  evolution := evolution seed grossClaim
  finite := entries_finite seed grossClaim
  injective := by
    intro phase
    cases phase with
    | false =>
        exact ⟨Financial.Installation.keys_imply_origin_injective _ (gross_admission_keeps_every_original_key seed grossClaim)
          (fibres seed grossClaim),
          Financial.Installation.keys_imply_destination_injective _ (gross_admission_keeps_every_original_key seed grossClaim)
          (fibres seed grossClaim)⟩
    | true => exact ⟨Function.injective_id,Function.injective_id⟩
  open_fibres := fibres seed grossClaim

abbrev V := Abolition.Accounting.Root.Compiler.V (flow seed grossClaim)
abbrev baseRoot := Abolition.Accounting.Root.Compiler.livingRoot (flow seed grossClaim)

theorem the_first_write_updates_both_old_and_new_rows_to_the_same_shared_value :
    (support seed grossClaim true).1.2 = some (.current (declaredShared seed grossClaim)) ∧
      (support seed grossClaim true).2 = some (declaredShared seed grossClaim) :=
  ⟨congrArg Prod.snd (the_old_side_of_the_declaration_already_uses_the_same_shared_pointer seed grossClaim),rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission
