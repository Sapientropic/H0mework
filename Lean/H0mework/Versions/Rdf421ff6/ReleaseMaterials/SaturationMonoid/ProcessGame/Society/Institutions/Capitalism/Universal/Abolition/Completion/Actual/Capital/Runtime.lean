import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital.Permission
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Persistence

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Registered Source.Program Source.ProgrammeControl

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth sourceStart : Nat)
  (datum : Macro.Ingress.Datum input depth sourceStart) (prefixLimit renewalLimit : Nat)
  (reader : Macro.Raw.Reader input depth (Macro.Ingress.cut input depth sourceStart))
  (review : Option (ReviewPhase.ContextAt input) := none)
  {origin : Functions.Revision.Context (input := input) (review := review)
    depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit
    depth (Macro.Ingress.cut input depth sourceStart)}
  {admission : Functions.Revision.InitialAdmissionAt origin}
  (frame : Macro.Public.Runtime.Frame origin admission) (tick : Nat)
  (selected : Macro.Runtime.actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick =
    .enacted origin admission frame)

local notation "actual" => Macro.Runtime.actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader

include selected

theorem the_same_actual_public_tail_cannot_regenerate_a_capital_kernel
    (steps : Nat) (word : RawEvent Party Good Port Technology Instrument) :
    ¬ Nonempty (Kernel.CapitalRelationKernel (actual (tick + steps)).interpreter
      (actual (tick + steps)).actualState.raw word) := by
  rw [Macro.Runtime.the_actual_public_tail_keeps_its_effective_interpreter input depth sourceStart datum
    prefixLimit renewalLimit reader review frame tick selected steps]
  exact Functions.open_permissions_have_no_capital_kernel _ (fun _ _ _ => rfl) _ _

theorem no_title_or_actual_surplus_can_reinstate_the_actual_private_relation
    (steps : Nat) (attempts : RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (item : OriginalItem (actual (tick + steps)).interpreter (actual (tick + steps)).actualState.raw word) :
    Kernel.AssetAuthority.generatedFamily _ _ _ attempts item = [] ∧ Kernel.ActualSurplus.familyAt _ _ _ item = [] := by
  have opened : ∀ technology port person,
      (actual (tick + steps)).interpreter.allowed technology port person = true := by
    rw [Macro.Runtime.the_actual_public_tail_keeps_its_effective_interpreter input depth sourceStart datum
      prefixLimit renewalLimit reader review frame tick selected steps]
    exact fun _ _ _ => rfl
  exact ⟨Functions.open_permissions_title_family_empty _ opened _ _ attempts item,
    Functions.open_permissions_actual_surplus_family_empty _ opened _ _ item⟩

theorem ending_new_capital_relations_keeps_every_original_native_claim_and_history
    (steps : Nat) (word : RawEvent Party Good Port Technology Instrument) :
    ¬ Nonempty (Kernel.CapitalRelationKernel (actual (tick + steps)).interpreter
      (actual (tick + steps)).actualState.raw word) ∧
    frame.account.current.slots.map (Epoch.Finance.slotClaim input depth (Macro.Ingress.cut input depth sourceStart)) <+:
      (actual (tick + steps)).nativeAccount.current.slots.map
        (Epoch.Finance.slotClaim input depth (Macro.Ingress.cut input depth sourceStart)) ∧
    frame.account.current.history <+: (actual (tick + steps)).nativeAccount.current.history := by
  let native := Macro.Runtime.the_actual_public_tail_keeps_the_original_native_run input depth sourceStart datum
    prefixLimit renewalLimit reader review frame tick selected steps
  refine ⟨the_same_actual_public_tail_cannot_regenerate_a_capital_kernel input depth sourceStart datum
    prefixLimit renewalLimit reader review frame tick selected steps word,
    Epoch.Finance.run_retains_all_claims input depth (Macro.Ingress.cut input depth sourceStart) native, ?_⟩
  rw [native.history_eq]
  exact List.prefix_append _ _

#print axioms the_same_actual_public_tail_cannot_regenerate_a_capital_kernel
#print axioms no_title_or_actual_surplus_can_reinstate_the_actual_private_relation
#print axioms ending_new_capital_relations_keeps_every_original_native_claim_and_history

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital
