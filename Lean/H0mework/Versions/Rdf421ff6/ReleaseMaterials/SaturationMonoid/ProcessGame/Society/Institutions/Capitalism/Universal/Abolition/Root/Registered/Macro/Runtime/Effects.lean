import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Successor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Frame

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount frame.start frame.proposal frame.sourcePosition frame.package.frame frame.visit.current)

theorem born_cursor :
    (frame.born registered).cursor =
      Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
        frame.start frame.proposal frame.sourcePosition frame.cursor :=
  (frame.package.born registered).frame.next_exact (Admission.initial frame.package.frame registered)

theorem born_account_is_the_actual_admission : (frame.born registered).cursor.account = registered.admitted :=
  Admission.first_source_step_registers_the_same_original_debt frame.package.frame registered

theorem born_slot_is_the_same_original_live_claim :
    (frame.born registered).cursor.account.current.slots[frame.cursor.account.current.slots.length]? =
      some (.live (Epoch.Finance.admission input depth count (.inr registered.issued.claim)).toObligation) := by
  rw [frame.born_account_is_the_actual_admission registered]
  exact registered.issued.original_principal_remains_live input depth count

theorem every_old_claim_remains_in_its_original_order :
    frame.cursor.account.current.slots.map (Epoch.Finance.slotClaim input depth count) <+:
      (frame.born registered).cursor.account.current.slots.map (Epoch.Finance.slotClaim input depth count) := by
  rw [frame.born_account_is_the_actual_admission registered]
  change _ <+: (frame.cursor.account.current.slots ++ _).map _
  rw [List.map_append]
  exact List.prefix_append _ _

theorem registration_has_no_second_physical_execution :
    Accounting.physical (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount frame.start frame.proposal frame.sourcePosition
      (frame.born registered).cursor =
    Accounting.physical (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount frame.start frame.proposal frame.sourcePosition frame.cursor := by
  rw [frame.born_cursor registered]
  exact Accounting.bookkeeping_does_not_replay_the_physical_body (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
    frame.start frame.proposal frame.sourcePosition frame.cursor
    (frame.package.data.bodyPaid frame.visit.current frame.ready)

theorem registration_does_not_discharge_principal :
    ¬ Nonempty (registered.law.SettlementAt registered.firstStep.target) :=
  registered.issued.registration_does_not_claim_financial_settlement input depth count

theorem source_selected_registration_is_actual_next
    (selected : headRegistration? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      frame.start frame.proposal frame.sourcePosition frame.package.frame frame.visit.current = some registered) :
    frame.next = frame.born registered := by
  have work : Inquiry.HasWork frame.package.source frame.visit.current :=
    Or.inr (congrArg Option.isSome registered.atHead)
  calc
    frame.next = frame.nextAt (.internal work) :=
      (congrArg frame.nextAt (frame.query_unique (.internal work))).symm
    _ = frame.born registered := by
      change frame.internalNext = _
      unfold internalNext
      rw [selected]

theorem actual_registration_keeps_the_original_admission
    (selected : headRegistration? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      frame.start frame.proposal frame.sourcePosition frame.package.frame frame.visit.current = some registered) :
    frame.next.account = registered.admitted :=
  (congrArg Frame.account (frame.source_selected_registration_is_actual_next registered selected)).trans
    (frame.born_account_is_the_actual_admission registered)

theorem source_selected_raw_is_actual_next
    (germ : Raw.GermAt frame.package.source frame.package.sourceData frame.package.reader frame.visit.current) :
    frame.next = frame.reenter germ :=
  (congrArg frame.nextAt (frame.query_unique (.raw germ))).symm

theorem actual_raw_reentry_retains_the_entire_existing_account
    (germ : Raw.GermAt frame.package.source frame.package.sourceData frame.package.reader frame.visit.current) :
    frame.next.account = frame.account :=
  (congrArg Frame.account (frame.source_selected_raw_is_actual_next germ)).trans
    (frame.reentry_preserves_the_literal_existing_account germ)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Frame

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Frame.born_slot_is_the_same_original_live_claim
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Frame.every_old_claim_remains_in_its_original_order
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Frame.registration_has_no_second_physical_execution
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Frame.source_selected_registration_is_actual_next
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Frame.actual_registration_keeps_the_original_admission
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Frame.actual_raw_reentry_retains_the_entire_existing_account
