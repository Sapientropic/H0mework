import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Step

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

private def OldAction (action : Action) : Prop := match action.operation with
  | .transfer sender recipient goods => sender ≤ 3 ∧ recipient ≤ 3 ∧ ∀ entry ∈ goods,entry.1 = .labor ∨ entry.1 = .feed
  | .use actor goods _ => actor ≤ 3 ∧ ∀ entry ∈ goods,entry.1 = .labor ∨ entry.1 = .feed
  | .revise actor _ => actor ≤ 3
  | _ => False

private theorem old_flow_zero (flow : Flow Party Good) (good : Good) (untouched : ∀ entry ∈ flow,entry.1.2 ≠ good)
    (actor : Party) : flowAt flow actor good = 0 := by
  unfold flowAt amount
  apply List.sum_eq_zero
  intro value member
  obtain ⟨entry,inside,rfl⟩ := List.mem_map.mp member
  have absent : entry.1 ≠ (actor,good) := by
    intro eq
    exact untouched entry inside (congrArg Prod.snd eq)
  simp only [if_neg absent]

private theorem old_step (before : AuditCurrent) (action : Action) (old : OldAction action)
    (actor : Party) (good : Good) (labor : good ≠ .labor) (feed : good ≠ .feed) :
    (auditLaw.step before action).stock actor good = before.stock actor good := by
  have debit : ∀ entry ∈ auditLaw.debit before action,entry.1.2 ≠ good := by
    cases operation : action.operation <;> simp only [OldAction,operation] at old
    case transfer sender recipient goods =>
      have old := old.2.2
      intro entry inside
      simp only [RawLaw.debit,operation,locate,List.mem_map] at inside
      obtain ⟨item,member,rfl⟩ := inside
      rcases old item member with eq | eq
      · exact eq ▸ Ne.symm labor
      · exact eq ▸ Ne.symm feed
    case use sender goods purpose =>
      have old := old.2
      intro entry inside
      simp only [RawLaw.debit,operation,locate,List.mem_map] at inside
      obtain ⟨item,member,rfl⟩ := inside
      rcases old item member with eq | eq
      · exact eq ▸ Ne.symm labor
      · exact eq ▸ Ne.symm feed
    case revise sender target =>
      simpa [auditLaw,RawLaw.debit,operation,Mandate.law,Scoped.scope,locate] using Ne.symm labor
  have credit : ∀ entry ∈ auditLaw.credit before action,entry.1.2 ≠ good := by
    cases operation : action.operation <;> simp only [OldAction,operation] at old
    case transfer sender recipient goods =>
      have old := old.2.2
      intro entry inside
      simp only [RawLaw.credit,operation,locate,List.mem_map] at inside
      obtain ⟨item,member,rfl⟩ := inside
      rcases old item member with eq | eq
      · exact eq ▸ Ne.symm labor
      · exact eq ▸ Ne.symm feed
    case use sender goods purpose | revise sender target => simp [RawLaw.credit,operation]
  unfold RawLaw.step
  split
  · simp only [RawLaw.paidStep,old_flow_zero _ good debit actor,old_flow_zero _ good credit actor,sub_zero,add_zero]
  · rfl

set_option linter.unusedSimpArgs false in
private theorem emitted_old (queries : Nat → Query) (larger : Bool) (before : AuditCurrent) :
    ∀ action ∈ Scoped.emit queries larger before,OldAction action := by
  unfold Scoped.emit Scoped.preparation Scoped.refill Scoped.handoff Scoped.authorization Scoped.readWord
  dsimp only
  split
  all_goals (repeat' split)
  all_goals simp [OldAction,Scoped.transferLabor,Scoped.command,Mandate.request,
    Scoped.privateUse,Scoped.accessRequest,Scoped.deliveryFee]

private theorem old_execute (before : AuditCurrent) (word : List Action) (old : ∀ action ∈ word,OldAction action)
    (index actor : Nat) (good : Good) (labor : good ≠ .labor) (feed : good ≠ .feed) :
    (auditLaw.execute before index word).final.stock actor good = before.stock actor good := by
  induction word generalizing before index with
  | nil => rfl
  | cons action rest ih =>
    change (auditLaw.execute (auditLaw.step before action) (index+1) rest).final.stock actor good = _
    rw [ih _ (fun action inside => old _ (List.mem_cons_of_mem _ inside)) (index+1),old_step _ _ (old _ (by simp)) _ _ labor feed]

theorem original_untouched (queries : Nat → Query) (larger : Bool) (n actor : Nat) (good : Good)
    (labor : good ≠ .labor) (feed : good ≠ .feed) :
    (Scoped.current queries larger n).stock actor good = Scoped.initial.stock actor good := by
  induction n with
  | zero => rw [Scoped.current_zero]
  | succ n ih =>
    rw [Scoped.current_succ]
    trans (Scoped.current queries larger n).stock actor good
    · apply old_execute
      split
      · simp
      · exact emitted_old _ _ _
      exact labor
      exact feed
    · exact ih

private theorem foreign_step (before : AuditCurrent) (action : Action) (old : OldAction action)
    (actor : Party) (foreign : 3 < actor) (good : Good) :
    (auditLaw.step before action).stock actor good = before.stock actor good := by
  have debit : ∀ entry ∈ auditLaw.debit before action,entry.1.1 ≤ 3 := by
    cases operation : action.operation <;> simp only [OldAction,operation] at old
    case transfer sender recipient goods | use sender goods purpose =>
      intro entry inside
      simp only [RawLaw.debit,operation,locate,List.mem_map] at inside
      obtain ⟨item,_,rfl⟩ := inside
      exact old.1
    case revise sender target =>
      simp only [RawLaw.debit,operation,auditLaw,Mandate.law,Scoped.scope,locate,
        List.map_cons,List.map_nil,List.mem_singleton]
      intro entry same
      subst entry
      exact old
  have credit : ∀ entry ∈ auditLaw.credit before action,entry.1.1 ≤ 3 := by
    cases operation : action.operation <;> simp only [OldAction,operation] at old
    case transfer sender recipient goods =>
      intro entry inside
      simp only [RawLaw.credit,operation,locate,List.mem_map] at inside
      obtain ⟨item,_,rfl⟩ := inside
      exact old.2.1
    case use sender goods purpose | revise sender target => simp [RawLaw.credit,operation]
  have zero : ∀ flow : Flow Party Good,(∀ entry ∈ flow,entry.1.1 ≤ 3) → flowAt flow actor good = 0 := by
    intro flow domestic
    unfold flowAt amount
    apply List.sum_eq_zero
    intro value member
    obtain ⟨entry,inside,rfl⟩ := List.mem_map.mp member
    have absent : entry.1 ≠ (actor,good) := by
      intro eq
      have small := domestic entry inside
      rw [congrArg Prod.fst eq] at small
      exact Nat.not_le_of_lt foreign small
    simp only [if_neg absent]
  unfold RawLaw.step
  split
  · simp only [RawLaw.paidStep,zero _ debit,zero _ credit,sub_zero,add_zero]
  · rfl

private theorem foreign_execute (before : AuditCurrent) (word : List Action) (old : ∀ action ∈ word,OldAction action)
    (index actor : Nat) (foreign : 3 < actor) (good : Good) :
    (auditLaw.execute before index word).final.stock actor good = before.stock actor good := by
  induction word generalizing before index with
  | nil => rfl
  | cons action rest ih =>
    change (auditLaw.execute (auditLaw.step before action) (index+1) rest).final.stock actor good = _
    rw [ih _ (fun action inside => old _ (List.mem_cons_of_mem _ inside)) (index+1),foreign_step _ _ (old _ (by simp)) _ foreign good]

private theorem original_foreign (queries : Nat → Query) (larger : Bool) (n actor : Nat)
    (foreign : 3 < actor) (good : Good) :
    (Scoped.current queries larger n).stock actor good = Scoped.initial.stock actor good := by
  induction n with
  | zero => rw [Scoped.current_zero]
  | succ n ih =>
    rw [Scoped.current_succ]
    trans (Scoped.current queries larger n).stock actor good
    · apply foreign_execute
      split
      · simp
      · exact emitted_old _ _ _
      exact foreign
    · exact ih

/-- The two lawful histories themselves generate the relation, for arbitrary original queries and time. -/
theorem original_twin (queries : Nat → Query) (n : Nat) :
    Twin (Scoped.current queries false n) (Scoped.current queries true n) := by
  have view := every_current_has_the_same_permitted_view queries n
  refine ⟨congrArg PublicView.permission view,congrArg PublicView.clock view,?_,?_,?_⟩
  · rw [Scoped.current_round,Scoped.current_round]
  · rw [every_current_keeps_the_original_claim_matrix,every_current_keeps_the_original_claim_matrix]
  · intro actor good feed
    by_cases labor : good = .labor
    · subst good
      by_cases a0 : actor = 0
      · subst actor; exact congrArg PublicView.labor0 view
      by_cases a1 : actor = 1
      · subst actor; exact congrArg PublicView.labor1 view
      by_cases a2 : actor = 2
      · subst actor; exact congrArg PublicView.labor2 view
      by_cases a3 : actor = 3
      · subst actor; exact congrArg PublicView.labor3 view
      have foreign : 3 < actor := by
        change (3 : Nat) < actor
        change actor ≠ (0 : Nat) at a0
        change actor ≠ (1 : Nat) at a1
        change actor ≠ (2 : Nat) at a2
        change actor ≠ (3 : Nat) at a3
        by_contra late
        have bound : actor ≤ 3 := Nat.le_of_not_gt late
        interval_cases actor <;> contradiction
      rw [original_foreign _ _ _ _ foreign,original_foreign _ _ _ _ foreign]
    · rw [original_untouched _ _ _ _ _ labor feed,original_untouched _ _ _ _ _ labor feed]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
