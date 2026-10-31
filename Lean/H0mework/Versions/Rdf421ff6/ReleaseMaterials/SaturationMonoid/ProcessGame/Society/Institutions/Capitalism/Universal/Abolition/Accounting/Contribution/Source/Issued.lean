import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source.Inventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Port] in
theorem an_emitted_claim_keeps_its_exact_source_origin
    (origin : Financial.InstructionOrigin input) (claim : Financial.IssuedClaim input)
    (emitted : Financial.issuedClaim? input origin = some claim) : claim.origin = origin := by
  unfold Financial.issuedClaim? at emitted
  cases found : Financial.readIssue input origin with
  | issued actual source =>
      rw [found] at emitted
      cases Option.some.inj emitted
      exact source
  | nonfinancial | rejected | missingBirth => simp only [found] at emitted; cases emitted

omit [DecidableEq Port] in
theorem issued_origins_are_a_sublist_of_the_original_requests
    (origins : List (Financial.InstructionOrigin input)) :
    ((Financial.issuedClaims input origins).map Financial.IssuedClaim.origin).Sublist origins := by
  induction origins with
  | nil => exact List.Sublist.refl _
  | cons original remaining inherited =>
      cases emitted : Financial.issuedClaim? input original with
      | none =>
          simpa only [Financial.issuedClaims,List.filterMap_cons,emitted] using inherited.cons original
      | some claim =>
          have source := an_emitted_claim_keeps_its_exact_source_origin input original claim emitted
          simpa only [Financial.issuedClaims,List.filterMap_cons,emitted,List.map_cons,source] using inherited.cons_cons original

omit [DecidableEq Port] in
theorem each_actual_visit_issues_each_origin_at_most_once (visit : Nat) :
    ((Financial.issuedClaims input (Financial.inventoryAt input (ProgrammeHistory.visitAt input visit))).map
      Financial.IssuedClaim.origin).Nodup := by
  cases visit with
  | zero =>
      have noAdministrative : ∀ original ∈ Financial.administrativeInventoryAt input (ProgrammeHistory.visitAt input 0),
          Financial.issuedClaim? input original = none := by
        intro original member
        obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
        rfl
      unfold Financial.issuedClaims
      cases generated : input.emission? with
      | none =>
          simp only [Financial.inventoryAt,generated]
          rw [List.filterMap_eq_nil_iff.mpr noAdministrative]
          exact List.nodup_nil
      | some emit =>
          have emptyTrace : Financial.traceInventoryAt input (ProgrammeHistory.visitAt input 0) = [] := by
            simp only [Financial.traceInventoryAt,Source.ProgrammeFace.Registered.traceItems,
              ProgrammeHistory.visitAt,ProgrammeSource.rawEvent]
            rfl
          simp only [Financial.inventoryAt,generated,emptyTrace,List.append_nil]
          rw [List.filterMap_eq_nil_iff.mpr noAdministrative]
          exact List.nodup_nil
  | succ visit =>
      have runningEq : ∃ raw past,(ProgrammeHistory.visitAt input (visit + 1)).current =
          .running raw past := by
        change ∃ raw past,ProgrammeSource.next input (ProgrammeHistory.visitAt input visit).current = .running raw past
        cases (ProgrammeHistory.visitAt input visit).current <;> exact ⟨_,_,rfl⟩
      obtain ⟨raw,past,runningEq⟩ := runningEq
      have running := an_actual_running_inventory_never_repeats_an_origin input
        (ProgrammeHistory.visitAt input (visit + 1)) raw past runningEq
      exact running.sublist (issued_origins_are_a_sublist_of_the_original_requests input _)

omit [DecidableEq Port] in
theorem an_issued_inventory_origin_has_its_original_visit
    (visit : Nat) (claim : Financial.IssuedClaim input)
    (member : claim ∈ Financial.issuedClaims input (Financial.inventoryAt input (ProgrammeHistory.visitAt input visit))) :
    claim.origin.visit = ProgrammeHistory.visitAt input visit := by
  have sourceMember := (issued_origins_are_a_sublist_of_the_original_requests input
    (Financial.inventoryAt input (ProgrammeHistory.visitAt input visit))).subset
      (List.mem_map.mpr ⟨claim,member,rfl⟩)
  exact inventory_member_has_its_original_visit input _ claim.origin sourceMember

omit [DecidableEq Port] in
theorem an_earlier_claim_keeps_its_strictly_earlier_visit
    (cut : Nat) (claim : Financial.IssuedClaim input) (member : claim ∈ Financial.issuedBefore input cut) :
    ∃ visit < cut,claim.origin.visit = ProgrammeHistory.visitAt input visit := by
  induction cut with
  | zero => exact (List.not_mem_nil member).elim
  | succ cut inherited =>
      rcases List.mem_append.mp member with old | fresh
      · obtain ⟨visit,before,source⟩ := inherited old
        exact ⟨visit,by omega,source⟩
      · exact ⟨cut,Nat.lt_succ_self cut,an_issued_inventory_origin_has_its_original_visit input cut claim fresh⟩

omit [DecidableEq Port] in
theorem the_actual_source_never_reissues_an_original_contribution (cut : Nat) :
    ((Financial.issuedBefore input cut).map Financial.IssuedClaim.origin).Nodup := by
  induction cut with
  | zero => exact List.nodup_nil
  | succ cut inherited =>
      rw [Financial.issuedBefore,List.map_append]
      apply List.nodup_append.mpr
      refine ⟨inherited,each_actual_visit_issues_each_origin_at_most_once input cut,?_⟩
      intro old oldMember fresh freshMember same
      obtain ⟨oldClaim,oldIssued,rfl⟩ := List.mem_map.mp oldMember
      obtain ⟨newClaim,newIssued,rfl⟩ := List.mem_map.mp freshMember
      obtain ⟨visit,before,oldVisit⟩ := an_earlier_claim_keeps_its_strictly_earlier_visit input cut oldClaim oldIssued
      have newVisit := an_issued_inventory_origin_has_its_original_visit input cut newClaim newIssued
      have currentSame := congrArg (fun origin : Financial.InstructionOrigin input => origin.visit.current) same
      rw [oldVisit,newVisit] at currentSame
      have impossible := ProgrammeHistory.visit_current_injective input currentSame
      omega

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source
