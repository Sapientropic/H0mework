import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.AuditLaw

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

theorem Twin.symm {left right : AuditCurrent} (same : Twin left right) : Twin right left :=
  ⟨same.technology.symm,same.clock.symm,same.round.symm,same.claims.symm,fun a g h => (same.stock a g h).symm⟩
theorem Twin.trans {left middle right : AuditCurrent} (first : Twin left middle) (second : Twin middle right) : Twin left right :=
  ⟨first.technology.trans second.technology,first.clock.trans second.clock,first.round.trans second.round,
    first.claims.trans second.claims,fun a g h => (first.stock a g h).trans (second.stock a g h)⟩

namespace GovernancePrivacy
open AuditLaw

theorem safe_command (current : AuditCurrent) (actor : Party) (kind : Mandate.Command Party) :
    Safe (Scoped.command current actor kind) := True.intro
theorem safe_access (actor : Party) (query : Query) : Safe (Scoped.accessRequest actor query) := by
  simp [Safe,Scoped.accessRequest]
theorem safe_fee : Safe Scoped.deliveryFee := by simp [Safe,Scoped.deliveryFee]
theorem stable_command (actor : Party) (kind : Mandate.Command Party) :
    Stable (fun current => Scoped.command current actor kind) :=
  ⟨fun _ _ same => same.command Scoped.scope actor kind,fun _ => True.intro⟩

theorem authorization {left right : AuditCurrent} (same : Twin left right) (actor : Party) :
    Scoped.authorization left actor = Scoped.authorization right actor := by
  have head := same.command Scoped.scope 0 (.propose actor)
  have tail := (AuditLaw.step same _ (safe_command left 0 (.propose actor))).command Scoped.scope actor .accept
  simp only [Scoped.authorization,Scoped.command]
  apply congrArg₂ List.cons head
  simpa only [Scoped.command,head] using congrArg (fun a => [a]) tail

theorem authorization_safe (current : AuditCurrent) (actor : Party) :
    ∀ action ∈ Scoped.authorization current actor,Safe action := by
  simp [Scoped.authorization,Safe,Scoped.command,Mandate.request]

theorem handoff {left right : AuditCurrent} (same : Twin left right) : Scoped.handoff left = Scoped.handoff right := by
  have head := same.command Scoped.scope 0 .revoke
  have tail := authorization (AuditLaw.step same _ (safe_command left 0 .revoke)) 2
  simp only [Scoped.handoff,Scoped.command]
  apply congrArg₂ List.cons head
  simpa only [Scoped.command,head] using tail

theorem handoff_safe (current : AuditCurrent) : ∀ action ∈ Scoped.handoff current,Safe action := by
  intro action member
  rcases List.mem_cons.mp member with rfl | inside
  · exact safe_command _ _ _
  · exact authorization_safe _ _ _ inside

theorem readWord {left right : AuditCurrent} (same : Twin left right) (actor : Party) (query : Query) :
    Scoped.readWord left actor query = Scoped.readWord right actor query := by
  simp only [Scoped.readWord,propext (AuditLaw.valid same _ (safe_access actor query)),
    propext (AuditLaw.valid (AuditLaw.step same _ (safe_access actor query)) _ safe_fee)]
theorem readWord_safe (current : AuditCurrent) (actor : Party) (query : Query) :
    ∀ action ∈ Scoped.readWord current actor query,Safe action := by
  unfold Scoped.readWord
  dsimp only
  split <;> simp [safe_access,safe_fee]

/-- The original private operation may succeed on only one branch; it still changes no public coordinate. -/
theorem private_step (current : AuditCurrent) (larger : Bool) :
    Twin current (auditLaw.step current (Scoped.privateUse larger)) := by
  unfold RawLaw.step
  split
  · refine ⟨rfl,rfl,rfl,rfl,?_⟩
    intro actor good visible
    cases good <;> simp_all [RawLaw.paidStep,RawLaw.debit,RawLaw.credit,Scoped.privateUse,locate,flowAt,amount]
  · exact Twin.refl _

theorem original_emit_next {left right : AuditCurrent} (same : Twin left right) (queries : Nat → Query) :
    Twin (auditLaw.next left (Scoped.emit queries false left))
      (auditLaw.next right (Scoped.emit queries true right)) := by
  unfold Scoped.emit
  rw [← same.round]
  dsimp only
  split
  · exact AuditLaw.next same _ (by simp [Scoped.preparation,Safe,Scoped.transferLabor])
  · rw [← authorization same 1]
    exact AuditLaw.next same _ (authorization_safe _ _)
  · have after := (private_step left false).symm.trans (same.trans (private_step right true))
    exact ⟨after.technology,congrArg (·+1) same.clock,congrArg Nat.succ same.round,after.claims,after.stock⟩
  · rw [← readWord same 1]
    exact AuditLaw.next same _ (readWord_safe _ _ _)
  · rw [← handoff same]
    exact AuditLaw.next same _ (handoff_safe _)
  · rw [← readWord same 1]
    exact AuditLaw.next same _ (readWord_safe _ _ _)
  · rw [← readWord same 2]
    exact AuditLaw.next same _ (readWord_safe _ _ _)
  · rw [← readWord same 2]
    exact AuditLaw.next same _ (readWord_safe _ _ _)
  · exact AuditLaw.next same _ (by simp [Scoped.refill,Safe,Scoped.transferLabor])
  · split
    · rw [← readWord same 2]; exact AuditLaw.next same _ (readWord_safe _ _ _)
    · exact AuditLaw.next same [] (by simp)

theorem expected (queries : Nat → Query) (cut : Nat) :
    Response.expectedAt queries false cut = Response.expectedAt queries true cut := by
  exact congrArg List.head? (records_have_identical_public_disclosure queries cut)

theorem review {left right : AuditCurrent} (same : Twin left right) (record : Record) (objection : Response.Objection) :
    Response.review left record objection = Response.review right record objection := by
  unfold Response.review
  simp only [same.technology,same.round,
    propext (AuditLaw.valid same _ (show Safe (Response.submission objection) from True.intro))]

theorem replacement {left right : AuditCurrent} (same : Twin left right) (actor : Party) :
    Response.replacement left actor = Response.replacement right actor := by
  simp only [Response.replacement,same.technology]

theorem fund_safe (before : AuditCurrent) (actor : Party) (donors : List Party) :
    ∀ action ∈ Response.fund before actor donors,Safe action := by
  induction donors generalizing before with
  | nil => simp [Response.fund]
  | cons donor rest ih =>
    unfold Response.fund
    dsimp only
    split
    · intro action member
      rcases List.mem_cons.mp member with rfl | inside
      · simp [Safe]
      · exact ih _ _ inside
    · exact ih _

theorem fund {left right : AuditCurrent} (same : Twin left right) (actor : Party) (donors : List Party) :
    Response.fund left actor donors = Response.fund right actor donors := by
  induction donors generalizing left right with
  | nil => rfl
  | cons donor rest ih =>
    have actorStock := same.stock actor .labor (by decide)
    have donorStock := same.stock donor .labor (by decide)
    simp only [Response.fund,← actorStock,← donorStock,← same.technology]
    split
    · congr 1
      exact ih (AuditLaw.step same _ (by simp [Safe]))
    · exact ih same

theorem response_attempt (before : AuditCurrent) (stages : List (AuditCurrent → Action)) :
    Response.attempt before stages = EnergyRenewal.attempt auditLaw before stages := by
  induction stages generalizing before with
  | nil => rfl
  | cons stage rest ih => simp only [Response.attempt,EnergyRenewal.attempt]; split <;> simp_all

theorem stages_stable (actor candidate : Party) (query : Query) :
    ∀ stage ∈ Response.stages actor candidate query,Stable stage := by
  simp only [Response.stages,List.mem_cons,List.not_mem_nil,or_false]
  intro stage member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact stable_command _ _
  · exact stable_command _ _
  · exact stable_command _ _
  · exact ⟨fun _ _ _ => rfl,fun _ => safe_access _ _⟩
  · exact ⟨fun _ _ _ => rfl,fun _ => safe_fee⟩

theorem response_safe (before : AuditCurrent) (record : Record) (objection : Response.Objection) :
    ∀ action ∈ Response.word before record objection,Safe action := by
  unfold Response.word
  split
  · intro action member
    rcases List.mem_cons.mp member with rfl | inside
    · exact True.intro
    rcases List.mem_append.mp inside with inside | inside
    · exact fund_safe _ _ _ _ inside
    split at inside
    · cases List.mem_singleton.mp inside; exact safe_command _ _ _
    · rw [response_attempt] at inside
      exact AuditLaw.attempt_safe _ _ (stages_stable _ _ _) _ inside
  · simp

theorem response {left right : AuditCurrent} (same : Twin left right) (record : Record) (objection : Response.Objection) :
    Response.word left record objection = Response.word right record objection := by
  have first := AuditLaw.step same (Response.submission objection) True.intro
  have supplies := fund first objection.challenger (Delegation.members Scoped.scope.task)
  have funded := AuditLaw.execute first
    (Response.fund (auditLaw.step left (Response.submission objection)) objection.challenger (Delegation.members Scoped.scope.task))
    (fund_safe _ _ _) 0
  unfold Response.word
  simp only [← review same record objection,← supplies]
  split
  · have replaced := replacement funded objection.challenger
    rw [← replaced]
    split
    · congr 2
      exact funded.command Scoped.scope objection.challenger .revoke
    · simp only [response_attempt]
      rw [AuditLaw.attempt funded _ (stages_stable _ _ _)]
  · rfl

theorem append_births {left right : AuditCurrent} (leftWord rightWord : List Action)
    (births : Governance.Births) (cut : Nat) :
    Twin (auditLaw.next left leftWord) (auditLaw.next right rightWord) →
      Twin (auditLaw.next left (leftWord ++ Governance.bornWord births cut))
        (auditLaw.next right (rightWord ++ Governance.bornWord births cut)) := by
  intro after
  have ignore (current : AuditCurrent) (items : List Action)
      (safe : ∀ action ∈ items,∃ key,action = Governance.birth key) (index : Nat) :
      (auditLaw.execute current index items).final = current := by
    induction items generalizing current index with
    | nil => rfl
    | cons head tail ih =>
      obtain ⟨key,rfl⟩ := safe head (by simp)
      change (auditLaw.execute (auditLaw.step current (Governance.birth key)) (index+1) tail).final = _
      rw [Governance.birth_does_not_grant_authority,ih _ (fun a h => safe a (List.mem_cons_of_mem _ h))]
  have birthsOnly : ∀ action ∈ Governance.bornWord births cut,∃ key,action = Governance.birth key := by
    intro action member
    obtain ⟨pair,_,rfl⟩ := List.mem_map.mp member
    exact ⟨pair.2,rfl⟩
  have eq (current : AuditCurrent) (word : List Action) : auditLaw.next current (word ++ Governance.bornWord births cut) = auditLaw.next current word := by
    simp only [RawLaw.next,RawLaw.execute_append,ignore _ _ birthsOnly]
  rw [eq,eq]
  exact after

/-- Original governance replies are consumed at every actual cut, including stale and refused submissions. -/
theorem current (queries : Nat → Query) (births : Governance.Births) (replies : Governance.Replies) (n : Nat) :
    Twin (Governance.current queries false births replies n) (Governance.current queries true births replies n) := by
  induction n with
  | zero => unfold Governance.current; exact Twin.refl _
  | succ n ih =>
    rw [Governance.current_succ,Governance.current_succ]
    split
    · exact AuditLaw.next ih [] (by simp)
    · unfold Governance.emit
      rw [← ih.round]
      dsimp only
      apply append_births
      split
      · rw [← expected]
        split
        · exact AuditLaw.next ih [] (by simp)
        · rw [← response ih]
          exact AuditLaw.next ih _ (response_safe _ _ _)
      · exact original_emit_next ih queries

end GovernancePrivacy
end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
