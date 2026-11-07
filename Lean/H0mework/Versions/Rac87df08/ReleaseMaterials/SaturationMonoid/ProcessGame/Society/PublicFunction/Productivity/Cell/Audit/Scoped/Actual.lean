import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Disclosure

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

def Silent (action : Action) : Prop := match action.operation with
  | .issue .. | .assign .. | .settle .. => False
  | _ => True

private theorem silent_step (before : AuditCurrent) (action : Action) (silent : Silent action) :
    (auditLaw.step before action).claims = before.claims := by
  unfold RawLaw.step
  split
  · change RawLaw.nextClaims before action = before.claims
    rcases action with ⟨signer,consents,purpose,gates,operation⟩
    cases operation <;> simp_all [Silent,RawLaw.nextClaims]
  · rfl

private theorem silent_execute (before : AuditCurrent) (index : Nat) (word : List Action)
    (silent : ∀ action ∈ word,Silent action) : (auditLaw.execute before index word).final.claims = before.claims := by
  induction word generalizing before index with
  | nil => rfl
  | cons head tail ih =>
      change (auditLaw.execute (auditLaw.step before head) (index + 1) tail).final.claims = _
      rw [ih _ _ (fun next inside => silent next (List.mem_cons_of_mem _ inside)),
        silent_step before head (silent head List.mem_cons_self)]

private theorem silent_pair (a b : Action) (first : Silent a) (second : Silent b) :
    ∀ action ∈ [a,b],Silent action := by
  intro action inside
  rcases List.mem_cons.mp inside with rfl | rest
  · exact first
  · exact List.mem_singleton.mp rest ▸ second

private theorem read_silent (before : AuditCurrent) (actor : Party) (query : Query) :
    ∀ action ∈ readWord before actor query,Silent action := by
  unfold readWord
  dsimp only
  split
  · exact silent_pair _ _ (by trivial) (by trivial)
  · intro action inside
    exact List.mem_singleton.mp inside ▸ (show Silent (accessRequest actor query) from True.intro)

private theorem authorization_silent (before : AuditCurrent) (actor : Party) :
    ∀ action ∈ authorization before actor,Silent action := silent_pair _ _ (by trivial) (by trivial)

theorem every_emitted_word_preserves_original_claims (queries : Nat → Query) (larger : Bool) (before : AuditCurrent) :
    (auditLaw.next before (emit queries larger before)).claims = before.claims := by
  apply silent_execute
  unfold emit
  dsimp only
  split
  · exact silent_pair _ _ (by trivial) (by trivial)
  · exact authorization_silent _ _
  · intro action inside
    exact List.mem_singleton.mp inside ▸ (show Silent (privateUse larger) from True.intro)
  · exact read_silent _ _ _
  · intro action inside
    rcases List.mem_cons.mp inside with rfl | rest
    · trivial
    · exact authorization_silent _ _ action rest
  · exact read_silent _ _ _
  · exact read_silent _ _ _
  · exact read_silent _ _ _
  · exact silent_pair _ _ (by trivial) (by trivial)
  · split
    · exact read_silent _ _ _
    · simp

theorem every_current_keeps_the_original_claim_matrix (queries : Nat → Query) (larger : Bool) (ordinal : Nat) :
    (current queries larger ordinal).claims = initial.claims := by
  induction ordinal with
  | zero => rw [current_zero]
  | succ ordinal ih =>
      rw [current_succ]
      cases ordinal with
      | zero => exact ih
      | succ ordinal =>
          simpa only [Nat.succ_ne_zero,if_false] using
            (every_emitted_word_preserves_original_claims queries larger (current queries larger (ordinal + 1))).trans ih

theorem current_round (queries : Nat → Query) (larger : Bool) (ordinal : Nat) :
    (current queries larger ordinal).round = initial.round + ordinal := by
  induction ordinal with
  | zero => rw [current_zero]; rfl
  | succ ordinal ih =>
      rw [current_succ]
      change (current queries larger ordinal).round + 1 = _
      rw [ih]
      omega

theorem actual_handoff_is_paid_and_generated :
    (Mandate.grantsAt baseLaw scope (current defaultQuery false 2)
      (emit defaultQuery false (current defaultQuery false 2))).isEmpty = false ∧
    (Mandate.grantsAt baseLaw scope (current defaultQuery false 5)
      (emit defaultQuery false (current defaultQuery false 5))).isEmpty = false ∧
    (emit defaultQuery false (current defaultQuery false 5)).map Request.signer = [0,0,2] := by decide +kernel

theorem every_generated_request_is_scope_bound (queries : Nat → Query) (larger : Bool) (cut : Nat)
    (actor : Party) (query : Query)
    (inside : (actor,query) ∈ actualQueries (emit queries larger (current queries larger cut))) :
    query = queries cut := by
  rw [query_schedule_is_the_actual_word,current_round] at inside
  unfold querySchedule at inside
  dsimp only at inside
  simp only [Nat.add_sub_cancel_left] at inside
  split at inside
  all_goals simp_all

theorem root_word_is_the_audit_word (queries : Nat → Query) (larger : Bool) (ordinal : Nat) :
    ProgrammeSource.rawEvent (input queries larger) (ProgrammeHistory.visitAt (input queries larger) (ordinal + 1)).current =
      emit queries larger (current queries larger (ordinal + 1)) := by
  rw [← current_is_own_root_current]
  change ProgrammeSource.rawEvent (input queries larger) (ProgrammeSource.next (input queries larger)
    (ProgrammeHistory.visitAt (input queries larger) ordinal).current) =
      emit queries larger (ProgrammeSource.rawCurrent (input queries larger) (ProgrammeSource.next (input queries larger)
        (ProgrammeHistory.visitAt (input queries larger) ordinal).current))
  generalize (ProgrammeHistory.visitAt (input queries larger) ordinal).current = prior
  cases prior <;> rfl

def actualNetLabor (before : AuditCurrent) (word : List Action) : ℚ :=
  ([0,1,2,3].map fun actor => auditLaw.totalDebit (auditLaw.rawItems before word) actor .labor -
    auditLaw.totalCredit (auditLaw.rawItems before word) actor .labor).sum

theorem labor_readout_is_the_actual_raw_net_flow (before : AuditCurrent) (word : List Action) :
    laborTotal (permittedView before) - laborTotal (permittedView (auditLaw.next before word)) =
      actualNetLabor before word := by
  have first := auditLaw.actual_next_material_balance before word 0 .labor
  have second := auditLaw.actual_next_material_balance before word 1 .labor
  have third := auditLaw.actual_next_material_balance before word 2 .labor
  have fourth := auditLaw.actual_next_material_balance before word 3 .labor
  simp only [laborTotal,permittedView,actualNetLabor,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  linarith

theorem actual_finite_funding_is_spent (larger : Bool) :
    laborTotal (permittedView initial) = 20 ∧
    laborTotal (permittedView (current defaultQuery larger 14)) = 1 ∧
    laborTotal (permittedView initial) - laborTotal (permittedView (current defaultQuery larger 14)) = 19 := by
  cases larger <;> decide +kernel

def privateTransfer : Action := ⟨3,[],native .common,[],.transfer 3 0 [(.feed,39)]⟩

theorem actual_private_histories_have_different_future_capacity :
    (current defaultQuery false 4).stock 3 .feed = 39 ∧
    (current defaultQuery true 4).stock 3 .feed = 38 ∧
    auditLaw.Valid (current defaultQuery false 4) privateTransfer ∧
    ¬ auditLaw.Valid (current defaultQuery true 4) privateTransfer := by decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped
