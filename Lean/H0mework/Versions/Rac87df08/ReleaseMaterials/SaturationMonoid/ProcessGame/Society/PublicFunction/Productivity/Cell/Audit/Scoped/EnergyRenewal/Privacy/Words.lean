import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Step

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

private theorem read_stable (actor : Party) (query : Query) :
    ∀ stage ∈ [fun _ : AuditCurrent => accessRequest actor query,fun _ => deliveryFee],StableStage stage := by
  intro stage member
  rcases List.mem_cons.mp member with rfl | member
  · exact stable_access actor query
  · cases List.mem_singleton.mp member
    exact stable_fee

private theorem grant_stable (scope : Scope) (actor : Party) (query : Query) :
    ∀ stage ∈ [fun state : AuditCurrent => Mandate.request scope state 0 (.propose actor),
      fun state => Mandate.request scope state actor .accept,
      fun _ => accessRequest actor query,fun _ => deliveryFee],StableStage stage := by
  intro stage member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact stable_command scope 0 (.propose actor)
  · exact stable_command scope actor .accept
  · exact stable_access actor query
  · exact stable_fee

private theorem repair_stable (actor : Party) (query : Query) :
    ∀ stage ∈ [fun _ : AuditCurrent => transfer actor 3,
      fun _ => accessRequest actor query,fun _ => deliveryFee],StableStage stage := by
  intro stage member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact stable_transfer actor 3
  · exact stable_access actor query
  · exact stable_fee

theorem window_word_energy {plan : Plan} (window : Continuation.Window plan)
    (request : Continuation.Request) (current : AuditCurrent) :
    ∀ action ∈ window.word request current, EnergyAction action := by
  have reads : ∀ state,∀ action ∈ window.readWord state request.query,EnergyAction action := by
    intro state
    exact attempt_energy window.scope state _ (read_stable _ _)
  cases command : request.command <;> simp only [Continuation.Window.word,command]
  · exact reads current
  · split
    · intro action member
      rcases List.mem_append.mp member with member | member
      · exact reads _ _ member
      · exact attempt_energy window.scope _ _ (repair_stable _ _) _ member
    · exact reads current
  · intro action member
    rcases List.mem_append.mp member with member | member
    · cases List.mem_singleton.mp member
      trivial
    · exact reads _ _ member
  · split
    · exact attempt_energy window.scope _ _ (by
        intro stage member
        cases List.mem_singleton.mp member
        exact stable_application)
    · simp
  · exact attempt_energy window.scope _ _ (grant_stable _ _ _)

theorem Twin.window_word {left right : AuditCurrent} (same : Twin left right)
    {lp rp : Plan} (leftWindow : Continuation.Window lp) (rightWindow : Continuation.Window rp)
    (scope : leftWindow.scope = rightWindow.scope) (candidate : lp.candidate = rp.candidate)
    (request : Continuation.Request) :
    leftWindow.word request left = rightWindow.word request right := by
  have cost : leftWindow.scope.revisionCost = [(.energy,1)] := rfl
  have lawEq : leftWindow.law = rightWindow.law := congrArg (Mandate.law energyBase) scope
  have reads : ∀ l r,Twin l r → leftWindow.readWord l request.query = rightWindow.readWord r request.query := by
    intro l r twin
    change EnergyRenewal.attempt (law leftWindow.scope) l _ = EnergyRenewal.attempt (law rightWindow.scope) r _
    rw [← scope,← candidate]
    exact twin.attempt _ cost _ (read_stable _ _)
  have visible : PublicDebit leftWindow.scope left (accessRequest lp.candidate request.query) :=
    energy_public _ cost left _ ((stable_access _ _).2 left)
  cases command : request.command <;> simp only [Continuation.Window.word,command]
  · exact reads _ _ same
  · have condition :
        (¬leftWindow.law.Valid left (accessRequest lp.candidate request.query) ∧
          left.technology.holder = some lp.candidate ∧ leftWindow.scope.task.earliest ≤ left.clock ∧
          left.clock ≤ leftWindow.scope.task.deadline) ↔
        (¬rightWindow.law.Valid right (accessRequest rp.candidate request.query) ∧
          right.technology.holder = some rp.candidate ∧ rightWindow.scope.task.earliest ≤ right.clock ∧
          right.clock ≤ rightWindow.scope.task.deadline) := by
      rw [← scope,← candidate,← lawEq]
      change (¬(law leftWindow.scope).Valid left _ ∧ _) ↔ (¬(law leftWindow.scope).Valid right _ ∧ _)
      simp only [same.valid leftWindow.scope _ visible,same.technology,same.clock]
    simp only [condition]
    split
    · rw [reads _ _ same]
      congr 1
      have executed := same.execute leftWindow.scope cost (leftWindow.readWord left request.query)
        (by intro action inside; exact attempt_energy _ _ _ (read_stable _ _) _ inside) 0
      rw [reads _ _ same] at executed
      rw [← lawEq]
      change EnergyRenewal.attempt (law leftWindow.scope) _ _ = EnergyRenewal.attempt (law leftWindow.scope) _ _
      rw [← candidate]
      exact executed.attempt _ cost _ (repair_stable _ _)
    · exact reads _ _ same
  · have action := same.command leftWindow.scope 0 .revoke
    simp only [← scope,← action]
    congr 1
    apply reads
    rw [← lawEq]
    exact same.step _ _ (energy_public _ cost _ _ (by trivial))
  · have quiet : Quiet left ↔ Quiet right := by simp only [Quiet,same.technology]
    simp only [quiet,same.clock,← scope]
    split
    · rw [← lawEq]
      exact same.attempt _ cost _ (by
        intro stage member
        cases List.mem_singleton.mp member
        exact stable_application)
    · rfl
  · change EnergyRenewal.attempt (law leftWindow.scope) left _ = EnergyRenewal.attempt (law rightWindow.scope) right _
    rw [← scope,← candidate]
    exact same.attempt _ cost _ (grant_stable _ _ _)

private theorem handoff_stable {plan : Plan} (seed : Handoff.Seed plan) (actor : Party) (query : Query) :
    ∀ stage ∈ seed.stages actor query,StableStage stage := by
  intro stage member
  simp only [Handoff.Seed.stages,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact stable_command _ _ _
  · exact stable_topUp _ _
  · exact stable_topUp _ _
  · exact stable_command _ _ _
  · exact stable_command _ _ _
  · exact stable_access _ _
  · exact stable_fee

theorem handoff_word_energy {plan : Plan} (seed : Handoff.Seed plan)
    (request : Handoff.Request) (current : AuditCurrent) :
    ∀ action ∈ seed.word request current,EnergyAction action := by
  unfold Handoff.Seed.word
  split
  · split
    · simp
    · exact attempt_energy seed.scope _ _ (handoff_stable _ _ _)
  · exact attempt_energy seed.scope _ _ (read_stable _ _)

theorem Twin.handoff_word {left right : AuditCurrent} (same : Twin left right)
    {lp rp : Plan} (leftSeed : Handoff.Seed lp) (rightSeed : Handoff.Seed rp)
    (scope : leftSeed.scope = rightSeed.scope) (request : Handoff.Request) :
    leftSeed.word request left = rightSeed.word request right := by
  have candidates : leftSeed.candidates left = rightSeed.candidates right := by
    simp only [Handoff.Seed.candidates,scope,same.technology]
  have target : leftSeed.target left = rightSeed.target right := by
    simp only [Handoff.Seed.target,candidates]
  have cost : leftSeed.scope.revisionCost = [(.energy,1)] := rfl
  unfold Handoff.Seed.word
  simp only [candidates,same.technology]
  split
  · split
    · rfl
    · change EnergyRenewal.attempt (law leftSeed.scope) left _ = EnergyRenewal.attempt (law rightSeed.scope) right _
      simp only [Handoff.Seed.stages,← scope,← target]
      exact same.attempt _ cost _ (handoff_stable leftSeed _ _)
  · change EnergyRenewal.attempt (law leftSeed.scope) left _ = EnergyRenewal.attempt (law rightSeed.scope) right _
    rw [← scope]
    exact same.attempt _ cost _ (read_stable _ _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
