import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Complete

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

private theorem flow_feed_zero (flow : Flow Party Good) (absent : ∀ item ∈ flow,item.1.2 ≠ .feed) (actor : Party) :
    flowAt flow actor .feed = 0 := by
  unfold flowAt amount
  apply List.sum_eq_zero
  intro quantity member
  obtain ⟨entry,inside,rfl⟩ := List.mem_map.mp member
  have different : entry.1 ≠ (actor,.feed) := by
    intro equal
    exact absent entry inside (congrArg Prod.snd equal)
  simp only [if_neg different]

theorem energy_private_step (scope : Scope) (cost : scope.revisionCost = [(.energy,1)])
    (current : AuditCurrent) (action : Action) (energy : EnergyAction action) (actor : Party) :
    ((law scope).step current action).stock actor .feed = current.stock actor .feed := by
  have debit := energy_public scope cost current action energy
  have credit : ∀ item ∈ (law scope).credit current action,item.1.2 ≠ .feed := by
    cases operation : action.operation <;> simp only [EnergyAction,operation] at energy
    case transfer sender recipient goods =>
      intro entry inside
      simp only [RawLaw.credit,operation,locate,List.mem_map] at inside
      obtain ⟨item,member,rfl⟩ := inside
      rw [energy item member]
      simp
    case use bearer goods purpose | revise bearer target => simp [RawLaw.credit,operation]
  unfold RawLaw.step
  split
  · simp only [RawLaw.paidStep,flow_feed_zero _ debit actor,flow_feed_zero _ credit actor,sub_zero,add_zero]
  · rfl

theorem energy_private_execute (scope : Scope) (cost : scope.revisionCost = [(.energy,1)])
    (current : AuditCurrent) (word : List Action) (energy : ∀ action ∈ word,EnergyAction action) (index actor : Nat) :
    ((law scope).execute current index word).final.stock actor .feed = current.stock actor .feed := by
  induction word generalizing current index with
  | nil => rfl
  | cons action rest ih =>
    change ((law scope).execute ((law scope).step current action) (index+1) rest).final.stock actor .feed = _
    rw [ih _ (fun action inside => energy _ (List.mem_cons_of_mem _ inside)) (index+1),
      energy_private_step _ cost _ _ (energy _ (by simp)) actor]

theorem window_keeps_own_private_feed {plan : Plan} (window : Continuation.Window plan)
    (requests : List Continuation.Request) (n actor : Nat) :
    (window.current requests n).stock actor .feed = window.initial.stock actor .feed := by
  induction n with
  | zero => unfold Continuation.Window.current; rfl
  | succ n ih =>
    rw [window.current_succ]
    trans (window.current requests n).stock actor .feed
    · exact energy_private_execute _ rfl _ _ (windowWord_energy window requests n) 0 actor
    · exact ih

theorem handoff_keeps_own_private_feed {plan : Plan} (seed : Handoff.Seed plan)
    (requests : List Handoff.Request) (n actor : Nat) :
    (seed.current requests n).stock actor .feed = seed.window.initial.stock actor .feed := by
  induction n with
  | zero => unfold Handoff.Seed.current; rfl
  | succ n ih =>
    rw [seed.current_succ]
    trans (seed.current requests n).stock actor .feed
    · apply energy_private_execute _ rfl
      split
      · simp
      · exact seed_emit_energy _ _ _
    · exact ih

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
