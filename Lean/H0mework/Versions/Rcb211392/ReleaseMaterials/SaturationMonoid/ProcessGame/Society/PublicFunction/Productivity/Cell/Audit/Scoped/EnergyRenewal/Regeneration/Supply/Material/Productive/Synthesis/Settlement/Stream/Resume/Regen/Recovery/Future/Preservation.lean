import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

def Tracked {basis : State} (protocol : Protocol basis) (window : Requests.Window basis) : Prop :=
  protocol.pending = some window ∨ Debt.requested window ∈ protocol.expired.map PastDue.debt ∨
    window ∈ protocol.completed.map Completion.window

private theorem stream_update_tracks_pending (basis : State) (requests : Requests.Source)
    (ordinal : Nat) (frame : Frame basis) (window : Requests.Window basis)
    (pending : frame.protocol.pending = some window) :
    Tracked (Stream.update basis requests ordinal frame) window := by
  unfold Tracked
  by_cases zero : ordinal = 0
  · simpa only [Stream.update, if_pos zero] using (Or.inl pending : Tracked frame.protocol window)
  · simp only [Stream.update, if_neg zero, pending]
    split
    · exact .inr (.inl (by simp))
    · split
      · exact .inl rfl
      · split
        · exact .inr (.inr (by simp))
        · exact .inl rfl

private theorem resume_update_tracks_pending (seed : Seed) (requests : Requests.Source)
    (permission : Material.Mode) (ordinal : Nat) (frame : Frame seed.basis)
    (window : Requests.Window seed.basis) (pending : frame.protocol.pending = some window) :
    Tracked (Resume.update seed requests permission ordinal frame) window := by
  rw [Resume.update_exact]
  split
  · exact .inl pending
  · unfold Material.update
    split
    · exact .inl pending
    · exact stream_update_tracks_pending seed.basis requests ordinal frame window pending

private theorem recovery_step_tracks_pending (seed : Seed) (requests : Requests.Source)
    (authority : Authority) (permission : Material.Mode) (ordinal : Nat) (frame : Frame seed.basis)
    (window : Requests.Window seed.basis) (pending : frame.protocol.pending = some window) :
    Tracked (Recovery.step seed requests authority permission ordinal frame).protocol window := by
  dsimp only [Recovery.step]
  split
  · unfold Regen.step
    split
    · exact .inl pending
    · exact resume_update_tracks_pending seed requests .normal ordinal frame window pending
  · exact .inl pending
  · exact .inl pending

private theorem stream_update_preserves_records (basis : State) (requests : Requests.Source)
    (ordinal : Nat) (frame : Frame basis) :
    frame.protocol.expired <+: (Stream.update basis requests ordinal frame).expired ∧
    frame.protocol.completed <+: (Stream.update basis requests ordinal frame).completed := by
  dsimp only [Stream.update]
  split
  · exact ⟨List.prefix_rfl, List.prefix_rfl⟩
  · split
    · split
      · exact ⟨List.prefix_append _ _, List.prefix_rfl⟩
      · split
        · exact ⟨List.prefix_rfl, List.prefix_rfl⟩
        · split
          · exact ⟨List.prefix_rfl, List.prefix_append _ _⟩
          · exact ⟨List.prefix_rfl, List.prefix_rfl⟩
    · split
      · exact ⟨List.prefix_rfl, List.prefix_rfl⟩
      · split <;> exact ⟨List.prefix_rfl, List.prefix_rfl⟩

private theorem resume_update_preserves_records (seed : Seed) (requests : Requests.Source)
    (permission : Material.Mode) (ordinal : Nat) (frame : Frame seed.basis) :
    frame.protocol.expired <+: (Resume.update seed requests permission ordinal frame).expired ∧
    frame.protocol.completed <+: (Resume.update seed requests permission ordinal frame).completed := by
  rw [Resume.update_exact]
  split
  · exact ⟨List.prefix_rfl, List.prefix_rfl⟩
  · unfold Material.update
    split
    · exact ⟨List.prefix_rfl, List.prefix_rfl⟩
    · exact stream_update_preserves_records seed.basis requests ordinal frame

private theorem recovery_step_preserves_records (seed : Seed) (requests : Requests.Source)
    (authority : Authority) (permission : Material.Mode) (ordinal : Nat) (frame : Frame seed.basis) :
    frame.protocol.expired <+: (Recovery.step seed requests authority permission ordinal frame).protocol.expired ∧
    frame.protocol.completed <+: (Recovery.step seed requests authority permission ordinal frame).protocol.completed := by
  dsimp only [Recovery.step]
  split
  · unfold Regen.step
    split
    · exact ⟨List.prefix_rfl, List.prefix_rfl⟩
    · exact resume_update_preserves_records seed requests .normal ordinal frame
  · exact ⟨List.prefix_rfl, List.prefix_rfl⟩
  · exact ⟨List.prefix_rfl, List.prefix_rfl⟩

variable {seed : Seed} {oldRequests : Requests.Source} {oldPermission : Material.Mode} {baseCut : Nat}
  {source : Inherited seed oldRequests oldPermission baseCut}
  {requests : Requests.Source} {authority : Authority} {index : Nat}
  {cut : Cut source requests authority index} {count : Nat}
  (original : Snapshot cut count)
  (futureRequests : Requests.Source) (futureAuthority : Authority) (futurePermission : Material.Mode)

theorem step_preserves_all_records (offset : Nat) (frame : Frame seed.basis) :
    frame.protocol.expired <+:
      (step original futureRequests futureAuthority futurePermission offset frame).protocol.expired ∧
    frame.protocol.completed <+:
      (step original futureRequests futureAuthority futurePermission offset frame).protocol.completed := by
  unfold step
  split
  · exact recovery_step_preserves_records seed futureRequests futureAuthority futurePermission _ frame
  · exact ⟨List.prefix_rfl, List.prefix_rfl⟩

theorem every_finite_future_preserves_due_and_completed (n : Nat) :
    original.frame.protocol.expired <+:
      (run original futureRequests futureAuthority futurePermission n).protocol.expired ∧
    original.frame.protocol.completed <+:
      (run original futureRequests futureAuthority futurePermission n).protocol.completed := by
  induction n with
  | zero => exact ⟨List.prefix_rfl, List.prefix_rfl⟩
  | succ n previous =>
    rw [run_succ]
    have later := step_preserves_all_records original futureRequests futureAuthority futurePermission n
      (run original futureRequests futureAuthority futurePermission n)
    exact ⟨previous.1.trans later.1, previous.2.trans later.2⟩

theorem step_accounts_for_every_pending_window (offset : Nat) (frame : Frame seed.basis)
    (window : Requests.Window seed.basis) (pending : frame.protocol.pending = some window) :
    Tracked (step original futureRequests futureAuthority futurePermission offset frame).protocol window := by
  unfold step
  split
  · exact recovery_step_tracks_pending seed futureRequests futureAuthority futurePermission _ frame window pending
  · exact .inl pending

theorem step_preserves_every_tracked_window (offset : Nat) (frame : Frame seed.basis)
    (window : Requests.Window seed.basis) (tracked : Tracked frame.protocol window) :
    Tracked (step original futureRequests futureAuthority futurePermission offset frame).protocol window := by
  rcases tracked with pending | due | paid
  · exact step_accounts_for_every_pending_window original futureRequests futureAuthority futurePermission
      offset frame window pending
  · exact .inr (.inl ((step_preserves_all_records original futureRequests futureAuthority futurePermission
      offset frame).1.map PastDue.debt |>.mem due))
  · exact .inr (.inr ((step_preserves_all_records original futureRequests futureAuthority futurePermission
      offset frame).2.map Completion.window |>.mem paid))

theorem every_finite_future_accounts_for_every_old_window (n : Nat)
    (window : Requests.Window seed.basis) (tracked : Tracked original.frame.protocol window) :
    Tracked (run original futureRequests futureAuthority futurePermission n).protocol window := by
  induction n with
  | zero => exact tracked
  | succ n previous =>
    rw [run_succ]
    exact step_preserves_every_tracked_window original futureRequests futureAuthority futurePermission n _ window previous

private theorem recovery_word_is_historical (seed : Seed) (requests : Requests.Source)
    (authority : Authority) (permission : Material.Mode) (ordinal : Nat) (frame : Frame seed.basis) :
    ∀ action ∈ Recovery.word seed requests authority permission ordinal frame, Historical action := by
  dsimp only [Recovery.word]
  split
  · unfold Regen.word
    split
    · exact Supply.lot_historical _ _ _
    · rw [Resume.word_exact]
      exact Material.every_action_keeps_old_instruments seed.basis requests .normal ordinal frame
  · rename_i choice selected
    intro action present
    have retained := choice.property.2.2.2.1 action present
    cases operation : action.operation <;> simp_all [RetainsClaims, Historical]
  · simp

theorem every_emitted_action_preserves_old_instruments (offset : Nat) (frame : Frame seed.basis) :
    ∀ action ∈ word original futureRequests futureAuthority futurePermission offset frame, Historical action := by
  unfold word
  split
  · exact recovery_word_is_historical seed futureRequests futureAuthority futurePermission _ frame
  · simp

open private Stream.safe_execution from H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream

theorem every_finite_future_preserves_old_claims (n : Nat) (instrument : Instrument)
    (old : instrument ≠ .delivery) :
    (run original futureRequests futureAuthority futurePermission n).raw.claims instrument =
      original.frame.raw.claims instrument := by
  induction n with
  | zero => rfl
  | succ n previous =>
    rw [run_succ]
    rw [step_uses_its_actual_word]
    exact (Stream.safe_execution _ _ _ 0
      (every_emitted_action_preserves_old_instruments original futureRequests futureAuthority futurePermission n _)
      instrument old).trans previous

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future
