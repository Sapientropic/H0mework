import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Online
import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.PrivateStock

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Timing
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root Lean

/-- All actors and all other inventory coordinates, claims and technology remain intact. -/
def rebuild (visible : AuditCurrent) (frame : Party → ℚ) : AuditCurrent :=
  { visible with stock := fun actor good => if good = .feed then frame actor else visible.stock actor good }

def publicize (current : AuditCurrent) : AuditCurrent := rebuild current (fun _ => 0)
def ownFrame (current : AuditCurrent) : Party → ℚ := fun actor => current.stock actor .feed

theorem rebuild_twin (visible : AuditCurrent) (frame : Party → ℚ) : Twin visible (rebuild visible frame) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro actor good visible
  simp [rebuild,visible]

theorem rebuild_from_twin {visible own : AuditCurrent} (same : Twin visible own) :
    rebuild visible (ownFrame own) = own := by
  apply RawCurrent.ext
  · funext actor good
    by_cases privateGood : good = .feed
    · simp [rebuild,ownFrame,privateGood]
    · simpa [rebuild,privateGood] using same.stock actor good privateGood
  · exact same.claims
  · exact same.technology
  · exact same.clock
  · exact same.round

theorem initial_private_frame_is_exact (current : AuditCurrent) :
    rebuild (publicize current) (ownFrame current) = current := by
  exact rebuild_from_twin (visible := publicize current) (by
    refine ⟨rfl,rfl,rfl,rfl,?_⟩
    intro actor good visible
    simp [publicize,rebuild,visible])

/-- The actual next is reconstructed now; it is not conditional on a future private replay. -/
theorem rebuild_commutes_with_actual_next (scope : Scope) (cost : scope.revisionCost = [(.energy,1)])
    (visible : AuditCurrent) (frame : Party → ℚ) (word : List Action)
    (generated : ∀ action ∈ word, EnergyAction action) :
    rebuild ((law scope).next visible word) frame = (law scope).next (rebuild visible frame) word := by
  have related := (rebuild_twin visible frame).next scope cost word generated
  have frames : ownFrame ((law scope).next (rebuild visible frame) word) = frame := by
    funext actor
    change ((law scope).execute (rebuild visible frame) 0 word).final.stock actor .feed = frame actor
    rw [energy_private_execute scope cost _ word generated 0 actor]
    simp [rebuild]
  simpa [frames] using rebuild_from_twin related

theorem handoff_rebuild_is_own_current {lp rp : Plan} {visible : Handoff.Seed lp} {own : Handoff.Seed rp}
    (same : SeedTwin visible own) (requests : List Handoff.Request) (n : Nat) :
    rebuild (visible.current requests n) (ownFrame own.window.initial) = own.current requests n := by
  have frame : ownFrame (own.current requests n) = ownFrame own.window.initial := by
    funext actor
    exact handoff_keeps_own_private_feed own requests n actor
  simpa [frame] using rebuild_from_twin (same.current requests n)

theorem handoff_rebuild_is_own_root_next {lp rp : Plan} {visible : Handoff.Seed lp} {own : Handoff.Seed rp}
    (same : SeedTwin visible own) (requests : List Handoff.Request) (request : Handoff.Request) :
    rebuild (visible.current (requests++[request]) (visible.ordinal+requests.length+2))
        (ownFrame own.window.initial) =
      ProgrammeSource.rawCurrent (own.input (requests++[request]))
        (ProgrammeHistory.visitAt (own.input (requests++[request])) (own.ordinal+requests.length+2)).current := by
  rw [same.ordinal,handoff_rebuild_is_own_current same]
  exact online_handoff_next_is_own_root own requests request

/-- A hidden source frame has no argument position on the visible channel's execution path. -/
def run {State Noise Observation Frame : Type} (channel : Network.Channel State Noise Observation)
    (initial : State) (frame : Frame) (strategy : List Observation → Nat → Json) (tape : Nat → Noise)
    (count : Nat) : Frame × (State × List Observation) :=
  (frame,Network.publicRun channel initial strategy tape count)

theorem all_private_frames_have_the_same_complete_timed_observation {State Noise Observation Frame : Type}
    (channel : Network.Channel State Noise Observation) (initial : State) (left right : Frame)
    (strategy : List Observation → Nat → Json) (tape : Nat → Noise) (count : Nat) :
    (run channel initial left strategy tape count).2 = (run channel initial right strategy tape count).2 := rfl

theorem framed_public_run_is_actual {State Noise Observation Frame : Type}
    (channel : Network.Channel State Noise Observation) (initial : State) (frame : Frame) (larger : Bool)
    (strategy : List Observation → Nat → Json) (tape : Nat → Noise) (count : Nat) :
    (run channel initial frame strategy tape count).2 = Network.run channel larger initial strategy tape count :=
  Network.public_run_is_actual channel larger initial strategy tape count

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Timing
