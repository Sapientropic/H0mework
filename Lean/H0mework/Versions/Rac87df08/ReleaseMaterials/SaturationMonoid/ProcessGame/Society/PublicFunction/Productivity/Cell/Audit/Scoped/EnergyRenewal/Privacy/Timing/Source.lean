import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Timing

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Timing
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

def handoffFromWindow {plan : Plan} (input : SourceInput) (initial : Continuation.Window plan) : Except String (Handoff.Seed plan) :=
  if input.commands.phases.isEmpty ∨ input.commands.phases.any List.isEmpty then .error "EMPTY_PHASE"
  else match input.commands.handoffs with
  | none => .error "HANDOFF_REQUIRED"
  | some requests => if requests.isEmpty then .error "EMPTY_HANDOFF" else
    (phaseWindows initial (input.cut+input.ordinal+2) input.commands.phases.dropLast).map fun (window,_) =>
      Handoff.fromConsumed window input.commands.phases.getLast! input.commands.phases.getLast!.length

/-- Original arguments generate the seed and its private frame; no inventory or target next is supplied. -/
def sourceHandoffSeed (larger : Bool) (input : SourceInput) : Except String (Handoff.Seed (input.plan larger)) :=
  (initialWindows larger input).elim (.error "ORIGINAL_SUPPLY_NOT_READY") (handoffFromWindow input)

theorem original_source_generates_related_handoff_seeds (larger : Bool) (input : SourceInput) :
    ResultRel SeedTwin (sourceHandoffSeed false input) (sourceHandoffSeed larger input) := by
  have mapped : ∀ {lp rp : Plan} {left : Except String (Continuation.Window lp × Nat)}
      {right : Except String (Continuation.Window rp × Nat)},
      ResultRel (fun l r => WindowTwin l.1 r.1 ∧ l.2 = r.2) left right →
      ResultRel SeedTwin
        (left.map fun (window,_) => Handoff.fromConsumed window input.commands.phases.getLast! input.commands.phases.getLast!.length)
        (right.map fun (window,_) => Handoff.fromConsumed window input.commands.phases.getLast! input.commands.phases.getLast!.length) := by
    intro lp rp left right relation
    cases relation with
    | error _ => exact .error _
    | ok matched => exact .ok ⟨matched.1,rfl,rfl⟩
  have windows : ∀ {lp rp : Plan} {left : Continuation.Window lp} {right : Continuation.Window rp},
      WindowTwin left right → ResultRel SeedTwin (handoffFromWindow input left) (handoffFromWindow input right) := by
    intro lp rp left right same
    unfold handoffFromWindow
    split
    · exact .error _
    · split
      · exact .error _
      · split
        · exact .error _
        · exact mapped (same.phases (input.cut+input.ordinal+2) input.commands.phases.dropLast)
  have formed : ∀ {lp rp : Plan} {left : Option (Continuation.Window lp)} {right : Option (Continuation.Window rp)},
      Option.Rel WindowTwin left right →
      ResultRel SeedTwin (left.elim (.error "ORIGINAL_SUPPLY_NOT_READY") (handoffFromWindow input))
        (right.elim (.error "ORIGINAL_SUPPLY_NOT_READY") (handoffFromWindow input)) := by
    intro lp rp left right relation
    cases relation with
    | none => exact .error _
    | some same => exact windows same
  cases larger with
  | false =>
    cases sourceHandoffSeed false input with
    | error message => exact .error message
    | ok seed => exact .ok ⟨⟨rfl,rfl,Twin.refl _⟩,rfl,rfl⟩
  | true =>
    unfold sourceHandoffSeed
    exact formed (lp := input.plan false) (rp := input.plan true)
      (left := initialWindows false input) (right := initialWindows true input) (initial_windows_are_generated input)

def rebuiltSourceNext (larger : Bool) (input : SourceInput) : Except String AuditCurrent := do
  let visible ← sourceHandoffSeed false input
  let own ← sourceHandoffSeed larger input
  let requests := input.commands.handoffs.getD []
  return rebuild (visible.current requests (visible.ordinal+requests.length+1)) (ownFrame own.window.initial)

def actualSourceRootNext (larger : Bool) (input : SourceInput) : Except String AuditCurrent :=
  (sourceHandoffSeed larger input).map fun own =>
    let requests := input.commands.handoffs.getD []
    ProgrammeSource.rawCurrent (own.input requests)
      (ProgrammeHistory.visitAt (own.input requests) (own.ordinal+requests.length+1)).current

/-- The complete own-root next is reconstructed at the public event, without a future replay premise. -/
theorem public_next_with_generated_frame_is_actual_root_next (larger : Bool) (input : SourceInput) :
    rebuiltSourceNext larger input = actualSourceRootNext larger input := by
  have recognize : ∀ {lp rp : Plan} {left : Except String (Handoff.Seed lp)} {right : Except String (Handoff.Seed rp)},
      ResultRel SeedTwin left right →
      (do
        let visible ← left
        let own ← right
        let requests := input.commands.handoffs.getD []
        pure (rebuild (visible.current requests (visible.ordinal+requests.length+1)) (ownFrame own.window.initial))) =
      right.map (fun own =>
        let requests := input.commands.handoffs.getD []
        ProgrammeSource.rawCurrent (own.input requests)
          (ProgrammeHistory.visitAt (own.input requests) (own.ordinal+requests.length+1)).current) := by
    intro lp rp left right relation
    cases relation with
    | error _ => rfl
    | ok same =>
      dsimp only [Except.bind,Except.map]
      apply congrArg Except.ok
      rw [same.ordinal,handoff_rebuild_is_own_current same]
      exact (Handoff.Seed.current_is_own_root_current _ _ _).symm
  exact recognize (lp := input.plan false) (rp := input.plan larger)
    (left := sourceHandoffSeed false input) (right := sourceHandoffSeed larger input)
    (original_source_generates_related_handoff_seeds larger input)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Timing
