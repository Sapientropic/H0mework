import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Complete

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root Lean

/-- Requests contain commands and masks, never a caller-provided material world. -/
structure Input where
  phases : List (List Continuation.Request)
  handoffs : Option (List Handoff.Request)

inductive ResultRel {α β : Type} (related : α → β → Prop) : Except String α → Except String β → Prop
  | error (message : String) : ResultRel related (.error message) (.error message)
  | ok {left : α} {right : β} (same : related left right) : ResultRel related (.ok left) (.ok right)

def phaseWindows {plan : Plan} (window : Continuation.Window plan) (nextCut : Nat) :
    List (List Continuation.Request) → Except String (Continuation.Window plan × Nat)
  | [] => .ok (window,nextCut)
  | phase :: rest => match window.nextWindow phase phase.length with
    | none => .error "PREVIOUS_WINDOW_NOT_GENERATED"
    | some next => phaseWindows next (nextCut+phase.length+1) rest

theorem WindowTwin.phases {lp rp : Plan} {left : Continuation.Window lp} {right : Continuation.Window rp}
    (same : WindowTwin left right) (nextCut : Nat) (phases : List (List Continuation.Request)) :
    ResultRel (fun l r => WindowTwin l.1 r.1 ∧ l.2 = r.2)
      (phaseWindows left nextCut phases) (phaseWindows right nextCut phases) := by
  induction phases generalizing left right nextCut with
  | nil => exact .ok ⟨same,rfl⟩
  | cons phase rest ih =>
    unfold phaseWindows
    have useNext : ∀ {l : Option (Continuation.Window lp)} {r : Option (Continuation.Window rp)},
        Option.Rel WindowTwin l r → ResultRel (fun l r => WindowTwin l.1 r.1 ∧ l.2 = r.2)
          (match l with | none => .error "PREVIOUS_WINDOW_NOT_GENERATED" | some w => phaseWindows w (nextCut+phase.length+1) rest)
          (match r with | none => .error "PREVIOUS_WINDOW_NOT_GENERATED" | some w => phaseWindows w (nextCut+phase.length+1) rest) := by
      intro l r related
      cases related with
      | none => exact .error _
      | some twin => exact ih twin _
    exact useNext (same.nextWindow phase phase.length)

/-- Same full return carrier as the native executables, including exact source errors. -/
def response {plan : Plan} (initial : Continuation.Window plan) (initialCut : Nat) (input : Input) : Except String Json :=
  if input.phases.isEmpty ∨ input.phases.any List.isEmpty then .error "EMPTY_PHASE"
  else (phaseWindows initial initialCut input.phases.dropLast).bind fun (window,nextCut) =>
    let phase := input.phases.getLast!
    match input.handoffs with
    | none => .ok (continuationJson window phase phase.length (input.phases.length-1) (nextCut+phase.length+1))
    | some received =>
      if received.isEmpty then .error "EMPTY_HANDOFF" else
        let seed := Handoff.fromConsumed window phase phase.length
        .ok (handoffJson seed received (phase.length+received.length) (nextCut+phase.length+1+received.length))

theorem ResultRel.bind_eq {α β : Type} {related : α → β → Prop} {left : Except String α} {right : Except String β}
    (same : ResultRel related left right) (f : α → Except String Json) (g : β → Except String Json)
    (success : ∀ a b,related a b → f a = g b) : left.bind f = right.bind g := by
  cases same with
  | error => rfl
  | ok relation => exact success _ _ relation

theorem WindowTwin.response {lp rp : Plan} {left : Continuation.Window lp} {right : Continuation.Window rp}
    (same : WindowTwin left right) (initialCut : Nat) (input : Input) :
    response left initialCut input = response right initialCut input := by
  unfold Privacy.response
  split
  · rfl
  · apply ResultRel.bind_eq (same.phases initialCut input.phases.dropLast)
    intro l r matched
    rcases matched with ⟨twin,cut⟩
    simp only [cut]
    split
    · exact congrArg Except.ok (twin.complete _ _ _ _)
    · split
      · rfl
      · exact congrArg Except.ok ((show SeedTwin (Handoff.fromConsumed _ _ _) (Handoff.fromConsumed _ _ _) from
          ⟨twin,rfl,rfl⟩).complete _ _ _)

abbrev Strategy := List (Except String Json) → Nat → Input

def adaptive {plan : Plan} (window : Continuation.Window plan) (cut : Nat) (strategy : Strategy) : Nat → List (Except String Json)
  | 0 => []
  | n+1 => let past := adaptive window cut strategy n
    past ++ [response window cut (strategy past n)]

/-- A strategy observes every success field, failure detail and visible metadata before choosing again. -/
theorem every_adaptive_finite_prefix_has_identical_complete_output
    {lp rp : Plan} {left : Continuation.Window lp} {right : Continuation.Window rp}
    (same : WindowTwin left right) (cut : Nat) (strategy : Strategy) (count : Nat) :
    adaptive left cut strategy count = adaptive right cut strategy count := by
  induction count with
  | zero => rfl
  | succ n ih => simp only [adaptive,ih,same.response]

/-- Parsing/authentication metadata are fixed input functions, not hidden history-dependent advice. -/
def withEnvelope {plan : Plan} (window : Continuation.Window plan) (cut : Nat)
    (decode : Json → Except String Input) (metadata : Json → Json) (raw : Json) : Except String Json := do
  let parsed ← decode raw
  let answer ← response window cut parsed
  return Json.mkObj [("metadata",metadata raw),("native",answer)]

theorem WindowTwin.envelope {lp rp : Plan} {left : Continuation.Window lp} {right : Continuation.Window rp}
    (same : WindowTwin left right) (cut : Nat) (decode : Json → Except String Input)
    (metadata : Json → Json) (raw : Json) :
    withEnvelope left cut decode metadata raw = withEnvelope right cut decode metadata raw := by
  unfold withEnvelope
  cases decode raw with
  | error error => rfl
  | ok input => simp only [same.response]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
