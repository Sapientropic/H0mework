import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Packets

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root Lean

open Continuation in
def scopeJson {plan : Plan} (window : Window plan) : Json := Json.mkObj
  [("unit",toJson ("energy" : String)),("earliest",toJson (toString window.task.earliest)),
   ("deadline",toJson (toString window.task.deadline)),("slots",toJson window.task.slots.length),
   ("revisionEnergy",toJson ("1" : String)),("oldDeadline",toJson (toString auditTask.deadline))]

theorem WindowTwin.task {lp rp : Plan} {left : Continuation.Window lp} {right : Continuation.Window rp}
    (same : WindowTwin left right) : left.task = right.task := congrArg (fun scope => scope.task) same.scope

theorem WindowTwin.scopeJson {lp rp : Plan} {left : Continuation.Window lp} {right : Continuation.Window rp}
    (same : WindowTwin left right) : scopeJson left = scopeJson right := by
  simp only [Privacy.scopeJson,same.task]

def windowWord {plan : Plan} (window : Continuation.Window plan) (requests : List Continuation.Request) (n : Nat) :=
  if n = 0 then [] else window.emit requests (window.current requests n)

theorem WindowTwin.word {lp rp : Plan} {left : Continuation.Window lp} {right : Continuation.Window rp}
    (same : WindowTwin left right) (requests : List Continuation.Request) (n : Nat) :
    windowWord left requests n = windowWord right requests n := by
  unfold windowWord
  split
  · rfl
  · rw [left.emission_uses_exact_request,right.emission_uses_exact_request]
    exact (same.current requests n).window_word left right same.scope same.candidate _

theorem windowWord_energy {plan : Plan} (window : Continuation.Window plan)
    (requests : List Continuation.Request) (n : Nat) : ∀ action ∈ windowWord window requests n,EnergyAction action := by
  unfold windowWord
  split
  · simp
  · rw [window.emission_uses_exact_request]
    exact window_word_energy _ _ _

def windowPackets {plan : Plan} (window : Continuation.Window plan) (requests : List Continuation.Request) (n : Nat) :=
  packets window.scope plan.candidate (window.requestAt requests n).query
    (window.law.rawItems (window.current requests n) (windowWord window requests n))

def windowStage {plan : Plan} (window : Continuation.Window plan) (requests : List Continuation.Request) (n : Nat) :=
  stageJson window.scope n (window.current requests n) (windowWord window requests n)

theorem WindowTwin.packets {lp rp : Plan} {left : Continuation.Window lp} {right : Continuation.Window rp}
    (same : WindowTwin left right) (requests : List Continuation.Request) (n : Nat) :
    windowPackets left requests n = windowPackets right requests n := by
  unfold windowPackets
  change Privacy.packets left.scope lp.candidate _ ((law left.scope).rawItems _ _) =
    Privacy.packets right.scope rp.candidate _ ((law right.scope).rawItems _ _)
  rw [← same.scope,← same.candidate,← same.word requests n]
  exact (same.current requests n).packets _ rfl _ (windowWord_energy _ _ _) _ _

theorem WindowTwin.stage {lp rp : Plan} {left : Continuation.Window lp} {right : Continuation.Window rp}
    (same : WindowTwin left right) (requests : List Continuation.Request) (n : Nat) :
    windowStage left requests n = windowStage right requests n := by
  unfold windowStage
  rw [← same.scope,← same.word requests n]
  exact (same.current requests n).stage _ rfl _ (windowWord_energy _ _ _) n

def nextScopeJson {plan : Plan} (window : Continuation.Window plan) (requests : List Continuation.Request) (n : Nat) : Json :=
  match window.nextWindow requests n with | none => .null | some next => scopeJson next

theorem WindowTwin.nextScope {lp rp : Plan} {left : Continuation.Window lp} {right : Continuation.Window rp}
    (same : WindowTwin left right) (requests : List Continuation.Request) (n : Nat) :
    nextScopeJson left requests n = nextScopeJson right requests n := by
  have mapped : ∀ {l : Option (Continuation.Window lp)} {r : Option (Continuation.Window rp)},
      Option.Rel WindowTwin l r → (match l with | none => Json.null | some w => Privacy.scopeJson w) =
        (match r with | none => Json.null | some w => Privacy.scopeJson w) := by
    intro l r related
    cases related with
    | none => rfl
    | some twin => exact twin.scopeJson
  exact mapped (same.nextWindow requests n)

/-- Full continuation return, including the original bootstrap/stage convention and all errors' reasons. -/
def continuationJson {plan : Plan} (window : Continuation.Window plan)
    (requests : List Continuation.Request) (n phase nextCut : Nat) : Json :=
  let before := window.current requests n
  let after := window.current requests (n+1)
  let packetList := windowPackets window requests n
  let visits := if n = 1 then [0,n] else [n]
  let reason := if (window.requestAt requests n).command = .openWindow then
    if (window.nextWindow requests n).isSome then "OPENED" else if ¬Quiet before then "ACTIVE_MANDATE"
    else if before.clock ≤ window.task.deadline then "WINDOW_ACTIVE" else "UNPAID_APPLICATION"
    else if packetList.isEmpty then "NO_PAID_DELIVERY" else "DELIVERED"
  Json.mkObj [("scope",scopeJson window),("ordinal",toJson n),("phase",toJson phase),
    ("before",snapshot before),("next",snapshot after),
    ("rows",toJson ((window.law.rawItems before (windowWord window requests n)).map (rowJson window.scope))),
    ("packets",toJson packetList),("stages",toJson (visits.map (windowStage window requests))),
    ("nextScope",nextScopeJson window requests n),("reason",toJson reason),("nextCut",toJson nextCut)]

theorem WindowTwin.complete {lp rp : Plan} {left : Continuation.Window lp} {right : Continuation.Window rp}
    (same : WindowTwin left right) (requests : List Continuation.Request) (n phase nextCut : Nat) :
    continuationJson left requests n phase nextCut = continuationJson right requests n phase nextCut := by
  have twin := same.current requests n
  have rows : (left.law.rawItems (left.current requests n) (windowWord left requests n)).map (rowJson left.scope) =
      (right.law.rawItems (right.current requests n) (windowWord right requests n)).map (rowJson right.scope) := by
    change ((law left.scope).rawItems _ _).map _ = ((law right.scope).rawItems _ _).map _
    rw [← same.scope,← same.word requests n]
    exact twin.rows _ rfl _ (windowWord_energy _ _ _)
  have nextSome : (left.nextWindow requests n).isSome = (right.nextWindow requests n).isSome := by
    have mapped : ∀ {l : Option (Continuation.Window lp)} {r : Option (Continuation.Window rp)},
        Option.Rel WindowTwin l r → l.isSome = r.isSome := by
      intro l r related
      cases related <;> rfl
    exact mapped (same.nextWindow requests n)
  have stages : ∀ visits : List Nat,visits.map (windowStage left requests) = visits.map (windowStage right requests) := by
    intro visits
    apply List.map_congr_left
    intro visit _
    exact same.stage requests visit
  simp only [continuationJson,same.scopeJson,twin.snapshot,(same.current requests (n+1)).snapshot,
    rows,same.packets requests n,stages,same.nextScope requests n,nextSome,Quiet,twin.technology,twin.clock,same.task,
    Continuation.Window.requestAt]
  rfl

theorem SeedTwin.scope {lp rp : Plan} {left : Handoff.Seed lp} {right : Handoff.Seed rp}
    (same : SeedTwin left right) : left.scope = right.scope := same.window.scope

theorem SeedTwin.requestAt {lp rp : Plan} {left : Handoff.Seed lp} {right : Handoff.Seed rp}
    (same : SeedTwin left right) (requests : List Handoff.Request) (n : Nat) :
    left.requestAt requests n = right.requestAt requests n := by
  simp only [Handoff.Seed.requestAt,same.ordinal,same.window.candidate]

theorem SeedTwin.emit {lp rp : Plan} {left : Handoff.Seed lp} {right : Handoff.Seed rp}
    (same : SeedTwin left right) (requests : List Handoff.Request) (n : Nat) :
    left.emit requests (left.current requests n) = right.emit requests (right.current requests n) := by
  have twin := same.current requests n
  simp only [Handoff.Seed.emit,twin.round,same.window.initial.round,same.ordinal]
  split
  · simp only [Continuation.Window.emit,twin.round,same.window.initial.round,same.requests]
    exact twin.window_word left.window right.window same.window.scope same.window.candidate _
  · rw [same.requestAt]
    exact twin.handoff_word left right same.scope _

def handoffJson {plan : Plan} (seed : Handoff.Seed plan) (requests : List Handoff.Request) (n nextCut : Nat) : Json :=
  let before := seed.current requests n
  let word := seed.emit requests before
  let after := seed.current requests (n+1)
  let active := seed.requestAt requests n
  let actor := seed.requestActor active before
  let candidate := seed.target before
  let packetList := packets seed.scope actor active.query (seed.law.rawItems before word)
  let rows := toJson ((seed.law.rawItems before word).map (rowJson seed.scope))
  let stage := Json.mkObj [("ordinal",toJson n),("before",snapshot before),("rows",rows),("next",snapshot after)]
  let reason := if !packetList.isEmpty then "DELIVERED" else
    if active.replace then if (seed.candidates before).isEmpty then "NO_DISTINCT_MEMBER" else "HANDOFF_BLOCKED"
    else if before.technology.holder ≠ some active.actor then "UNAUTHORIZED"
    else if before.clock < seed.window.task.earliest ∨ seed.window.task.deadline < before.clock then "EXPIRED"
    else "UNFUNDED"
  Json.mkObj [("scope",scopeJson seed.window),("ordinal",toJson n),
    ("before",snapshot before),("next",snapshot after),("rows",rows),
    ("packets",toJson packetList),("stages",toJson [stage]),("nextScope",.null),
    ("candidate",toJson candidate),("actor",toJson actor),("reason",toJson reason),("nextCut",toJson nextCut)]

theorem seed_emit_energy {plan : Plan} (seed : Handoff.Seed plan) (requests : List Handoff.Request) (before : AuditCurrent) :
    ∀ action ∈ seed.emit requests before,EnergyAction action := by
  unfold Handoff.Seed.emit
  dsimp only
  split
  · unfold Continuation.Window.emit
    exact window_word_energy _ _ _
  · exact handoff_word_energy _ _ _

theorem SeedTwin.complete {lp rp : Plan} {left : Handoff.Seed lp} {right : Handoff.Seed rp}
    (same : SeedTwin left right) (requests : List Handoff.Request) (n nextCut : Nat) :
    handoffJson left requests n nextCut = handoffJson right requests n nextCut := by
  have twin := same.current requests n
  have active := same.requestAt requests n
  have candidates : left.candidates (left.current requests n) = right.candidates (right.current requests n) := by
    simp only [Handoff.Seed.candidates,same.scope,twin.technology]
  have target : left.target (left.current requests n) = right.target (right.current requests n) := by
    simp only [Handoff.Seed.target,candidates]
  have actor : left.requestActor (left.requestAt requests n) (left.current requests n) =
      right.requestActor (right.requestAt requests n) (right.current requests n) := by
    simp only [Handoff.Seed.requestActor,active,target]
  have rows : (left.law.rawItems (left.current requests n) (left.emit requests (left.current requests n))).map (rowJson left.scope) =
      (right.law.rawItems (right.current requests n) (right.emit requests (right.current requests n))).map (rowJson right.scope) := by
    change ((law left.scope).rawItems _ _).map _ = ((law right.scope).rawItems _ _).map _
    rw [← same.scope,← same.emit requests n]
    exact twin.rows _ rfl _ (seed_emit_energy _ _ _)
  have packetsEq : packets left.scope (left.requestActor (left.requestAt requests n) (left.current requests n))
      (left.requestAt requests n).query (left.law.rawItems (left.current requests n) (left.emit requests (left.current requests n))) =
      packets right.scope (right.requestActor (right.requestAt requests n) (right.current requests n))
      (right.requestAt requests n).query (right.law.rawItems (right.current requests n) (right.emit requests (right.current requests n))) := by
    change Privacy.packets left.scope _ _ ((law left.scope).rawItems _ _) = packets right.scope _ _ ((law right.scope).rawItems _ _)
    rw [← same.scope,← same.emit requests n,← actor,← active]
    exact twin.packets _ rfl _ (seed_emit_energy _ _ _) _ _
  simp only [handoffJson]
  rw [packetsEq,actor]
  simp only [same.window.scopeJson,twin.snapshot,(same.current requests (n+1)).snapshot,
    rows,target,candidates,active,twin.technology,twin.clock,same.window.task]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
