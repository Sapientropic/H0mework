import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Window
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (request : Request (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev remaining (point : Cursor request.model.source.code) := Cut.horizon point.source point.entry point.cut

theorem execute (point : Cursor request.model.source.code)
    (stages : List (EventHistory.Stage (code := request.model.source.code))) :
    remaining request (EventHistory.execute point stages) = remaining request point - stages.length := by
  induction stages generalizing point with
  | nil => rfl
  | cons stage tail ih =>
      change remaining request (EventHistory.execute (point.after stage.1 stage.2) tail) = _
      rw [ih]
      have moved := Installation.Chain.after_remaining (model := request.model) point stage.1 stage.2
      change remaining request (point.after stage.1 stage.2) = remaining request point - 1 at moved
      rw [moved]
      simp only [List.length_cons,Nat.sub_sub]
      rw [Nat.add_comm]

theorem initial (view : View (code := request.model.source.code)) (inside : view ∈ PublicTask.initial request) :
    remaining request view.point = request.budget := by
  change view ∈ (EventHistory.genesis request.model request.budget).map currentView at inside
  obtain ⟨point,member,rfl⟩ := List.mem_map.mp inside
  change point ∈ (Distributed.Recall.Information.origins request.model).map
    (EventHistory.ofOrigin request.model request.budget) at member
  obtain ⟨origin,_,rfl⟩ := List.mem_map.mp member
  rfl

theorem successors (views : List (View (code := request.model.source.code))) (budget : Nat)
    (uniform : ∀ view ∈ views,remaining request view.point = budget)
    (rule : Prefix.Rule request.model.source.code) :
    ∀ view ∈ Inquiry.successors rule views,remaining request view.point = budget-1 := by
  intro view inside
  obtain ⟨previous,member,inside⟩ := List.mem_flatMap.mp inside
  obtain ⟨table,_,rfl⟩ := List.mem_map.mp inside
  have moved := Installation.Chain.after_remaining (model := request.model) previous.point rule
    (Cut.opponent previous.point.source previous.point.entry previous.point.cut table)
  change remaining request (afterFinite previous rule table).point = remaining request previous.point - 1 at moved
  exact moved.trans (congrArg (fun n => n-1) (uniform previous member))

theorem advance (views : List (View (code := request.model.source.code))) (budget : Nat)
    (uniform : ∀ view ∈ views,remaining request view.point = budget)
    (rules : List (Prefix.Rule request.model.source.code)) :
    ∀ view ∈ advanceViews views rules,remaining request view.point = budget-rules.length := by
  induction rules generalizing views budget with
  | nil => exact uniform
  | cons rule tail ih =>
      intro view inside
      have value := ih _ (budget-1) (successors request views budget uniform rule) view inside
      simpa only [List.length_cons,Nat.sub_sub,Nat.add_comm 1] using value

theorem domain (signal : Fin request.model.source.code.signals) :
    ∀ point ∈ PublicTask.domain request signal,
      remaining request point = request.budget-request.installed.length := by
  intro point inside
  change point ∈ (fiber (PublicTask.views request) request.reader signal).map View.point at inside
  obtain ⟨view,inFiber,rfl⟩ := List.mem_map.mp inside
  have member : view ∈ PublicTask.views request := List.mem_of_mem_filter inFiber
  change view ∈ (advanceViews (PublicTask.initial request) request.installed).map (fun previous => currentView previous.point) at member
  obtain ⟨previous,inViews,rfl⟩ := List.mem_map.mp member
  exact advance request _ request.budget (initial request) request.installed previous inViews

private theorem constant_horizon (points : List (Cursor request.model.source.code)) (budget : Nat)
    (uniform : ∀ point ∈ points,remaining request point = budget) :
    horizon points ≤ budget := by
  induction points with
  | nil => exact Nat.zero_le _
  | cons point rest ih =>
      change max (remaining request point) (horizon rest) ≤ budget
      exact max_le (le_of_eq (uniform point (List.mem_cons_self ..)))
        (ih (fun other inside => uniform other (List.mem_cons_of_mem _ inside)))

theorem actual (origin : Distributed.Recall.Information.Origin request.model)
    (stages : List (EventHistory.Stage (code := request.model.source.code)))
    (installed : stages.map Prod.fst = request.installed) :
    let point := EventHistory.execute (EventHistory.ofOrigin request.model request.budget origin) stages
    horizon (PublicTask.domain request (observation (currentView point) request.reader)) =
      remaining request point := by
  dsimp only
  have current := execute request (EventHistory.ofOrigin request.model request.budget origin) stages
  have lengths := congrArg List.length installed
  simp only [List.length_map] at lengths
  have seed : remaining request (EventHistory.ofOrigin request.model request.budget origin) = request.budget := rfl
  rw [seed,lengths] at current
  have coverage := PublicTask.every_actual_receipt_has_a_complete_local_source request origin stages installed
  obtain ⟨representative,inside,matched⟩ := coverage
  have member : representative.point ∈ PublicTask.domain request _ := List.mem_map.mpr ⟨representative,inside,rfl⟩
  have upper := constant_horizon request
    (PublicTask.domain request (observation (currentView (EventHistory.execute (EventHistory.ofOrigin request.model request.budget origin) stages)) request.reader))
    (request.budget-request.installed.length)
    (domain request (observation (currentView (EventHistory.execute (EventHistory.ofOrigin request.model request.budget origin) stages)) request.reader))
  have lower := Whole.Complete.each_remaining_horizon_is_generated _ _ member
  change remaining request representative.point ≤ _ at lower
  rw [domain request _ _ member] at lower
  exact (Nat.le_antisymm upper lower).trans current.symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Window
