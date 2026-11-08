import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ServiceActorConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeliveryControlTree
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def deliveryOnly (event : Event Party Good Port (Mandate.State Party Technology) Instrument code.sites) : Bool :=
  match event with | .deliver _ => true | _ => false

-- The external interface owns the menu. Registered addresses may be replayed;
-- packet existence, ownership, payment and actual effects remain original checks.
def menu (code : Code Party Good Port (Mandate.State Party Technology) Instrument) : List (Move code) :=
  none :: (code.eventAlphabet.attach.filter (fun event => deliveryOnly event.val)).map some

structure Command (code : Code Party Good Port (Mandate.State Party Technology) Instrument) where
  attempt : Move code
  admitted : attempt ∈ menu code

abbrev Stages (code : Code Party Good Port (Mandate.State Party Technology) Instrument) :=
  List (EventHistory.Stage (code := code))

def advance (past : Stages code) (attempt : Move code) : Stages code :=
  past ++ [(SilentWindow.quiet,EventStep.fixed attempt)]

def branches (count : Nat) (past : Stages code) : List (Stages code) :=
  Nat.rec (motive := fun _ => Stages code → List (Stages code)) (fun initial => [initial])
    (fun _ recur initial => (menu code).flatMap fun attempt => recur (advance initial attempt)) count past

def run (choose : Nat → Stages code → Command code) (count index : Nat) (past : Stages code) : Stages code :=
  Nat.rec (motive := fun _ => Nat → Stages code → Stages code) (fun _ initial => initial)
    (fun _ recur position initial => recur (position+1) (advance initial (choose position initial).attempt)) count index past

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_adaptive_source_choice_is_in_the_generated_tree
    (choose : Nat → Stages code → Command code) (count index : Nat) (past : Stages code) :
    run choose count index past ∈ branches count past := by
  induction count generalizing index past with
  | zero => exact List.mem_singleton.mpr rfl
  | succ count ih =>
    exact List.mem_flatMap.mpr ⟨(choose index past).attempt,(choose index past).admitted,ih _ _⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_generated_branch_is_an_actual_extension (count : Nat) (past result : Stages code)
    (member : result ∈ branches count past) : past <+: result ∧ result.length = past.length + count := by
  induction count generalizing past with
  | zero => cases List.mem_singleton.mp member; exact ⟨List.prefix_refl _,by omega⟩
  | succ count ih =>
    obtain ⟨attempt,_,inside⟩ := List.mem_flatMap.mp member
    obtain ⟨ordered,length⟩ := ih _ inside
    refine ⟨(List.prefix_append _ _).trans ordered,?_⟩
    simp only [advance,List.length_append,List.length_singleton] at length
    omega

theorem every_generated_branch_spends_its_actual_physical_length
    (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (start : Cursor model.source.code) (count : Nat) (past result : Stages model.source.code)
    (member : result ∈ branches count past) :
    JointResponse.fuel model start result = JointResponse.fuel model start past - count := by
  obtain ⟨⟨tail,same⟩,length⟩ := every_generated_branch_is_an_actual_extension count past result member
  have size : tail.length = count := by rw [← same,List.length_append] at length; omega
  rw [← same]
  exact (UnifiedResponse.fuel_after_actual_extension model start past tail).trans (by rw [size])

omit [DecidableEq Port] [DecidableEq Technology] in
theorem admitted_attempts_are_wait_or_registered_delivery (command : Command code) :
    command.attempt = none ∨ ∃ event : Choice code, command.attempt = some event ∧
      ∃ serial, event.val = .deliver serial := by
  rcases List.mem_cons.mp command.admitted with empty | present
  · exact Or.inl empty
  · obtain ⟨event,inside,same⟩ := List.mem_map.mp present
    have kind := (List.mem_filter.mp inside).2
    refine Or.inr ⟨event,same.symm,?_⟩
    rcases event with ⟨event,registered⟩
    cases event <;> simp_all [deliveryOnly]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeliveryControlTree
