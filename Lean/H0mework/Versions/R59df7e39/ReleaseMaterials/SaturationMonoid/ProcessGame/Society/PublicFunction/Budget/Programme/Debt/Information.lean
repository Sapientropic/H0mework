import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Review

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

structure View where
  point : Cursor code
  origin : Origin point

variable (views : List (View (code := code))) (template : Template (code := code))
  (site : Fin code.sites) (signal : Fin code.signals)

abbrev observation (view : View (code := code)) (site : Fin code.sites) :=
  (seed view.point).frame.inbox site

def fiber := views.filter (fun view => observation view site == signal)

theorem mem_fiber (view : View (code := code)) :
    view ∈ fiber views site signal ↔ view ∈ views ∧ observation view site = signal := by
  simp [fiber]

abbrev desired (view : View (code := code)) := word view.point view.origin template

inductive Answer where
  | absent (empty : fiber views site signal = [])
  | ready (value : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
      (witness : View (code := code)) (actual : witness ∈ fiber views site signal)
      (exact : desired template witness = value)
      (uniform : ∀ other ∈ fiber views site signal,desired template other = value)
  | ambiguous (first second : View (code := code))
      (firstActual : first ∈ fiber views site signal)
      (secondActual : second ∈ fiber views site signal)
      (different : desired template second ≠ desired template first)

def generate : Answer views template site signal :=
  match selected : fiber views site signal with
  | [] => .absent selected
  | first :: rest =>
    match inspect (fun other => desired template other = desired template first) rest with
    | .accepted uniform => .ready (desired template first) first
        (by rw [selected];exact List.mem_cons_self) rfl (by
          intro other member
          rw [selected] at member
          rcases List.mem_cons.mp member with same | later
          · exact same ▸ rfl
          · exact uniform other later)
    | .rejected other member different => .ambiguous first other
        (by rw [selected];exact List.mem_cons_self)
        (by rw [selected];exact List.mem_cons_of_mem _ member) different

def work : RawEvent Party Good Port (Mandate.State Party Technology) Instrument :=
  match generate views template site signal with
  | .ready value _ _ _ _ => value
  | .absent _ | .ambiguous _ _ _ _ _ => []

theorem an_ambiguity_has_two_actual_indistinguishable_native_origins
    (first second : View (code := code))
    (firstActual : first ∈ fiber views site signal) (secondActual : second ∈ fiber views site signal)
    (different : desired template second ≠ desired template first) :
    first ∈ views ∧ second ∈ views ∧ observation first site = observation second site ∧
      desired template second ≠ desired template first := by
  have left := (mem_fiber views site signal first).mp firstActual
  have right := (mem_fiber views site signal second).mp secondActual
  exact ⟨left.1,right.1,left.2.trans right.2.symm,different⟩

theorem no_local_rule_can_reproduce_both_conflicting_original_words
    (first second : View (code := code))
    (same : observation first site = observation second site)
    (different : desired template second ≠ desired template first)
    (rule : Fin code.signals → RawEvent Party Good Port (Mandate.State Party Technology) Instrument) :
    ¬ (rule (observation first site) = desired template first ∧
      rule (observation second site) = desired template second) := by
  rintro ⟨left,right⟩
  exact different (right.symm.trans ((congrArg rule same).symm.trans left))

def table : Vector (RawEvent Party Good Port (Mandate.State Party Technology) Instrument) code.signals :=
  Vector.ofFn (work views template site)

def policy : code.Policy :=
  let prepared := table views template site
  fun key _ => if key.1 = site then prepared.get key.2 else []

theorem policy_at (record : Fin code.signals) :
    policy views template site (site,record) (code.key_mem _) = work views template site record := by
  simp only [policy,table,Vector.get,Vector.ofFn,if_pos rfl,Array.getElem_ofFn]
  apply congrArg (work views template site)
  exact Fin.ext rfl

theorem actual_work_reads_only_the_workers_received_record (first second : View (code := code))
    (same : observation first site = observation second site) :
    code.action (policy views template site) site (observation first site) =
      code.action (policy views template site) site (observation second site) := by rw [same]

inductive Recovery (actual : View (code := code)) where
  | resolved (correct : work views template site (observation actual site) = desired template actual)
  | uncertain (other : View (code := code)) (generated : other ∈ views)
      (indistinguishable : observation other site = observation actual site)
      (different : desired template other ≠ desired template actual)
      (noAttempt : work views template site (observation actual site) = [])

def recover (actual : View (code := code)) (generated : actual ∈ views) :
    Recovery views template site actual := by
  have member : actual ∈ fiber views site (observation actual site) :=
    (mem_fiber _ _ _ _).mpr ⟨generated,rfl⟩
  cases report : generate views template site (observation actual site) with
  | absent empty => exact False.elim (by rw [empty] at member;exact List.not_mem_nil member)
  | ready value witness present exact uniform =>
    exact .resolved ((show work views template site (observation actual site) = value by
      simp only [work,report]).trans (uniform actual member).symm)
  | ambiguous first second left right different =>
    have skip : work views template site (observation actual site) = [] := by simp only [work,report]
    if same : desired template actual = desired template first then
      exact .uncertain second ((mem_fiber _ _ _ _).mp right).1
        ((mem_fiber _ _ _ _).mp right).2 (fun equal => different (equal.trans same)) skip
    else
      exact .uncertain first ((mem_fiber _ _ _ _).mp left).1
        ((mem_fiber _ _ _ _).mp left).2 (Ne.symm same) skip

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) (budget : Nat)

def ofWorld (world : Distributed.Recall.Information.World model budget) :
    View (code := model.source.code) :=
  ⟨Continuation.ofWorld model budget world,⟨(world.source model budget).history.length+2,by
    change (world.source model budget).history.length+2 <
      (world.source model budget).history.length+2+world.phase.val+1
    omega⟩⟩

def completeViews := (Distributed.Recall.Information.worlds model budget).map (ofWorld model budget)

theorem every_source_generated_world_is_in_the_information_domain
    (world : Distributed.Recall.Information.World model budget) :
    ofWorld model budget world ∈ completeViews model budget :=
  List.mem_map.mpr ⟨world,Distributed.Recall.Information.every_world_is_generated model budget world,rfl⟩

def recoverWorld (template : Template (code := model.source.code)) (site : Fin model.source.code.sites)
    (world : Distributed.Recall.Information.World model budget) :=
  recover (completeViews model budget) template site (ofWorld model budget world)
    (every_source_generated_world_is_in_the_information_domain model budget world)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information
