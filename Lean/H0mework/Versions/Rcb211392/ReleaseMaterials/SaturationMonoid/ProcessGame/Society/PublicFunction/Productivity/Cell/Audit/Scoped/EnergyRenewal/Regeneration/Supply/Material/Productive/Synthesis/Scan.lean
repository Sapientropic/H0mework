import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Demand
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Compiler

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

structure Charge where
  payer : Actor
  request : JointAction
  operation : request.operation=.use payer [(.labor,1)] .external

def auditCharge : Charge :=
  ⟨customer,⟨customer,[],.audit (native .common),[],.use customer [(.labor,1)] .external⟩,rfl⟩
def providerCharge : Charge :=
  ⟨supplier,⟨supplier,[],.provider (.reserve 0),[],.use supplier [(.labor,1)] .external⟩,rfl⟩

variable (scope : Scope) (task : PublicTaskSpec Actor Good)
  (alphabet : List JointAction) (budget : Nat) (charge : Charge)

abbrev Candidate := {word : List JointAction // word ∈ words alphabet budget}
abbrev PlanAt (current : Current) := PaidServicePlan (law scope) current task alphabet budget

/-- Old delivery is paid in the generated word, never discarded by a new task. -/
def check (current : Current) (candidate : Candidate alphabet budget) : Option (PlanAt scope task alphabet budget current) :=
  (PaidServicePlan.checkCandidate candidate.val candidate.property).filter fun plan =>
    decide (plan.next.claims .delivery supplier receiver=0)

inductive Scan : Current → List (Candidate alphabet budget) → Type where
  | exhausted (current) : Scan current []
  | unpaid {current candidate rest}
      (refused : ¬ (law scope).Valid current charge.request) : Scan current (candidate::rest)
  | found {current candidate rest}
      (feePaid : (law scope).Valid current charge.request)
      (plan : PlanAt scope task alphabet budget ((law scope).step current charge.request))
      (checked : check scope task alphabet budget ((law scope).step current charge.request) candidate=some plan) :
      Scan current (candidate::rest)
  | skip {current candidate rest}
      (feePaid : (law scope).Valid current charge.request)
      (rejected : check scope task alphabet budget ((law scope).step current charge.request) candidate=none)
      (tail : Scan ((law scope).step current charge.request) rest) : Scan current (candidate::rest)

def search (current : Current) : (candidates : List (Candidate alphabet budget)) →
    Scan scope task alphabet budget charge current candidates
  | [] => .exhausted current
  | candidate::rest =>
    if paid : (law scope).Valid current charge.request then
      match checked : check scope task alphabet budget ((law scope).step current charge.request) candidate with
      | some plan => .found paid plan checked
      | none => .skip paid checked (search ((law scope).step current charge.request) rest)
    else .unpaid paid

def generate (current : Current) := search scope task alphabet budget charge current (words alphabet budget).attach

theorem checked_candidate_keeps_the_original_word_and_pays_delivery (current : Current)
    (candidate : Candidate alphabet budget) (plan : PlanAt scope task alphabet budget current)
    (checked : check scope task alphabet budget current candidate=some plan) :
    plan.word=candidate.val ∧ plan.next.claims .delivery supplier receiver=0 := by
  unfold check at checked
  simp only [Option.filter_eq_some_iff,decide_eq_true_eq] at checked
  exact ⟨PaidServicePlan.checkCandidate_word _ _ plan checked.1,checked.2⟩

namespace Scan
variable {scope task alphabet budget charge} {current : Current} {candidates : List (Candidate alphabet budget)}

private theorem paid_index (initial : Current) (actions : List JointAction) (first second : Nat)
    (paid : ∀ item ∈ ((law scope).execute initial first actions).items,
      (law scope).Valid item.before item.request) :
    ∀ item ∈ ((law scope).execute initial second actions).items,
      (law scope).Valid item.before item.request := by
  induction actions generalizing initial first second with
  | nil => simp [RawLaw.execute]
  | cons head rest ih =>
    intro item member
    simp only [RawLaw.execute,List.mem_cons] at member
    rcases member with rfl | member
    · exact paid ⟨first,initial,head⟩ (by simp [RawLaw.execute])
    · exact ih ((law scope).step initial head) (first+1) (second+1)
        (fun item member => paid item (List.mem_cons_of_mem _ member)) item member

private theorem item_index (initial : Current) (actions : List JointAction) (first second : Nat)
    (item : ExecutionItem Actor Good Port Technology Instrument)
    (member : item ∈ ((law scope).execute initial first actions).items) :
    ∃ other ∈ ((law scope).execute initial second actions).items,
      other.before=item.before ∧ other.request=item.request := by
  induction actions generalizing initial first second with
  | nil => simp [RawLaw.execute] at member
  | cons head rest ih =>
    simp only [RawLaw.execute,List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨⟨second,initial,head⟩,by simp [RawLaw.execute],rfl,rfl⟩
    · obtain ⟨other,inside,before,request⟩ := ih _ _ _ member
      exact ⟨other,List.mem_cons_of_mem _ inside,before,request⟩

private theorem final_index (initial : Current) (actions : List JointAction) (first second : Nat) :
    ((law scope).execute initial first actions).final=((law scope).execute initial second actions).final := by
  induction actions generalizing initial first second with
  | nil => rfl
  | cons head rest ih => exact ih _ _ _

private theorem paid_cons (initial : Current) (actions : List JointAction) (slot : ServiceSlot Actor Good)
    (paid : Institutions.Capitalism.Universal.Exit.Necessity.BundlePaid (law scope)
      ((law scope).step initial charge.request) actions slot.bearer slot.goods slot.purpose) :
    Institutions.Capitalism.Universal.Exit.Necessity.BundlePaid (law scope)
      initial (charge.request::actions) slot.bearer slot.goods slot.purpose := by
  rcases paid with empty | ⟨item,member,valid,matched⟩
  · exact Or.inl empty
  · obtain ⟨other,inside,before,request⟩ := item_index _ actions 0 1 item member
    exact Or.inr ⟨other,List.mem_cons_of_mem _ inside,by simpa [before,request] using valid,
      by simpa [request] using matched⟩

private theorem fee_clock (initial : Current) : ((law scope).step initial charge.request).clock=initial.clock := by
  unfold RawLaw.step
  split <;> rfl

private theorem next_clock (initial : Current) (actions : List JointAction) :
    ((law scope).next initial actions).clock=initial.clock+1 := rfl

def fees : {current : Current} → {candidates : List (Candidate alphabet budget)} →
    Scan scope task alphabet budget charge current candidates → Nat
  | _,_,.exhausted _ | _,_,.unpaid _ => 0
  | _,_,.found .. => 1
  | _,_,.skip _ _ tail => 1+tail.fees

def word : {current : Current} → {candidates : List (Candidate alphabet budget)} →
    Scan scope task alphabet budget charge current candidates → List JointAction
  | _,_,.exhausted _ | _,_,.unpaid _ => []
  | _,_,.found _ plan _ => charge.request::plan.word
  | _,_,.skip _ _ tail => charge.request::tail.word

def succeeded : {current : Current} → {candidates : List (Candidate alphabet budget)} →
    Scan scope task alphabet budget charge current candidates → Bool
  | _,_,.exhausted _ | _,_,.unpaid _ => false
  | _,_,.found .. => true
  | _,_,.skip _ _ tail => tail.succeeded

def planningAfter : {current : Current} → {candidates : List (Candidate alphabet budget)} →
    Scan scope task alphabet budget charge current candidates → Current
  | current,_,.exhausted _ | current,_,.unpaid _ => current
  | current,_,.found .. => (law scope).step current charge.request
  | _,_,.skip _ _ tail => tail.planningAfter

theorem planning_labor_is_really_debited (scan : Scan scope task alphabet budget charge current candidates) :
    scan.planningAfter.stock charge.payer .labor=current.stock charge.payer .labor-scan.fees := by
  have fee_labor (before : Current) (paid : (law scope).Valid before charge.request) :
      ((law scope).step before charge.request).stock charge.payer .labor=before.stock charge.payer .labor-1 := by
    rw [RawLaw.step,if_pos paid]
    simp [RawLaw.paidStep,RawLaw.debit,RawLaw.credit,charge.operation,flowAt,locate,amount]
  induction scan with
  | exhausted _ => simp [planningAfter,fees]
  | unpaid _ => simp [planningAfter,fees]
  | found paid plan checked => simpa only [planningAfter,fees,Nat.cast_one] using fee_labor _ paid
  | skip paid rejected tail ih =>
    simp only [planningAfter,fees,Nat.cast_add,Nat.cast_one,ih,fee_labor _ paid]
    ring

theorem actual_word_is_paid (scan : Scan scope task alphabet budget charge current candidates) (index : Nat := 0) :
    ∀ item ∈ ((law scope).execute current index scan.word).items,(law scope).Valid item.before item.request := by
  induction scan generalizing index with
  | exhausted current => simp [word,RawLaw.execute]
  | unpaid refused => simp [word,RawLaw.execute]
  | found paid plan checked =>
    intro item member
    simp only [word,RawLaw.execute,List.mem_cons] at member
    rcases member with rfl | member
    · exact paid
    · exact paid_index _ _ 0 (index+1) plan.sound.2 item member
  | skip paid rejected tail ih =>
    intro item member
    simp only [word,RawLaw.execute,List.mem_cons] at member
    rcases member with rfl | member
    · exact paid
    · exact ih (index+1) item member

theorem success_pays_new_service (scan : Scan scope task alphabet budget charge current candidates)
    (success : scan.succeeded=true) (slot : ServiceSlot Actor Good) (inside : slot ∈ task.slots) :
    Institutions.Capitalism.Universal.Exit.Necessity.BundlePaid (law scope) current scan.word
      slot.bearer slot.goods slot.purpose := by
  induction scan with
  | exhausted _ => contradiction
  | unpaid _ => contradiction
  | found paid plan checked => exact paid_cons _ _ slot (plan.pointwise_service slot inside)
  | skip paid rejected tail ih => exact paid_cons _ _ slot (ih success)

theorem success_keeps_the_original_window (scan : Scan scope task alphabet budget charge current candidates)
    (success : scan.succeeded=true) :
    task.earliest≤current.clock ∧ ((law scope).next current scan.word).clock≤task.deadline := by
  induction scan with
  | exhausted _ => contradiction
  | unpaid _ => contradiction
  | found paid plan checked =>
    have window := plan.sound.1
    have first := window.1
    have last := window.2.1
    simp only [fee_clock] at first
    change ((law scope).next _ plan.word).clock≤task.deadline at last
    simp only [next_clock,fee_clock] at last
    exact ⟨first,by simpa only [next_clock] using last⟩
  | skip paid rejected tail ih =>
    have window := ih success
    simpa only [next_clock,fee_clock] using window

theorem word_preserves_old_instruments (scan : Scan scope task alphabet budget charge current candidates)
    (supported : ∀ action ∈ alphabet,Historical action) : ∀ action ∈ scan.word,Historical action := by
  induction scan with
  | exhausted _ => simp [word]
  | unpaid _ => simp [word]
  | found paid plan checked =>
    intro action member
    rcases List.mem_cons.mp member with rfl | member
    · simp [Historical,charge.operation]
    · exact supported action (((mem_words_iff _ _ _).mp plan.generated).2 action member)
  | skip paid rejected tail ih =>
    intro action member
    rcases List.mem_cons.mp member with rfl | member
    · simp [Historical,charge.operation]
    · exact ih action member

theorem success_really_settles_old_delivery (scan : Scan scope task alphabet budget charge current candidates)
    (success : scan.succeeded=true) :
    ((law scope).next current scan.word).claims .delivery supplier receiver=0 := by
  induction scan with
  | exhausted _ => contradiction
  | unpaid _ => contradiction
  | found paid plan checked =>
    have debt := (checked_candidate_keeps_the_original_word_and_pays_delivery _ _ _ _ _ _ _ checked).2
    change ((law scope).execute _ 1 plan.word).final.claims .delivery supplier receiver=0
    rw [final_index _ _ 1 0]
    exact debt
  | skip paid rejected tail ih =>
    change ((law scope).execute _ 1 tail.word).final.claims .delivery supplier receiver=0
    rw [final_index _ _ 1 0]
    exact ih success

theorem charges_are_an_actual_prefix (scan : Scan scope task alphabet budget charge current candidates) :
    ∃ work,scan.word=List.replicate scan.fees charge.request++work := by
  induction scan with
  | exhausted _ => exact ⟨[],rfl⟩
  | unpaid _ => exact ⟨[],rfl⟩
  | found paid plan checked => exact ⟨plan.word,rfl⟩
  | skip paid rejected tail ih =>
    obtain ⟨work,equal⟩ := ih
    exact ⟨work,by simp only [word,fees,equal,Nat.add_comm 1,List.replicate_succ,List.cons_append]⟩

theorem planning_after_is_the_actual_prefix (scan : Scan scope task alphabet budget charge current candidates)
    (index : Nat := 0) :
    ((law scope).execute current index (List.replicate scan.fees charge.request)).final=scan.planningAfter := by
  induction scan generalizing index with
  | exhausted _ => rfl
  | unpaid _ => rfl
  | found paid plan checked => rfl
  | skip paid rejected tail ih =>
    simp only [fees,Nat.add_comm 1,List.replicate_succ,RawLaw.execute,planningAfter]
    exact ih (index+1)

end Scan

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis
