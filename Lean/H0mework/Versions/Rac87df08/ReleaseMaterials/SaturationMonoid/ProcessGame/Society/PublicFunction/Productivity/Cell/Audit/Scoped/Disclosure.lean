import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Continuation
import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Origin
import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure.Disclosure

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped
open Institutions.Capitalism.Universal.Source.Program

abbrev Access := BoundedDisclosure.Access

def actualQueries (word : List Action) : List (Party × Query) :=
  word.filterMap fun request => request.purpose.query.map (request.signer,·)

theorem query_of_paid_or_blocked_read (before : AuditCurrent) (actor : Party) (query : Query) :
    actualQueries (readWord before actor query) = [(actor,query)] := by
  unfold readWord
  dsimp only
  split <;> rfl

def querySchedule (queries : Nat → Query) (round : Nat) : List (Party × Query) :=
  let phase := round - initial.round
  match phase with
  | 1 | 2 | 3 => []
  | 4 => [(1,queries phase)]
  | 5 => []
  | 6 => [(1,queries phase)]
  | 7 | 8 => [(2,queries phase)]
  | 9 => []
  | _ => if 10 ≤ phase then [(2,queries phase)] else []

theorem query_schedule_is_the_actual_word (queries : Nat → Query) (larger : Bool) (before : AuditCurrent) :
    actualQueries (emit queries larger before) = querySchedule queries before.round := by
  unfold emit querySchedule
  dsimp only
  split
  all_goals simp_all only [query_of_paid_or_blocked_read]
  all_goals first | rfl | (split <;> try simp_all only [query_of_paid_or_blocked_read])
  all_goals rfl

def decision (view : PublicView) (actor : Party) : Access :=
  BoundedDisclosure.accessDecision ⟨view.permission,view.clock,view.labor0,view.labor1,view.labor2⟩ actor

structure Record where
  cut : Nat
  actor : Party
  query : Query
  access : Access
  version : Nat
  clock : ℚ
  laborCost : ℚ
  evidence : List (Slot × Evidence)
  deriving DecidableEq

def serve (view : PublicView) (cut : Nat) (actor : Party) (query : Query) : Record :=
  let accepted := decision view actor
  ⟨cut,actor,query,accepted,view.permission.version,view.clock,
    if accepted = .admitted then 2 else 0,
    if accepted = .admitted then (selected query).map (fun slot => (slot,restrict (fields query) (originalEvidence slot))) else []⟩

def laborTotal (view : PublicView) : ℚ := view.labor0 + view.labor1 + view.labor2 + view.labor3

def accountedServe (before after : PublicView) (cut actor : Nat) (query : Query) : Record :=
  { serve before cut actor query with laborCost := laborTotal before - laborTotal after }

def journal (queries : Nat → Query) (larger : Bool) : Nat → List Record
  | 0 => []
  | n + 1 => journal queries larger n ++
      (actualQueries (emit queries larger (current queries larger n))).map
        (fun (actor,query) => accountedServe (permittedView (current queries larger n))
          (permittedView (current queries larger (n + 1))) n actor query)

theorem every_query_has_the_same_public_source (queries : Nat → Query) (ordinal : Nat) :
    actualQueries (emit queries false (current queries false ordinal)) =
      actualQueries (emit queries true (current queries true ordinal)) := by
  rw [query_schedule_is_the_actual_word,query_schedule_is_the_actual_word]
  exact congrArg (querySchedule queries)
    (congrArg PublicView.round (every_current_has_the_same_permitted_view queries ordinal))

theorem every_finite_prefix_has_identical_cumulative_disclosure (queries : Nat → Query) (count : Nat) :
    journal queries false count = journal queries true count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [journal,ih,every_query_has_the_same_public_source queries count,
        every_current_has_the_same_permitted_view queries count,
        every_current_has_the_same_permitted_view queries (count + 1)]

theorem every_released_slice_has_its_original_source (view : PublicView) (cut actor : Nat) (query : Query)
    (slot : Slot) (evidence : Evidence) (released : (slot,evidence) ∈ (serve view cut actor query).evidence) :
    Origin slot evidence := by
  unfold serve at released
  dsimp only at released
  split at released
  · obtain ⟨original,_selected,equal⟩ := List.mem_map.mp released
    rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
    exact restrict_has_origin _ _ _ (original_evidence_has_origin _)
  · cases released

theorem trace_acceptance_is_the_original_whole_slot (view : PublicView) (cut actor : Nat) (query : Query)
    (slot : Slot) (evidence : Evidence) (released : (slot,evidence) ∈ (serve view cut actor query).evidence)
    (accepted : traceCheck slot evidence = .verified) : source.ActualSlotPaid 1 (originalIndex slot) :=
  trace_verifies_original _ _ (every_released_slice_has_its_original_source view cut actor query slot evidence released) accepted

theorem lifecycle_acceptance_is_the_original_whole_slot (view : PublicView) (cut actor : Nat) (query : Query)
    (slot : Slot) (evidence : Evidence) (released : (slot,evidence) ∈ (serve view cut actor query).evidence)
    (accepted : lifecycleCheck slot evidence = .verified) : source.ActualSlotPaid 1 (originalIndex slot) :=
  lifecycle_verifies_original _ _ (every_released_slice_has_its_original_source view cut actor query slot evidence released) accepted

def fastCurrent (_queries : Nat → Query) (larger : Bool) (ordinal : Nat) : AuditCurrent :=
  if ordinal < 14 then current defaultQuery larger ordinal
  else shift (current defaultQuery larger 14) (ordinal - 14)

theorem fast_current_is_the_original_source_current (queries : Nat → Query) (larger : Bool) (ordinal : Nat) :
    fastCurrent queries larger ordinal = current queries larger ordinal := by
  rw [query_masks_do_not_change_material_history queries defaultQuery larger]
  unfold fastCurrent
  split
  · rfl
  · have same : ordinal = 14 + (ordinal - 14) := by omega
    conv_rhs => rw [same,exhausted_history_is_its_own_continuing_tail]

def recordsAt (queries : Nat → Query) (larger : Bool) (cut : Nat) : List Record :=
  let before := fastCurrent queries larger cut
  (actualQueries (emit queries larger before)).map (fun (actor,query) =>
    accountedServe (permittedView before) (permittedView (fastCurrent queries larger (cut + 1))) cut actor query)

theorem records_are_the_actual_journal_extension (queries : Nat → Query) (larger : Bool) (cut : Nat) :
    journal queries larger (cut + 1) = journal queries larger cut ++ recordsAt queries larger cut := by
  simp only [journal,recordsAt,fast_current_is_the_original_source_current]

theorem records_have_identical_public_disclosure (queries : Nat → Query) (cut : Nat) :
    recordsAt queries false cut = recordsAt queries true cut := by
  simp only [recordsAt,fast_current_is_the_original_source_current,
    every_query_has_the_same_public_source queries cut,
    every_current_has_the_same_permitted_view queries cut,
    every_current_has_the_same_permitted_view queries (cut + 1)]

/-- The strategy receives only the pooled disclosed records. -/
abbrev Strategy := List Record → Nat → Query

def adaptive (strategy : Strategy) (larger : Bool) : Nat → List Record × List (Nat × Query)
  | 0 => ([],[])
  | n + 1 =>
    let past := adaptive strategy larger n
    let received := past.2 ++ [(n,strategy past.1 n)]
    let queries := fun cut => ((received.find? (fun item => item.1 = cut)).map Prod.snd).getD (defaultQuery cut)
    (past.1 ++ recordsAt queries larger n,received)

theorem every_adaptive_finite_prefix_has_identical_cumulative_disclosure
    (strategy : Strategy) (count : Nat) : adaptive strategy false count = adaptive strategy true count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [adaptive,ih,records_have_identical_public_disclosure]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped
