import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Accounting

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Exposure

open ResponsibilityLifecycle
open LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

abbrev Window := (index : Index) ×
  RootVisit (ProgrammeLiving.livingRoot (sources index)).toAuthoritativeRoot.toRoot

def windowOf (claim : Claim sources) : Window sources := ⟨claim.1, claim.2.origin.visit⟩

/-- Each admission carries its actual prefix and its own postbirth suffix.
This lets the original slot follower consume debts born inside the run. -/
structure Birth {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) where
  private mk ::
  before : ResponsibilityState (vocabulary sources)
  priorRun : (process sources).Run first before
  claim : Claim sources
  suffix : (process sources).Run
    (NativeResponsibilityProcess.Edge.admit (P := process sources) claim : (process sources).Edge before).target last
  exact_events : run.events = priorRun.events ++
    [(NativeResponsibilityProcess.Edge.admit (P := process sources) claim : (process sources).Edge before).lifecycleEvent] ++ suffix.events

namespace Birth

variable {sources} {first last : ResponsibilityState (vocabulary sources)}
  {run : (process sources).Run first last}

def index (birth : Birth sources run) : Nat := birth.before.slots.length

def address (birth : Birth sources run) : Nat × Claim sources := ⟨birth.index, birth.claim⟩

def extend (birth : Birth sources run) (edge : (process sources).Edge last) :
    Birth sources (.step run edge) where
  before := birth.before
  priorRun := birth.priorRun
  claim := birth.claim
  suffix := .step birth.suffix edge
  exact_events := by
    rw [NativeResponsibilityProcess.Run.events, birth.exact_events]
    simp only [NativeResponsibilityProcess.Run.events, List.append_assoc]

def fresh (prior : (process sources).Run first last) (claim : Claim sources) :
    Birth sources (.step prior (.admit claim)) where
  before := last
  priorRun := prior
  claim := claim
  suffix := .nil
  exact_events := by simp only [NativeResponsibilityProcess.Run.events, List.append_nil]

def follow (birth : Birth sources run) :
    Migration.Follow sources birth.suffix birth.index (.live (admission sources birth.claim).toObligation) :=
  Migration.follow sources birth.suffix birth.index _
    (NativeResponsibilityProcess.admit_target_slot (P := process sources) birth.claim)

def remaining (birth : Birth sources run) : ℚ := principal sources birth.follow.slot

def paid (birth : Birth sources run) : ℚ := birth.follow.path.paid sources

theorem conservation (birth : Birth sources run) :
    birth.remaining + birth.paid = birth.claim.2.quantity := by
  have balance := birth.follow.path.conservation sources
  change principal sources birth.follow.slot + birth.follow.path.paid sources =
    Financial.total (sources birth.claim.1) (initialBalance (sources birth.claim.1) birth.claim.2) at balance
  simpa only [remaining, paid, Financial.initial_total] using balance

theorem actual_slot (birth : Birth sources run) :
    last.slots[birth.index]? = some birth.follow.slot := birth.follow.present

theorem original_claim (birth : Birth sources run) :
    slotClaim sources birth.follow.slot = birth.claim := birth.follow.path.preserves_claim sources

theorem payment_records (birth : Birth sources run) :
    birth.paid = ((birth.suffix.events.filter (fun event => event.slot == birth.index)).map
      (fun event => retired sources (sourceEvent sources event))).sum :=
  birth.follow.payment_is_exactly_the_actual_slot_records sources

def unit (birth : Birth sources run) : Good :=
  (sources birth.claim.1).law.settlementUnit birth.claim.2.instrument

def rate (birth : Birth sources run) : ℚ :=
  (sources birth.claim.1).law.settlementRate birth.claim.2.instrument

theorem settlement_quote_conservation (birth : Birth sources run) :
    birth.remaining * birth.rate + birth.paid * birth.rate = birth.claim.2.quantity * birth.rate := by
  rw [← add_mul, birth.conservation]

end Birth

def admissions {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) : List (Birth sources run) :=
  match run with
  | .nil => []
  | .step prior edge =>
      (admissions prior).map (fun birth => birth.extend edge) ++
        match edge with
        | .admit claim => [Birth.fresh prior claim]
        | .cross .. => []
        | .reopen _ _ _ impossible => impossible.elim

def admittedAddress (event : LifecycleEvent (vocabulary sources)) : Option (Nat × Claim sources) :=
  match event with
  | .admitted index payload => some ⟨index, payload.content⟩
  | _ => none

theorem admissions_exact {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) :
    (admissions sources run).map Birth.address = run.events.filterMap (admittedAddress sources) := by
  induction run with
  | nil => rfl
  | @step middle prior edge ih =>
      cases edge with
      | admit claim =>
          change ((admissions sources prior).map (fun birth => birth.extend (.admit claim)) ++
            [Birth.fresh prior claim]).map Birth.address = _
          rw [List.map_append, List.map_map]
          change (admissions sources prior).map Birth.address ++ ([(middle.slots.length, claim)] : List (Nat × Claim sources)) =
            (prior.events ++ [LifecycleEvent.admitted middle.slots.length (admission sources claim)]).filterMap (admittedAddress sources)
          rw [ih, List.filterMap_append]
          rfl
      | cross changed obligation present boundary =>
          change ((admissions sources prior).map (fun birth : Birth sources prior => birth.extend (.cross changed obligation present boundary)) ++
            []).map Birth.address = _
          rw [List.append_nil, List.map_map]
          change (admissions sources prior).map Birth.address =
            (prior.events ++ [(NativeResponsibilityProcess.Edge.cross (P := process sources)
              changed obligation present boundary).lifecycleEvent]).filterMap (admittedAddress sources)
          rw [ih, List.filterMap_append, cross_record sources changed obligation present boundary]
          have notBorn : admittedAddress sources (record sources changed.val boundary) = none := by
            unfold record Boundary.disposition
            split <;> rfl
          simp only [List.filterMap_cons, notBorn, List.filterMap_nil, List.append_nil]
      | reopen _ _ _ impossible => exact impossible.elim

theorem admission_indices {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) :
    List.range first.slots.length ++ (admissions sources run).map Birth.index = List.range last.slots.length := by
  induction run with
  | nil => simp only [admissions, List.map_nil, List.append_nil]
  | @step middle prior edge ih =>
      cases edge with
      | admit claim =>
          have size : (NativeResponsibilityProcess.Edge.admit (P := process sources) claim :
              (process sources).Edge middle).target.slots.length = middle.slots.length + 1 := by
            simp only [NativeResponsibilityProcess.Edge.target, List.length_append,
              List.length_cons, List.length_nil, Nat.zero_add]
          rw [size]
          change List.range first.slots.length ++
            (((admissions sources prior).map (fun birth => birth.extend (.admit claim)) ++
              [Birth.fresh prior claim]).map Birth.index) = _
          rw [List.map_append, List.map_map]
          change List.range first.slots.length ++
            ((admissions sources prior).map Birth.index ++ [middle.slots.length]) = _
          rw [List.range_succ, ← ih, List.append_assoc]
      | cross changed obligation present boundary =>
          have size : (NativeResponsibilityProcess.Edge.cross (P := process sources)
              changed obligation present boundary).target.slots.length = middle.slots.length := List.length_set
          rw [size]
          change List.range first.slots.length ++
            (((admissions sources prior).map (fun birth : Birth sources prior =>
              birth.extend (.cross changed obligation present boundary)) ++ []).map Birth.index) = _
          rw [List.append_nil, List.map_map]
          exact ih
      | reopen _ _ _ impossible => exact impossible.elim

def selected {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (debtor : Party) (unit : Good)
    (window : Window sources → Bool) : List (Birth sources run) :=
  (admissions sources run).filter fun birth =>
    decide (birth.claim.2.debtor = debtor) && decide (birth.unit = unit) && window (windowOf sources birth.claim)

theorem selected_has_the_original_debtor_unit_and_window
    {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (debtor : Party) (unit : Good)
    (window : Window sources → Bool) (birth : Birth sources run)
    (member : birth ∈ selected sources run debtor unit window) :
    birth ∈ admissions sources run ∧ birth.claim.2.debtor = debtor ∧
      birth.unit = unit ∧ window (windowOf sources birth.claim) = true := by
  simpa only [selected, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using member

def remainingQuote {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (debtor : Party) (unit : Good)
    (window : Window sources → Bool) : ℚ :=
  ((selected sources run debtor unit window).map fun birth => birth.remaining * birth.rate).sum

def paidQuote {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (debtor : Party) (unit : Good)
    (window : Window sources → Bool) : ℚ :=
  ((selected sources run debtor unit window).map fun birth => birth.paid * birth.rate).sum

def issuedQuote {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (debtor : Party) (unit : Good)
    (window : Window sources → Bool) : ℚ :=
  ((selected sources run debtor unit window).map fun birth => birth.claim.2.quantity * birth.rate).sum

/-- The window queries original source-tagged claims. Quotes retain the original
unit and rate; they do not assert that issuance itself spends material. -/
theorem per_debtor_unit_window_conservation {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (debtor : Party) (unit : Good)
    (window : Window sources → Bool) :
    remainingQuote sources run debtor unit window + paidQuote sources run debtor unit window =
      issuedQuote sources run debtor unit window := by
  unfold remainingQuote paidQuote issuedQuote
  induction selected sources run debtor unit window with
  | nil => simp only [List.map_nil, List.sum_nil, add_zero]
  | cons birth rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have exactAmount := birth.settlement_quote_conservation
      linarith

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Exposure
