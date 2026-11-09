import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.Exit
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.Envelope
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.Trace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm (withCutoff)
open PublicFunction PublicFunction.Mandate

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {first second : Party} {unit : Good}

local notation "Raw" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Req" => Request Party Good Port (State Party Technology) Instrument
local notation "Term" => SafeTerm base scope first second unit

def SafeTerm.releaseTarget (term : Term) (expiry : ℚ) : Raw :=
  let installed := withCutoff scope expiry
  (law base installed).next term.cell.target (reviewPair base installed term.cell.target first second)

def SafeTerm.parties (term : Term) : List Party :=
  let active := law base (withCutoff scope term.band.lower)
  (scope.task.slots.map (·.bearer) ++ [first, second] ++ term.cell.target.technology.holder.toList ++
    term.cell.history.flatMap fun day => day.postings.flatMap fun posting =>
      Capitalism.Universal.Source.ProgrammeFace.itemParties active posting.item).dedup

def SafeTerm.exitAt (term : Term) (actions : Raw → List Req) (expiry : ℚ) (bearer : Party) : List Req :=
  Opening.independentOffersAt (law base (withCutoff scope expiry)) (term.releaseTarget expiry) actions bearer

def SafeTerm.ExitReady (term : Term) (actions : Raw → List Req) (expiry : ℚ) : Prop :=
  ∀ bearer ∈ term.parties, (term.exitAt actions expiry bearer).isEmpty = false

instance (term : Term) (actions : Raw → List Req) (expiry : ℚ) : Decidable (term.ExitReady actions expiry) := by
  unfold SafeTerm.ExitReady
  infer_instance

theorem SafeTerm.exit_same_on_admitted_band (term : Term) (actions : Raw → List Req)
    {a b : ℚ} (left : term.Allows a) (right : term.Allows b) (bearer : Party) :
    term.exitAt actions a bearer = term.exitAt actions b bearer := by
  have early := ((term_band_exact scope.task term.cell term.assigned a).mp left.2).2.1
  have also := ((term_band_exact scope.task term.cell term.assigned b).mp right.2).2.1
  have same : term.releaseTarget a = term.releaseTarget b :=
    reviewed_successor_same_expired_cell base scope term.cell.target first second early also
  have later : term.cell.target.clock ≤ (term.releaseTarget b).clock := by
    exact le_add_of_nonneg_right (le_max_left _ _)
  unfold SafeTerm.exitAt Opening.independentOffersAt
  rw [same]
  apply List.filter_congr
  intro instruction _
  have allowed := valid_iff_same_cell base scope (term.releaseTarget b) instruction
    (iff_of_false (not_le.mpr (early.trans_le later)) (not_le.mpr (also.trans_le later)))
  have independence : Opening.IndependentNecessity (law base (withCutoff scope a)) (term.releaseTarget b) bearer instruction ↔
      Opening.IndependentNecessity (law base (withCutoff scope b)) (term.releaseTarget b) bearer instruction := by
    unfold Opening.IndependentNecessity
    exact and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => allowed
  by_cases valid : Opening.IndependentNecessity (law base (withCutoff scope a)) (term.releaseTarget b) bearer instruction
  · simp [valid, independence.mp valid]
  · have invalid : ¬ Opening.IndependentNecessity (law base (withCutoff scope b)) (term.releaseTarget b) bearer instruction :=
      fun paid => valid (independence.mpr paid)
    simp [valid, invalid]

theorem SafeTerm.exit_ready_same_on_admitted_band (term : Term) (actions : Raw → List Req)
    {a b : ℚ} (left : term.Allows a) (right : term.Allows b) :
    term.ExitReady actions a ↔ term.ExitReady actions b :=
  forall_congr' fun bearer => forall_congr' fun _ => by
    rw [term.exit_same_on_admitted_band actions left right bearer]

variable (base scope first second unit)
  (initial : RawCurrent Party Good (State Party Technology) Instrument)
  (words : List (RawEvent Party Good Port (State Party Technology) Instrument))
  (actions : RawCurrent Party Good (State Party Technology) Instrument →
    List (Request Party Good Port (State Party Technology) Instrument))

def protectedFrontier : List Term :=
  (frontier base scope first second unit initial words).filter fun term =>
    decide (term.ExitReady actions term.band.lower)

def ProtectedFeasible (expiry : ℚ) : Prop :=
  ∃ term ∈ frontier base scope first second unit initial words,
    term.Allows expiry ∧ term.ExitReady actions expiry

theorem protected_frontier_exact (expiry : ℚ) :
    ProtectedFeasible base scope first second unit initial words actions expiry ↔
      ∃ term ∈ protectedFrontier base scope first second unit initial words actions, term.Allows expiry := by
  constructor
  · rintro ⟨term, original, fits, exits⟩
    refine ⟨term, List.mem_filter.mpr ⟨original, ?_⟩, fits⟩
    exact decide_eq_true ((term.exit_ready_same_on_admitted_band actions fits term.at_least_owns_its_review).mp exits)
  · rintro ⟨term, selected, fits⟩
    have original := List.mem_filter.mp selected
    exact ⟨term, original.1, fits,
      (term.exit_ready_same_on_admitted_band actions term.at_least_owns_its_review fits).mp
        (of_decide_eq_true original.2)⟩

def shortestProtected? :=
  Threshold.best (fun term : Term => -term.band.lower)
    (protectedFrontier base scope first second unit initial words actions)

theorem shortest_protected_exact {term : Term}
    (selected : shortestProtected? base scope first second unit initial words actions = some term) :
    term ∈ protectedFrontier base scope first second unit initial words actions ∧
      IsLeast {expiry | ProtectedFeasible base scope first second unit initial words actions expiry} term.band.lower := by
  have chosen := Threshold.best_spec selected
  refine ⟨chosen.1, (protected_frontier_exact base scope first second unit initial words actions _).mpr
    ⟨term, chosen.1, term.at_least_owns_its_review⟩, ?_⟩
  intro expiry feasible
  obtain ⟨other, original, fits⟩ := (protected_frontier_exact base scope first second unit initial words actions _).mp feasible
  exact (neg_le_neg_iff.mp (chosen.2 other original)).trans (Band.lower_le fits.2)

theorem shortest_protected_none
    (selected : shortestProtected? base scope first second unit initial words actions = none) (expiry : ℚ) :
    ¬ ProtectedFeasible base scope first second unit initial words actions expiry := by
  intro possible
  obtain ⟨term, candidate, _⟩ := (protected_frontier_exact base scope first second unit initial words actions _).mp possible
  rw [Threshold.best_eq_none.mp selected] at candidate
  cases candidate

def failed_exit_address (term : Term) (expiry : ℚ) (failed : ¬ term.ExitReady actions expiry) :
    {bearer // bearer ∈ term.parties ∧ (term.exitAt actions expiry bearer).isEmpty = true} :=
  match inspectList (fun bearer => (term.exitAt actions expiry bearer).isEmpty = false) term.parties with
  | .clear all => False.elim (failed all)
  | .failure bearer original absent => ⟨bearer, original, Bool.eq_true_of_not_eq_false absent⟩

def longestProtected? :=
  Threshold.best SafeTerm.ceiling
    (protectedFrontier base scope first second unit initial words actions)

theorem longest_protected_exact {term : Term}
    (selected : longestProtected? base scope first second unit initial words actions = some term) :
    IsLUB {expiry | ProtectedFeasible base scope first second unit initial words actions expiry} term.ceiling ∧
      ∀ earlier < term.ceiling,
        ∃ expiry, ProtectedFeasible base scope first second unit initial words actions expiry ∧ earlier < expiry := by
  simpa only [← protected_frontier_exact base scope first second unit initial words actions] using
    exact_envelope (protectedFrontier base scope first second unit initial words actions) selected

inductive ProtectedFailure (expiry : ℚ) where
  | calendar (reason : CandidateFailure base scope first second unit expiry initial words)
  | independentExit (term : Term) (listed : term ∈ frontier base scope first second unit initial words)
      (allowed : term.Allows expiry) (bearer : Party) (present : bearer ∈ term.parties)
      (missing : (term.exitAt actions expiry bearer).isEmpty = true)

def explainProtected (expiry : ℚ)
    (blocked : ¬ ProtectedFeasible base scope first second unit initial words actions expiry) :
    ProtectedFailure base scope first second unit initial words actions expiry :=
  letI (term : Term) : Decidable (term.Allows expiry) :=
    inferInstanceAs (Decidable (expiry ≤ scope.task.deadline ∧ term.band.Holds expiry))
  match inspectList (fun term : Term => ¬ term.Allows expiry)
      (frontier base scope first second unit initial words) with
  | .clear absent =>
    .calendar (explainCandidate base scope first second unit expiry initial words (fun possible => by
      obtain ⟨term, original, allowed⟩ := (frontier_is_exact base scope first second unit initial words expiry).mp possible
      exact absent term original allowed))
  | .failure term original denied =>
    let allowed := of_not_not denied
    let failed := failed_exit_address base scope first second unit actions term expiry
      (fun exits => blocked ⟨term, original, allowed, exits⟩)
    .independentExit term original allowed failed.val failed.property.1 failed.property.2

variable (original : RawEvent Party Good Port (State Party Technology) Instrument)
  (service : List (RawEvent Party Good Port (State Party Technology) Instrument))

local notation "Registered" => [] :: original :: service

inductive ProtectedResult where
  | blocked
      (absent : ∀ expiry, ¬ ProtectedFeasible base scope first second unit initial Registered actions expiry)
      (explain : ∀ expiry, ProtectedFailure base scope first second unit initial Registered actions expiry)
  | alreadyAdmitted (expiry : ℚ) (noOriginalRefusal : ¬ OriginDenied base scope initial original expiry)
  | installed (opening : Opening base scope first second unit initial original service)
      (exits : opening.term.ExitReady actions opening.term.band.lower)
      (least : IsLeast {expiry | ProtectedFeasible base scope first second unit initial Registered actions expiry}
        opening.term.band.lower)

def compileProtected : ProtectedResult base scope first second unit initial actions original service :=
  match selected : shortestProtected? base scope first second unit initial Registered actions with
  | none =>
    let absent := shortest_protected_none base scope first second unit initial Registered actions selected
    .blocked absent fun expiry =>
      explainProtected base scope first second unit initial Registered actions expiry (absent expiry)
  | some term =>
    let exact := shortest_protected_exact base scope first second unit initial Registered actions selected
    let listed := List.mem_filter.mp exact.1
    let active := law base (withCutoff scope term.band.lower)
    match inspectList (fun item => active.Valid item.before item.request)
        (active.rawItems (active.next initial []) original) with
    | .failure item original refused => .installed ⟨term, listed.1, item, original, refused⟩
        (of_decide_eq_true listed.2) exact.2
    | .clear paid => .alreadyAdmitted term.band.lower (fun ⟨item, original, denied⟩ => denied (paid item original))

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation
