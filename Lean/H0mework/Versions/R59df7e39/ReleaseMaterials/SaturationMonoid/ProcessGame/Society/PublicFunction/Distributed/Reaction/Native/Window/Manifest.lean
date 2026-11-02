import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Finance.Fields
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Manifest
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Feedback.Authority.Trace Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat)
abbrev Visit := RootVisit (ProgrammeLiving.livingRoot bound.source.input).toAuthoritativeRoot.toRoot
abbrev World := Identity.OccurrenceImage P G O (Mandate.State P T) I
namespace Worlds
variable (limit : Nat)
def image (visit : Visit bound) : World (P := P) (G := G) (O := O) (T := T) (I := I) :=
  Identity.occurrenceImage bound.source.code bound.source.input visit.current
structure Cursor where
  private mk ::
  ordinal : Nat
  bounded : ordinal ≤ limit
  visit : Visit bound
  known : visit = ProgrammeHistory.visitAt bound.source.input ordinal
  cached : List (World (P := P) (G := G) (O := O) (T := T) (I := I))
  coherent : cached = (List.range ordinal).map (fun n => image bound (ProgrammeHistory.visitAt bound.source.input n))
def initial : Cursor bound limit := ⟨0,Nat.zero_le _,(ProgrammeLiving.livingRoot bound.source.input).toAuthoritativeRoot.toRoot.initialVisit,rfl,[],rfl⟩
variable {bound limit}
def Cursor.rank (cursor : Cursor bound limit) := limit-cursor.ordinal
def Cursor.move (cursor : Cursor bound limit) : Option (Nat × Cursor bound limit) :=
  if inside : cursor.ordinal < limit then
    some (cursor.ordinal,⟨cursor.ordinal+1,by omega,cursor.visit.next rfl,by rw [cursor.known];rfl,
      cursor.cached++[image bound cursor.visit],by
        rw [List.range_succ,List.map_append,List.map_cons,List.map_nil,←cursor.known,←cursor.coherent]⟩)
  else none
structure Completed (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (limit : Nat) where
  private mk ::
  visit : Visit bound
  known : visit = ProgrammeHistory.visitAt bound.source.input limit
  cached : List (World (P := P) (G := G) (O := O) (T := T) (I := I))
  coherent : cached = (List.range limit).map (fun n => image bound (ProgrammeHistory.visitAt bound.source.input n))
def Cursor.completed (cursor : Cursor bound limit) : Option (Completed bound limit) :=
  if done : cursor.ordinal = limit then some ⟨cursor.visit,by rw [cursor.known,done],cursor.cached,by rw [cursor.coherent,done]⟩ else none
theorem initial_rank : (initial bound limit).rank = limit := rfl
theorem Cursor.move_decreases {before after : Cursor bound limit} {event : Nat} (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  unfold Cursor.move at actual;split at actual
  · rename_i inside;cases actual;dsimp only [Cursor.rank];omega
  · cases actual
theorem Cursor.completed_iff_stopped (cursor : Cursor bound limit) : cursor.completed.isSome = true ↔ cursor.move = none := by
  by_cases done : cursor.ordinal = limit
  · simp [Cursor.completed,Cursor.move,done]
  · have inside : cursor.ordinal < limit := by have := cursor.bounded;omega
    simp [Cursor.completed,Cursor.move,done,inside]
theorem Cursor.stopped_iff_zero (cursor : Cursor bound limit) : cursor.move = none ↔ cursor.rank = 0 := by
  by_cases inside : cursor.ordinal < limit
  · simp only [Cursor.move,dif_pos inside,Option.some_ne_none,false_iff,Cursor.rank];omega
  · have done : cursor.ordinal = limit := by have := cursor.bounded;omega
    simp [Cursor.move,Cursor.rank,done]
end Worlds

abbrev GrantRecord (depth : Nat) := Sigma fun birth : Fin (depth+1) => Authority.TracedGrant bound birth.val depth
abbrev ChallengeRecord := Sigma fun claim : Authority.Challenge bound => Authority.ChallengeHistory bound claim
def originalImage (record : GrantRecord bound start) : List (GrantImage P G O T I × GrantImage P G O T I) :=
  if record.1.val < start then [(grantImage bound record.1.val (start-1) (Authority.traceGrant bound record.1.val (start-1) record.2.admission.grant),
    grantImage bound record.1.val (start+span-1) (Authority.traceGrant bound record.1.val (start+span-1) record.2.admission.grant))] else []
def candidateImage (record : GrantRecord bound (start+span)) : List (GrantImage P G O T I) :=
  if record.1.val < start+span then [grantImage bound record.1.val (start+span-1) (Authority.traceGrant bound record.1.val (start+span-1) record.2.admission.grant)] else []
def originalChallengeImage (record : ChallengeRecord bound) :=
  (challengeImage bound.source.code (Authority.programme bound) (Authority.sourceIndex bound) record.1,
    challengeStateImage bound.source.code (Authority.programme bound) (Authority.sourceIndex bound) record.2.state.current,
    challengeStateImage bound.source.code (Authority.programme bound) (Authority.sourceIndex bound)
      (Mandate.Challenge.through (Authority.programme bound) (Authority.sourceIndex bound) record.1 (Window.finish start span)).state.current)
def candidateChallengeImage (record : ChallengeRecord bound) :=
  (challengeImage bound.source.code (Authority.programme bound) (Authority.sourceIndex bound) record.1,
    challengeStateImage bound.source.code (Authority.programme bound) (Authority.sourceIndex bound) record.2.state.current)
open Finance.Fields
abbrev OriginalCursor := Mapping.State (originalImage bound start span) (Authority.recordsAt bound start)
abbrev Original := {values // values = (Authority.recordsAt bound start).map (originalImage bound start span)}
abbrev OldChallengeCursor := Mapping.State (originalChallengeImage bound start span) (Authority.challengesAt bound (start+1))
abbrev OldChallenge := {values // values = (Authority.challengesAt bound (start+1)).map (originalChallengeImage bound start span)}
abbrev CandidateCursor := Mapping.State (candidateImage bound start span) (Authority.recordsAt bound (start+span))
abbrev Candidate := {values // values = (Authority.recordsAt bound (start+span)).map (candidateImage bound start span)}
abbrev FreshChallengeCursor := Mapping.State (candidateChallengeImage bound) (Authority.challengesAt bound (Window.finish start span))
abbrev FreshChallenge := {values // values = (Authority.challengesAt bound (Window.finish start span)).map (candidateChallengeImage bound)}
private theorem filtered_map {A B : Type} (items : List A) (test : A → Bool) (value : A → B) :
    items.flatMap (fun item => if test item then [value item] else []) = (items.filter test).map value := by
  induction items with
  | nil => rfl
  | cons head tail ih => cases h : test head <;> simp [h,ih]
def oldCost := (Authority.recordsAt bound start).length
def oldChallengeCost := (Authority.challengesAt bound (start+1)).length
def candidateCost := (Authority.recordsAt bound (start+span)).length
def freshChallengeCost := (Authority.challengesAt bound (Window.finish start span)).length
noncomputable def capacity := Window.finish start span+oldCost bound start+oldChallengeCost bound start+candidateCost bound start span+freshChallengeCost bound start span+4
structure Completed where
  private mk ::
  worlds : Worlds.Completed bound (Window.finish start span)
  originals : Original bound start span
  oldChallenges : OldChallenge bound start span
  candidates : Candidate bound start span
  freshChallenges : FreshChallenge bound start span
inductive Cursor where
  | sourceWorlds (state : Worlds.Cursor bound (Window.finish start span))
  | oldGrants (worlds : Worlds.Completed bound (Window.finish start span)) (state : OriginalCursor bound start span)
  | oldClaims (worlds : Worlds.Completed bound (Window.finish start span)) (originals : Original bound start span) (state : OldChallengeCursor bound start span)
  | newGrants (worlds : Worlds.Completed bound (Window.finish start span)) (originals : Original bound start span) (oldChallenges : OldChallenge bound start span) (state : CandidateCursor bound start span)
  | newClaims (worlds : Worlds.Completed bound (Window.finish start span)) (originals : Original bound start span) (oldChallenges : OldChallenge bound start span) (candidates : Candidate bound start span) (state : FreshChallengeCursor bound start span)
def initial : Cursor bound start span := .sourceWorlds (Worlds.initial bound _)
variable {bound start span}
noncomputable def Cursor.rank : Cursor bound start span → Nat
  | .sourceWorlds state => state.rank+oldCost bound start+oldChallengeCost bound start+candidateCost bound start span+freshChallengeCost bound start span+4
  | .oldGrants _ state => state.rank+oldChallengeCost bound start+candidateCost bound start span+freshChallengeCost bound start span+3
  | .oldClaims _ _ state => state.rank+candidateCost bound start span+freshChallengeCost bound start span+2
  | .newGrants _ _ _ state => state.rank+freshChallengeCost bound start span+1
  | .newClaims _ _ _ _ state => state.rank
inductive Event (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat) where
  | world (ordinal : Nat)
  | beginOriginals
  | original (record : GrantRecord bound start)
  | beginOldChallenges
  | oldChallenge (record : ChallengeRecord bound)
  | beginCandidates
  | candidate (record : GrantRecord bound (start+span))
  | beginFreshChallenges
  | freshChallenge (record : ChallengeRecord bound)
def Cursor.move : Cursor bound start span → Option (Event bound start span × Cursor bound start span)
  | .sourceWorlds state => match done : state.completed with
    | some made => some (.beginOriginals,.oldGrants made (Mapping.initial _ _))
    | none => match moved : state.move with
      | none => False.elim (by have complete := (Worlds.Cursor.completed_iff_stopped state).mpr moved;rw [done] at complete;cases complete)
      | some (ordinal,next) => some (.world ordinal,.sourceWorlds next)
  | .oldGrants worlds state => match done : state.completed with
    | some made => some (.beginOldChallenges,.oldClaims worlds made (Mapping.initial _ _))
    | none => match moved : state.move with
      | none => False.elim (by have complete := (Mapping.State.completed_iff_stopped state).mpr moved;rw [done] at complete;cases complete)
      | some (record,next) => some (.original record,.oldGrants worlds next)
  | .oldClaims worlds originals state => match done : state.completed with
    | some made => some (.beginCandidates,.newGrants worlds originals made (Mapping.initial _ _))
    | none => match moved : state.move with
      | none => False.elim (by have complete := (Mapping.State.completed_iff_stopped state).mpr moved;rw [done] at complete;cases complete)
      | some (record,next) => some (.oldChallenge record,.oldClaims worlds originals next)
  | .newGrants worlds originals oldChallenges state => match done : state.completed with
    | some made => some (.beginFreshChallenges,.newClaims worlds originals oldChallenges made (Mapping.initial _ _))
    | none => match moved : state.move with
      | none => False.elim (by have complete := (Mapping.State.completed_iff_stopped state).mpr moved;rw [done] at complete;cases complete)
      | some (record,next) => some (.candidate record,.newGrants worlds originals oldChallenges next)
  | .newClaims worlds originals oldChallenges candidates state =>
    state.move.map fun (record,next) => (.freshChallenge record,.newClaims worlds originals oldChallenges candidates next)
def Cursor.completed : Cursor bound start span → Option (Completed bound start span)
  | .newClaims worlds originals oldChallenges candidates state => state.completed.map fun fresh => ⟨worlds,originals,oldChallenges,candidates,fresh⟩
  | _ => none
theorem initial_rank : (initial bound start span).rank = capacity bound start span := rfl

theorem Cursor.move_decreases {before after : Cursor bound start span} {event : Event bound start span}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  cases before with
  | sourceWorlds state =>
    dsimp only [Cursor.move] at actual;split at actual
    · rename_i made done;cases actual
      have zero := (Worlds.Cursor.stopped_iff_zero state).mp ((Worlds.Cursor.completed_iff_stopped _).mp (by rw [done];rfl))
      dsimp only [Cursor.rank]
      change (oldCost bound start+oldChallengeCost bound start+candidateCost bound start span+freshChallengeCost bound start span+3)+1 = state.rank+oldCost bound start+oldChallengeCost bound start+candidateCost bound start span+freshChallengeCost bound start span+4
      rw [zero];omega
    · rename_i pending;split at actual
      · rename_i stopped
        have complete := (Worlds.Cursor.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
      · rename_i native next moved;cases actual
        have decrease := Worlds.Cursor.move_decreases moved;dsimp only [Cursor.rank];omega
  | oldGrants frames state =>
    dsimp only [Cursor.move] at actual;split at actual
    · rename_i made done;cases actual
      have zero := (Mapping.State.stopped_iff_zero state).mp ((Mapping.State.completed_iff_stopped _).mp (by rw [done];rfl))
      dsimp only [Cursor.rank]
      change (oldChallengeCost bound start+candidateCost bound start span+freshChallengeCost bound start span+2)+1 = state.rank+oldChallengeCost bound start+candidateCost bound start span+freshChallengeCost bound start span+3
      rw [zero];omega
    · rename_i pending;split at actual
      · rename_i stopped
        have complete := (Mapping.State.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
      · rename_i native next moved;cases actual
        have decrease := Mapping.State.move_decreases moved;dsimp only [Cursor.rank];omega
  | oldClaims frames original state =>
    dsimp only [Cursor.move] at actual;split at actual
    · rename_i made done;cases actual
      have zero := (Mapping.State.stopped_iff_zero state).mp ((Mapping.State.completed_iff_stopped _).mp (by rw [done];rfl))
      dsimp only [Cursor.rank]
      change (candidateCost bound start span+freshChallengeCost bound start span+1)+1 = state.rank+candidateCost bound start span+freshChallengeCost bound start span+2
      rw [zero];omega
    · rename_i pending;split at actual
      · rename_i stopped
        have complete := (Mapping.State.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
      · rename_i native next moved;cases actual
        have decrease := Mapping.State.move_decreases moved;dsimp only [Cursor.rank];omega
  | newGrants frames original old state =>
    dsimp only [Cursor.move] at actual;split at actual
    · rename_i made done;cases actual
      have zero := (Mapping.State.stopped_iff_zero state).mp ((Mapping.State.completed_iff_stopped _).mp (by rw [done];rfl))
      dsimp only [Cursor.rank]
      change (freshChallengeCost bound start span+0)+1 = state.rank+freshChallengeCost bound start span+1
      rw [zero];omega
    · rename_i pending;split at actual
      · rename_i stopped
        have complete := (Mapping.State.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
      · rename_i native next moved;cases actual
        have decrease := Mapping.State.move_decreases moved;dsimp only [Cursor.rank];omega
  | newClaims frames original old fresh state =>
    dsimp only [Cursor.move] at actual
    cases moved : state.move with
    | none => simp only [moved,Option.map_none,reduceCtorEq] at actual
    | some pair =>
      rcases pair with ⟨native,next⟩;rw [moved] at actual;cases actual
      exact Mapping.State.move_decreases moved

theorem Cursor.completed_iff_stopped (cursor : Cursor bound start span) : cursor.completed.isSome = true ↔ cursor.move = none := by
  cases cursor with
  | sourceWorlds state =>
    simp only [Cursor.completed,Option.isSome_none,Bool.false_eq_true,false_iff]
    dsimp only [Cursor.move];split
    · simp
    · rename_i pending;split
      · rename_i stopped
        have complete := (Worlds.Cursor.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
      · simp
  | oldGrants frames state =>
    simp only [Cursor.completed,Option.isSome_none,Bool.false_eq_true,false_iff]
    dsimp only [Cursor.move];split
    · simp
    · rename_i pending;split
      · rename_i stopped
        have complete := (Mapping.State.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
      · simp
  | oldClaims frames original state =>
    simp only [Cursor.completed,Option.isSome_none,Bool.false_eq_true,false_iff]
    dsimp only [Cursor.move];split
    · simp
    · rename_i pending;split
      · rename_i stopped
        have complete := (Mapping.State.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
      · simp
  | newGrants frames original old state =>
    simp only [Cursor.completed,Option.isSome_none,Bool.false_eq_true,false_iff]
    dsimp only [Cursor.move];split
    · simp
    · rename_i pending;split
      · rename_i stopped
        have complete := (Mapping.State.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
      · simp
  | newClaims frames original old fresh state =>
    have same := Mapping.State.completed_iff_stopped state
    cases done : state.completed <;> cases moved : state.move <;> simp [Cursor.completed,Cursor.move,done,moved] at *
theorem Cursor.stopped_iff_zero (cursor : Cursor bound start span) : cursor.move = none ↔ cursor.rank = 0 := by
  cases cursor with
  | sourceWorlds state =>
    have active : (Cursor.sourceWorlds state).move ≠ none := by
      intro stopped;have complete := (Cursor.completed_iff_stopped (Cursor.sourceWorlds state)).mpr stopped;cases complete
    simp only [active,false_iff,Cursor.rank];omega
  | oldGrants frames state =>
    have active : (Cursor.oldGrants frames state).move ≠ none := by
      intro stopped;have complete := (Cursor.completed_iff_stopped (Cursor.oldGrants frames state)).mpr stopped;cases complete
    simp only [active,false_iff,Cursor.rank];omega
  | oldClaims frames original state =>
    have active : (Cursor.oldClaims frames original state).move ≠ none := by
      intro stopped;have complete := (Cursor.completed_iff_stopped (Cursor.oldClaims frames original state)).mpr stopped;cases complete
    simp only [active,false_iff,Cursor.rank];omega
  | newGrants frames original old state =>
    have active : (Cursor.newGrants frames original old state).move ≠ none := by
      intro stopped;have complete := (Cursor.completed_iff_stopped (Cursor.newGrants frames original old state)).mpr stopped;cases complete
    simp only [active,false_iff,Cursor.rank];omega
  | newClaims frames original old fresh state =>
    have same : (Cursor.newClaims frames original old fresh state).move = none ↔ state.move = none := by cases moved : state.move <;> simp [Cursor.move,moved]
    rw [same];exact Mapping.State.stopped_iff_zero state

inductive History : Cursor bound start span → Cursor bound start span → List (Event bound start span) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
structure Run (before : Cursor bound start span) (capacity : Nat) where
  private mk ::
  endpoint : Cursor bound start span
  work : List (Event bound start span)
  history : History before endpoint work
  covered : work.length ≤ capacity
  exhausted : endpoint.move = none ∨ work.length = capacity
  conservation : endpoint.rank+work.length = before.rank

def run : (capacity : Nat) → (before : Cursor bound start span) → Run before capacity
  | 0,before => ⟨before,[],.nil before,Nat.le_refl _,Or.inr rfl,by simp⟩
  | capacity+1,before => match actual : before.move with
    | none => ⟨before,[],.nil before,by simp,Or.inl actual,by simp⟩
    | some (event,next) =>
        let later := run capacity next
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.covered;simp only [List.length_cons];omega,
          later.exhausted.imp_right (fun same => by simp only [List.length_cons,same]),by
            have := later.conservation;have := Cursor.move_decreases actual;simp only [List.length_cons];omega⟩
theorem run_sufficient (before : Cursor bound start span) (capacity : Nat) (enough : before.rank ≤ capacity) :
    (run capacity before).endpoint.completed.isSome = true := by
  apply (Cursor.completed_iff_stopped _).mpr
  rcases (run capacity before).exhausted with stopped | full
  · exact stopped
  apply (Cursor.stopped_iff_zero _).mpr
  have := (run capacity before).conservation;omega

theorem run_work_exact (before : Cursor bound start span) (available : Nat) :
    (run available before).work.length = min available before.rank := by
  have covered := (run available before).covered
  have conserved := (run available before).conservation
  rcases (run available before).exhausted with stopped | full
  · have zero := (Cursor.stopped_iff_zero _).mp stopped
    rw [zero] at conserved
    have same : (run available before).work.length = before.rank := by omega
    rw [same,Nat.min_eq_right (by omega)]
  · rw [full,Nat.min_eq_left (by omega)]


def Completed.terminal (cache : Completed bound start span) := ProgrammeSource.rawCurrent bound.source.input cache.worlds.visit.current
theorem Completed.terminal_exact (cache : Completed bound start span) : cache.terminal = Window.terminal bound start span := by
  unfold Completed.terminal;rw [cache.worlds.known];rfl
def Completed.control (cache : Completed bound start span) : Open.Control (Mandate.State P T) :=
  ⟨cache.terminal.technology,cache.terminal.clock,cache.terminal.round⟩
theorem Completed.control_exact (cache : Completed bound start span) : cache.control = (Window.profile bound start span).control := by
  unfold Completed.control;rw [cache.terminal_exact];rfl

def Completed.manifest (cache : Completed bound start span) : Feedback.Authority.Trace.Manifest P G O T I :=
  ⟨cache.worlds.cached,cache.originals.val.flatten,cache.oldChallenges.val,cache.candidates.val.flatten,cache.freshChallenges.val⟩
theorem Completed.manifest_exact (cache : Completed bound start span) : cache.manifest = Window.manifest bound start span := by
  unfold Completed.manifest Window.manifest
  congr 1
  · exact cache.worlds.coherent
  · rw [cache.originals.property,←List.flatMap_def]
    unfold originalImage
    simpa only [decide_eq_true_eq] using filtered_map (Authority.recordsAt bound start)
      (fun record => decide (record.1.val < start)) (fun record =>
        (grantImage bound record.1.val (start-1) (Authority.traceGrant bound record.1.val (start-1) record.2.admission.grant),
         grantImage bound record.1.val (start+span-1) (Authority.traceGrant bound record.1.val (start+span-1) record.2.admission.grant)))
  · exact cache.oldChallenges.property
  · rw [cache.candidates.property,←List.flatMap_def]
    unfold candidateImage
    simpa only [Window.grants,decide_eq_true_eq] using filtered_map (Authority.recordsAt bound (start+span))
      (fun record => decide (record.1.val < start+span)) (fun record =>
        grantImage bound record.1.val (start+span-1) (Authority.traceGrant bound record.1.val (start+span-1) record.2.admission.grant))
  · exact cache.freshChallenges.property
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Manifest
