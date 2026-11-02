import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Admission.Credit
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Product
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {source : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue source.snapshot} {all : Candidates source catalogue} (owner : Ready all)

abbrev Raw := Section owner.release.programme.actual.pool
def fields := keys owner.release.programme.paid.family
abbrev branches := Comparison.branches owner.release.programme.actual.pool
abbrev Queue := Product.Queue (Key := Index owner.release.programme.paid.family)
  (Value := fun index => Comparison.Branch owner.release.programme.actual.pool index) (Output := Raw owner)
def queue : Queue owner := [.build (fields owner) id]
def sourceCount := Product.cardinality (branches owner) (fields owner)
def searchCeiling := 1+sourceCount owner*(Review.innerBound (all := all)+2)

private theorem cache_bound (remaining : Queue owner) (done : List (Raw owner)) (cached : List (Owned owner))
    (exact_cache : cached = done.filterMap (PublicPolicy.check owner.release.programme.actual.pool))
    (conserved : done++Product.denote (branches owner) remaining = sections owner.release.programme.actual.pool) :
    cached.length ≤ sourceCount owner := by
  have cacheLength : cached.length ≤ done.length := by rw [exact_cache];exact List.length_filterMap_le _ _
  have prefixes := congrArg List.length conserved
  have source := Product.cardinality_is_the_source_product_size (branches owner) (fields owner)
  change (sections owner.release.programme.actual.pool).length = sourceCount owner at source
  rw [List.length_append,source] at prefixes
  omega


def branchStart (head : Index owner.release.programme.paid.family) :=
  Comparison.BranchSource.start owner.release.programme.actual.pool head
def sourceWeight := 2+((keys owner.release.programme.paid.family).map fun head => (branchStart owner head).rank).sum+Admission.ceiling owner+3

theorem branch_rank_fits_the_source_weight (head : Index owner.release.programme.paid.family) :
    (branchStart owner head).rank+1 < sourceWeight owner := by
  have inside : (branchStart owner head).rank ∈
      (keys owner.release.programme.paid.family).map (fun head => (branchStart owner head).rank) :=
    List.mem_map.mpr ⟨head,List.mem_finRange _,rfl⟩
  have bounded := List.le_sum_of_mem inside
  dsimp only [sourceWeight]
  omega

inductive State where
  | constructing (remaining : Queue owner) (done : List (Raw owner)) (cached : List (Owned owner))
      (exact_cache : cached = done.filterMap (PublicPolicy.check owner.release.programme.actual.pool))
      (conserved : done++Product.denote (branches owner) remaining = sections owner.release.programme.actual.pool)
  | loading (head : Index owner.release.programme.paid.family) (tail : List (Index owner.release.programme.paid.family))
      (wrap : (∀ key ∈ head::tail,Comparison.Branch owner.release.programme.actual.pool key) → Raw owner)
      (rest : Queue owner) (current : Comparison.BranchSource.Cursor owner.release.programme.actual.pool head)
      (emitted : List (Comparison.Branch owner.release.programme.actual.pool head))
      (field_exact : emitted++current.denote = branches owner head)
      (bounded : current.rank ≤ (branchStart owner head).rank)
      (done : List (Raw owner)) (cached : List (Owned owner))
      (exact_cache : cached = done.filterMap (PublicPolicy.check owner.release.programme.actual.pool))
      (conserved : done++Product.denote (branches owner) (.build (head::tail) wrap::rest) = sections owner.release.programme.actual.pool)
  | admitting (term : Raw owner) (remaining : Queue owner) (done : List (Raw owner)) (cached : List (Owned owner))
      (exact_cache : cached = done.filterMap (PublicPolicy.check owner.release.programme.actual.pool))
      (conserved : done++[term]++Product.denote (branches owner) remaining = sections owner.release.programme.actual.pool)
  | nativeChecking (term : Raw owner) (remaining : Queue owner) (done : List (Raw owner)) (cached : List (Owned owner))
      (exact_cache : cached = done.filterMap (PublicPolicy.check owner.release.programme.actual.pool))
      (conserved : done++[term]++Product.denote (branches owner) remaining = sections owner.release.programme.actual.pool)
      (current : Admission.State owner term)
  | searching (current : Search owner)

def start : State owner := .constructing (queue owner) [] [] rfl (by
  simp only [queue,Product.denote,List.flatMap_cons,List.flatMap_nil,List.append_nil,Product.Task.denote,List.map_id,List.nil_append]
  rfl)
inductive Action where
  | source (event : Product.Event (Key := Index owner.release.programme.paid.family)
      (Value := fun index => Comparison.Branch owner.release.programme.actual.pool index) (Output := Raw owner))
  | admitted (term : Raw owner) (valid : Accepted owner.release.programme.actual.pool term)
  | rejected (term : Raw owner) (invalid : ¬ Accepted owner.release.programme.actual.pool term)
  | beginBranch (head : Index owner.release.programme.paid.family)
  | branch (head : Index owner.release.programme.paid.family) (event : Comparison.BranchSource.Event owner.release.programme.actual.pool head)
  | finishBranch (head : Index owner.release.programme.paid.family)
  | beginAdmission (term : Raw owner)
  | nativeAdmission (term : Raw owner) (event : Admission.Event owner term)
  | beginReview
  | review (action : Review.Action (all := all))

private theorem cache_is_the_complete_owned_catalogue (remaining : Queue owner) (done : List (Raw owner))
    (cached : List (Owned owner)) (exact_cache : cached = done.filterMap (PublicPolicy.check owner.release.programme.actual.pool))
    (conserved : done++Product.denote (branches owner) remaining = sections owner.release.programme.actual.pool)
    (stopped : Product.step (branches owner) remaining = none) : cached = policies owner := by
  have empty := (Product.stopped_iff_empty (branches owner) remaining).mp stopped
  have exactDone : done = sections owner.release.programme.actual.pool := by
    simpa only [empty,Product.denote,List.flatMap_nil,List.append_nil] using conserved
  rw [exact_cache,exactDone]
  rfl


private def moveProduct (remaining : Queue owner) (done : List (Raw owner)) (cached : List (Owned owner))
    (exact_cache : cached = done.filterMap (PublicPolicy.check owner.release.programme.actual.pool))
    (conserved : done++Product.denote (branches owner) remaining = sections owner.release.programme.actual.pool) :
    Option (State owner × Action owner) :=
      match observed : Product.step (branches owner) remaining with
      | none =>
        let complete := cache_is_the_complete_owned_catalogue owner remaining done cached exact_cache conserved observed
        some (.searching (.candidates cached (by
          intro rejected
          rw [complete] at rejected
          exact rejected)),.beginReview)
      | some (after,yielded,event) => match yielded with
        | none => some (.constructing after done cached exact_cache (by
            have next := Product.one_step_conserves_order_and_multiplicity (branches owner) observed
            rw [next] at conserved
            exact conserved),.source event)
        | some term => some (.admitting term after done cached exact_cache (by
            have next := Product.one_step_conserves_order_and_multiplicity (branches owner) observed
            rw [next] at conserved
            simpa only [Option.toList_some,List.append_assoc] using conserved),.source event)

def move : State owner → Option (State owner × Action owner)
  | .constructing (.build (head::tail) wrap::rest) done cached exact_cache conserved =>
      some (.loading head tail wrap rest (branchStart owner head) []
        (Comparison.BranchSource.all_quotas_are_exactly_the_original_branches _ _) (Nat.le_refl _)
        done cached exact_cache conserved,.beginBranch head)
  | .constructing remaining done cached exact_cache conserved => moveProduct owner remaining done cached exact_cache conserved
  | .loading head tail wrap rest current emitted field_exact bounded done cached exact_cache conserved =>
      match observed : Comparison.BranchSource.step current with
      | none =>
          let complete : emitted = branches owner head := by
            simpa only [Comparison.BranchSource.stopped_has_no_residual current observed,List.append_nil] using field_exact
          some (.constructing (.alternatives head tail emitted wrap::rest) done cached exact_cache (by
            have ordered : Product.denote (branches owner) (.build (head::tail) wrap::rest) =
                Product.denote (branches owner) (.alternatives head tail emitted wrap::rest) := by
              rw [complete]
              simpa only [Option.toList_none,List.nil_append] using
                (Product.one_step_conserves_order_and_multiplicity (branches owner)
                  (before := .build (head::tail) wrap::rest)
                  (after := .alternatives head tail (branches owner head) wrap::rest)
                  (yielded := none) (event := .read head) rfl)
            rw [←ordered];exact conserved),.finishBranch head)
      | some (after,yielded,event) =>
          some (.loading head tail wrap rest after (emitted++yielded.toList) (by
            rw [List.append_assoc,←Comparison.BranchSource.one_step_conserves observed];exact field_exact) (by
            have smaller := Comparison.BranchSource.step_decreases_rank observed;omega)
            done cached exact_cache conserved,.branch head event)

  | .admitting term remaining done cached exact_cache conserved =>
      some (.nativeChecking term remaining done cached exact_cache conserved (Admission.start owner term),.beginAdmission term)
  | .nativeChecking term remaining done cached exact_cache conserved current =>
      match tested : Admission.step owner current with
      | some (after,event) => some (.nativeChecking term remaining done cached exact_cache conserved after,.nativeAdmission term event)
      | none => match current with
        | .approved valid => some
          (.constructing remaining (done++[term]) (cached++[⟨term,valid⟩]) (by
            rw [List.filterMap_append,List.filterMap_cons,PublicPolicy.check,dif_pos valid,List.filterMap_nil]
            exact congrArg (fun xs => xs++[⟨term,valid⟩]) exact_cache) conserved,.admitted term valid)
        | .refused row inside broken =>
          let valid : ¬ Accepted owner.release.programme.actual.pool term := fun yes => broken ((rows_iff _ term).mpr yes row inside)
          some (.constructing remaining (done++[term]) cached (by
            rw [List.filterMap_append,List.filterMap_cons,PublicPolicy.check,dif_neg valid,List.filterMap_nil,List.append_nil]
            exact exact_cache) conserved,.rejected term valid)
        | .waiting .. | .finishing .. | .quoting .. | .reserving .. => False.elim (by
            have impossible := (Admission.stopped_iff_finished owner _).mp tested
            cases impossible)
  | .searching current => match Review.move owner current with
    | none => none
    | some (next,action) => some (.searching next,.review action)

def moveUsing (supplied : List (Review.Probe all)) (exact_source : supplied = Review.probes all) : State owner → Option (State owner × Action owner)
  | .constructing (.build (head::tail) wrap::rest) done cached exact_cache conserved =>
      some (.loading head tail wrap rest (branchStart owner head) []
        (Comparison.BranchSource.all_quotas_are_exactly_the_original_branches _ _) (Nat.le_refl _)
        done cached exact_cache conserved,.beginBranch head)
  | .constructing remaining done cached exact_cache conserved => moveProduct owner remaining done cached exact_cache conserved
  | .loading head tail wrap rest current emitted field_exact bounded done cached exact_cache conserved =>
      match observed : Comparison.BranchSource.step current with
      | none =>
          let complete : emitted = branches owner head := by
            simpa only [Comparison.BranchSource.stopped_has_no_residual current observed,List.append_nil] using field_exact
          some (.constructing (.alternatives head tail emitted wrap::rest) done cached exact_cache (by
            have ordered : Product.denote (branches owner) (.build (head::tail) wrap::rest) =
                Product.denote (branches owner) (.alternatives head tail emitted wrap::rest) := by
              rw [complete]
              simpa only [Option.toList_none,List.nil_append] using
                (Product.one_step_conserves_order_and_multiplicity (branches owner)
                  (before := .build (head::tail) wrap::rest)
                  (after := .alternatives head tail (branches owner head) wrap::rest)
                  (yielded := none) (event := .read head) rfl)
            rw [←ordered];exact conserved),.finishBranch head)
      | some (after,yielded,event) =>
          some (.loading head tail wrap rest after (emitted++yielded.toList) (by
            rw [List.append_assoc,←Comparison.BranchSource.one_step_conserves observed];exact field_exact) (by
            have smaller := Comparison.BranchSource.step_decreases_rank observed;omega)
            done cached exact_cache conserved,.branch head event)

  | .admitting term remaining done cached exact_cache conserved =>
      some (.nativeChecking term remaining done cached exact_cache conserved (Admission.start owner term),.beginAdmission term)
  | .nativeChecking term remaining done cached exact_cache conserved current =>
      match tested : Admission.step owner current with
      | some (after,event) => some (.nativeChecking term remaining done cached exact_cache conserved after,.nativeAdmission term event)
      | none => match current with
        | .approved valid => some
          (.constructing remaining (done++[term]) (cached++[⟨term,valid⟩]) (by
            rw [List.filterMap_append,List.filterMap_cons,PublicPolicy.check,dif_pos valid,List.filterMap_nil]
            exact congrArg (fun xs => xs++[⟨term,valid⟩]) exact_cache) conserved,.admitted term valid)
        | .refused row inside broken =>
          let valid : ¬ Accepted owner.release.programme.actual.pool term := fun yes => broken ((rows_iff _ term).mpr yes row inside)
          some (.constructing remaining (done++[term]) cached (by
            rw [List.filterMap_append,List.filterMap_cons,PublicPolicy.check,dif_neg valid,List.filterMap_nil,List.append_nil]
            exact exact_cache) conserved,.rejected term valid)
        | .waiting .. | .finishing .. | .quoting .. | .reserving .. => False.elim (by
            have impossible := (Admission.stopped_iff_finished owner _).mp tested
            cases impossible)
  | .searching current => match Review.moveUsing owner supplied exact_source current with
    | none => none
    | some (next,action) => some (.searching next,.review action)

theorem moveUsing_eq (supplied : List (Review.Probe all)) (exact_source : supplied = Review.probes all) (before : State owner) :
    moveUsing owner supplied exact_source before = move owner before := by
  cases before with
  | constructing remaining done cached exact_cache conserved =>
    cases remaining with
    | nil => rfl
    | cons task rest => cases task with
      | build fields wrap => cases fields <;> rfl
      | alternatives => rfl
  | loading => rfl
  | admitting | nativeChecking => rfl
  | searching current => simp only [moveUsing,move,Review.moveUsing_eq]

def moveWith (supplied : List (Review.Probe all)) (exact_source : supplied = Review.probes all) (challengers : List (Offer all)) (exact_challengers : challengers = offers all) : State owner → Option (State owner × Action owner)
  | .constructing (.build (head::tail) wrap::rest) done cached exact_cache conserved =>
      some (.loading head tail wrap rest (branchStart owner head) []
        (Comparison.BranchSource.all_quotas_are_exactly_the_original_branches _ _) (Nat.le_refl _)
        done cached exact_cache conserved,.beginBranch head)
  | .constructing remaining done cached exact_cache conserved => moveProduct owner remaining done cached exact_cache conserved
  | .loading head tail wrap rest current emitted field_exact bounded done cached exact_cache conserved =>
      match observed : Comparison.BranchSource.step current with
      | none =>
          let complete : emitted = branches owner head := by
            simpa only [Comparison.BranchSource.stopped_has_no_residual current observed,List.append_nil] using field_exact
          some (.constructing (.alternatives head tail emitted wrap::rest) done cached exact_cache (by
            have ordered : Product.denote (branches owner) (.build (head::tail) wrap::rest) =
                Product.denote (branches owner) (.alternatives head tail emitted wrap::rest) := by
              rw [complete]
              simpa only [Option.toList_none,List.nil_append] using
                (Product.one_step_conserves_order_and_multiplicity (branches owner)
                  (before := .build (head::tail) wrap::rest)
                  (after := .alternatives head tail (branches owner head) wrap::rest)
                  (yielded := none) (event := .read head) rfl)
            rw [←ordered];exact conserved),.finishBranch head)
      | some (after,yielded,event) =>
          some (.loading head tail wrap rest after (emitted++yielded.toList) (by
            rw [List.append_assoc,←Comparison.BranchSource.one_step_conserves observed];exact field_exact) (by
            have smaller := Comparison.BranchSource.step_decreases_rank observed;omega)
            done cached exact_cache conserved,.branch head event)

  | .admitting term remaining done cached exact_cache conserved =>
      some (.nativeChecking term remaining done cached exact_cache conserved (Admission.start owner term),.beginAdmission term)
  | .nativeChecking term remaining done cached exact_cache conserved current =>
      match tested : Admission.step owner current with
      | some (after,event) => some (.nativeChecking term remaining done cached exact_cache conserved after,.nativeAdmission term event)
      | none => match current with
        | .approved valid => some
          (.constructing remaining (done++[term]) (cached++[⟨term,valid⟩]) (by
            rw [List.filterMap_append,List.filterMap_cons,PublicPolicy.check,dif_pos valid,List.filterMap_nil]
            exact congrArg (fun xs => xs++[⟨term,valid⟩]) exact_cache) conserved,.admitted term valid)
        | .refused row inside broken =>
          let valid : ¬ Accepted owner.release.programme.actual.pool term := fun yes => broken ((rows_iff _ term).mpr yes row inside)
          some (.constructing remaining (done++[term]) cached (by
            rw [List.filterMap_append,List.filterMap_cons,PublicPolicy.check,dif_neg valid,List.filterMap_nil,List.append_nil]
            exact exact_cache) conserved,.rejected term valid)
        | .waiting .. | .finishing .. | .quoting .. | .reserving .. => False.elim (by
            have impossible := (Admission.stopped_iff_finished owner _).mp tested
            cases impossible)
  | .searching current => match Review.moveWith owner supplied exact_source challengers exact_challengers current with
    | none => none
    | some (next,action) => some (.searching next,.review action)

theorem moveWith_eq (supplied : List (Review.Probe all)) (exact_source : supplied = Review.probes all) (challengers : List (Offer all)) (exact_challengers : challengers = offers all) (before : State owner) :
    moveWith owner supplied exact_source challengers exact_challengers before = move owner before := by
  cases before with
  | constructing remaining done cached exact_cache conserved =>
    cases remaining with
    | nil => rfl
    | cons task rest => cases task with
      | build fields wrap => cases fields <;> rfl
      | alternatives => rfl
  | loading => rfl
  | admitting | nativeChecking => rfl
  | searching current => simp only [moveWith,move,Review.moveWith_eq]

def State.finished : State owner → Bool
  | .searching current => current.finished owner
  | _ => false


def State.rank : State owner → Nat
  | .constructing remaining .. => sourceWeight owner*Product.rank (branches owner) remaining+searchCeiling owner+2
  | .loading head tail wrap rest current _ _ _ .. =>
      sourceWeight owner*Product.rank (branches owner) (.alternatives head tail (branches owner head) wrap::rest)+current.rank+searchCeiling owner+3
  | .admitting _ remaining .. => sourceWeight owner*Product.rank (branches owner) remaining+searchCeiling owner+Admission.ceiling owner+4
  | .nativeChecking _ remaining _ _ _ _ current => sourceWeight owner*Product.rank (branches owner) remaining+searchCeiling owner+3+current.rank owner
  | .searching current => current.rank owner


private theorem product_step_progresses (remaining : Queue owner) (done : List (Raw owner)) (cached : List (Owned owner))
    (exact_cache : cached = done.filterMap (PublicPolicy.check owner.release.programme.actual.pool))
    (conserved : done++Product.denote (branches owner) remaining = sections owner.release.programme.actual.pool)
    {after : State owner} {action : Action owner}
    (step : moveProduct owner remaining done cached exact_cache conserved = some (after,action)) :
    after.rank owner < (State.constructing remaining done cached exact_cache conserved).rank owner := by
  dsimp only [moveProduct] at step
  split at step
  · rename_i stopped
    cases Option.some.inj step
    have bounded := cache_bound owner remaining done cached exact_cache conserved
    have multiplied := Nat.mul_le_mul_right (Review.innerBound (all := all)+2) bounded
    simp only [State.rank,Search.rank,searchCeiling]
    omega
  · rename_i next yielded event observed
    cases yielded <;> dsimp only at step
    all_goals cases Option.some.inj step
    all_goals have reduced := Product.step_decreases_the_source_constructor_rank (branches owner) observed
    all_goals have positive : 2 ≤ sourceWeight owner := by dsimp only [sourceWeight];omega
    all_goals have nativeCredit : Admission.ceiling owner+3 ≤ sourceWeight owner := by dsimp only [sourceWeight];omega
    all_goals simp only [State.rank]
    all_goals nlinarith

theorem each_paid_constructor_or_review_step_progresses {before after : State owner} {action : Action owner}
    (step : move owner before = some (after,action)) : after.rank owner < before.rank owner := by
  cases before with
  | constructing remaining done cached exact_cache conserved =>
    cases remaining with
    | nil => exact product_step_progresses owner _ _ _ _ _ step
    | cons task rest =>
      cases task with
      | build fields wrap =>
        cases fields with
        | nil => exact product_step_progresses owner _ _ _ _ _ step
        | cons head tail =>
          cases Option.some.inj step
          have reduced := Product.step_decreases_the_source_constructor_rank (branches owner)
            (before := .build (head::tail) wrap::rest) (by rfl)
          have bounded := branch_rank_fits_the_source_weight owner head
          simp only [State.rank]
          nlinarith
      | alternatives head tail values wrap => exact product_step_progresses owner _ _ _ _ _ step
  | loading head tail wrap rest current emitted field_exact bounded done cached exact_cache conserved =>
    dsimp only [move] at step
    split at step
    · rename_i stopped
      cases Option.some.inj step
      have complete : emitted = branches owner head := by
        simpa only [Comparison.BranchSource.stopped_has_no_residual current stopped,List.append_nil] using field_exact
      simp only [State.rank,complete];omega
    · rename_i next yielded event observed
      cases Option.some.inj step
      have reduced := Comparison.BranchSource.step_decreases_rank observed
      simp only [State.rank];omega
  | admitting term remaining done cached exact_cache conserved =>
    cases Option.some.inj step
    simp only [State.rank,Admission.start_rank];omega
  | nativeChecking term remaining done cached exact_cache conserved current =>
    dsimp only [move] at step;split at step
    · rename_i next event observed
      cases Option.some.inj step
      have reduced := Admission.each_step_progresses owner observed
      simp only [State.rank];omega
    · rename_i stopped
      cases current with
      | approved | refused => cases Option.some.inj step;simp only [State.rank,Admission.State.rank];omega
      | waiting | finishing | quoting | reserving =>
        have impossible := (Admission.stopped_iff_finished owner _).mp stopped
        cases impossible
  | searching current =>
    dsimp only [move] at step;split at step
    · cases step
    · rename_i next event observed
      cases Option.some.inj step
      exact Review.each_search_step_decreases_the_source_rank owner observed

private theorem moveProduct_ne_none (remaining : Queue owner) (done : List (Raw owner)) (cached : List (Owned owner))
    (exact_cache : cached = done.filterMap (PublicPolicy.check owner.release.programme.actual.pool))
    (conserved : done++Product.denote (branches owner) remaining = sections owner.release.programme.actual.pool) :
    moveProduct owner remaining done cached exact_cache conserved ≠ none := by
  dsimp only [moveProduct]
  split
  · simp
  · rename_i next yielded event observed
    cases yielded <;> simp

theorem move_none_iff_finished (before : State owner) : move owner before = none ↔ before.finished owner = true := by
  cases before with
  | constructing remaining done cached exact_cache conserved =>
    cases remaining with
    | nil => exact ⟨fun stopped => False.elim (moveProduct_ne_none owner _ _ _ _ _ (by simpa only [move] using stopped)),by simp [State.finished]⟩
    | cons task rest =>
      cases task with
      | build fields wrap =>
        cases fields with
        | nil => exact ⟨fun stopped => False.elim (moveProduct_ne_none owner _ _ _ _ _ (by simpa only [move] using stopped)),by simp [State.finished]⟩
        | cons head tail => simp [move,State.finished]
      | alternatives head tail values wrap =>
        exact ⟨fun stopped => False.elim (moveProduct_ne_none owner _ _ _ _ _ (by simpa only [move] using stopped)),by simp [State.finished]⟩
  | loading head tail wrap rest current emitted field_exact bounded done cached exact_cache conserved =>
    dsimp only [move,State.finished];split <;> simp
  | admitting => simp [move,State.finished]
  | nativeChecking term remaining done cached exact_cache conserved current =>
    dsimp only [move,State.finished];split
    · simp
    · rename_i stopped
      cases current with
      | approved | refused => simp
      | waiting | finishing | quoting | reserving =>
        have impossible := (Admission.stopped_iff_finished owner _).mp stopped
        cases impossible
  | searching current =>
    dsimp only [move,State.finished];split
    · rename_i stopped;simp only [Review.move_none_iff_finished] at stopped;exact ⟨fun _ => stopped,fun _ => rfl⟩
    · rename_i next event observed
      have unfinished : current.finished owner ≠ true := fun finished => by
        have stopped := (Review.move_none_iff_finished owner current).mpr finished
        rw [stopped] at observed;cases observed
      exact ⟨(by intro impossible;cases impossible),fun finished => False.elim (unfinished finished)⟩

inductive History : State owner → State owner → List (Action owner) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (observed : move owner before = some (middle,event))
      (later : History middle after work) : History before after (event::work)
structure Run (before : State owner) (capacity : Nat) where
  private mk ::
  endpoint : State owner
  work : List (Action owner)
  history : History owner before endpoint work
  fits : work.length ≤ capacity

def execute : (capacity : Nat) → (before : State owner) → Run owner before capacity
  | 0,before => ⟨before,[],.nil before,by rfl⟩
  | capacity+1,before => match observed : move owner before with
    | none => ⟨before,[],.nil before,Nat.zero_le _⟩
    | some (after,event) =>
      let later := execute capacity after
      ⟨later.endpoint,event::later.work,.step observed later.history,by
        have := later.fits;simpa only [List.length_cons] using Nat.succ_le_succ this⟩

theorem zero_credit_does_not_load_any_source_field (before : State owner) :
    (execute owner 0 before).endpoint = before ∧ (execute owner 0 before).work = [] := ⟨rfl,rfl⟩

theorem source_rank_completes_generation_and_full_review (capacity : Nat) (before : State owner)
    (enough : before.rank owner ≤ capacity) : (execute owner capacity before).endpoint.finished owner = true := by
  induction capacity generalizing before with
  | zero =>
    cases before with
    | constructing | loading | admitting | nativeChecking => simp_all [State.rank]
    | searching current => cases current <;> simp_all [State.rank,State.finished,Search.rank,Search.finished,execute]
  | succ capacity ih =>
    unfold execute
    split
    · rename_i stopped;exact (move_none_iff_finished owner before).mp stopped
    · rename_i after event observed
      exact ih after (by have reduced := each_paid_constructor_or_review_step_progresses owner observed;omega)

structure Generated where
  private mk ::
  execution : Run owner (start owner) (Review.capacity owner)
  generated : execution = execute owner (Review.capacity owner) (start owner)
def generate : Generated owner := ⟨execute owner (Review.capacity owner) (start owner),rfl⟩

namespace Generated
variable {owner} (made : Generated owner)
def spent := made.execution.work.length
def ordinal (event : Fin made.execution.work.length) := Review.offset owner+event.val

theorem ordinal_bound (event : Fin made.execution.work.length) : made.ordinal event < owner.quota.val := by
  have fits := made.execution.fits;have covered := offset_is_covered_by_the_same_invoice owner;have := event.isLt
  dsimp [ordinal,Review.capacity] at *;omega

def slot (index : Index prepared) (event : Fin made.execution.work.length) :
    Fin (((owner.release.programme.paid.funding.resultAt index).invoice (owner.release.programme.paid.all_paid index)).bill.units) :=
  ⟨made.ordinal event,by
    rw [((owner.release.programme.paid.funding.resultAt index).invoice (owner.release.programme.paid.all_paid index)).size]
    exact made.ordinal_bound event⟩
theorem slots_are_not_reused (index : Index prepared) : Function.Injective (made.slot index) := by
  intro first second same;apply Fin.ext
  have equal := congrArg (fun slot => slot.val) same
  dsimp only [slot,ordinal] at equal;omega

theorem no_constructor_or_review_event_reuses_old_work (index : Index prepared) (old : owner.release.Token)
    (event : Fin made.execution.work.length) : made.slot index event ≠ owner.release.slot index old := by
  intro same
  have different := every_old_work_slot_precedes_the_new_tail owner old
  have equal := congrArg (fun slot => slot.val) same
  change Review.offset owner+event.val = owner.release.ordinal old at equal
  omega

structure Allocation (index : Index prepared) (event : Fin made.execution.work.length) where
  private mk ::
  invoice : EscrowBudget.Charge.Invoice (owner.release.programme.paid.funding.resultAt index)
  slot : Fin invoice.bill.units
  operation : Action owner
  slot_exact : slot.val = made.ordinal event
  operation_exact : operation = made.execution.work[event]
def allocation (index : Index prepared) (event : Fin made.execution.work.length) : Allocation made index event :=
  ⟨(owner.release.programme.paid.funding.resultAt index).invoice (owner.release.programme.paid.all_paid index),
    made.slot index event,made.execution.work[event],rfl,rfl⟩
theorem all_source_and_review_events_use_the_same_successful_invoice (index : Index prepared) (event : Fin made.execution.work.length) :
    (made.allocation index event).invoice.bill.payment.succeeded = true ∧
    (made.allocation index event).invoice.bill.units = owner.quota.val ∧
    (made.allocation index event).operation = made.execution.work[event] :=
  ⟨(made.allocation index event).invoice.paid,(made.allocation index event).invoice.size,rfl⟩

def unused := Review.capacity owner-made.spent
theorem constructor_and_review_share_one_tail : made.spent+made.unused = Review.capacity owner := by
  have := made.execution.fits;dsimp [spent,unused];omega

def completed : Option (Choice all) := match made.execution.endpoint with
  | .searching (.released policy maximal) => some (choice all (offer owner policy) maximal)
  | _ => none

def endpoint (index : Index prepared) : Binding.NativeCursor prepared.saved[index].point :=
  match made.execution.endpoint with
  | .searching (.released policy _) => ((offer owner policy).view index).endpoint
  | _ => Review.Generated.retained (owner := owner) index

theorem only_the_same_source_generated_verified_policy_is_executed (policy : Owned owner) (maximal : Maximal all (offer owner policy))
    (released : made.execution.endpoint = .searching (.released policy maximal)) (index : Index prepared) :
    made.endpoint index = ((offer owner policy).view index).endpoint := by simp only [endpoint,released]

end Generated
/-- Only a complete local catalogue may cross from source construction into challenger emission. -/
def SourceOnly : State owner → Prop
  | .searching (.candidates cached _) => cached = policies owner
  | .searching _ => False
  | _ => True

def SourceOpen : State owner → Prop
  | .searching _ => False
  | _ => True

private theorem product_handoff_has_exact_catalogue (remaining : Queue owner) (done : List (Raw owner))
    (cached : List (Owned owner)) (exact_cache : cached = done.filterMap (PublicPolicy.check owner.release.programme.actual.pool))
    (conserved : done++Product.denote (branches owner) remaining = sections owner.release.programme.actual.pool)
    {after : State owner} {action : Action owner}
    (step : moveProduct owner remaining done cached exact_cache conserved = some (after,action)) : SourceOnly owner after := by
  dsimp only [moveProduct] at step
  split at step
  · rename_i stopped
    cases Option.some.inj step
    exact cache_is_the_complete_owned_catalogue owner remaining done cached exact_cache conserved stopped
  · rename_i next yielded event observed
    cases yielded <;> dsimp only at step
    all_goals cases Option.some.inj step
    all_goals trivial

theorem source_steps_preserve_the_complete_catalogue {before after : State owner} {action : Action owner}
    (unstarted : SourceOpen owner before) (step : move owner before = some (after,action)) : SourceOnly owner after := by
  cases before with
  | constructing remaining done cached exact_cache conserved =>
    cases remaining with
    | nil => exact product_handoff_has_exact_catalogue owner _ done cached exact_cache conserved (by simpa only [move] using step)
    | cons task rest =>
      cases task with
      | build fields wrap =>
        cases fields with
        | nil => exact product_handoff_has_exact_catalogue owner _ done cached exact_cache conserved (by simpa only [move] using step)
        | cons head tail => cases Option.some.inj step;trivial
      | alternatives => exact product_handoff_has_exact_catalogue owner _ done cached exact_cache conserved (by simpa only [move] using step)
  | loading =>
    dsimp only [move] at step;split at step
    all_goals cases Option.some.inj step
    all_goals trivial
  | admitting => cases Option.some.inj step;trivial
  | nativeChecking term remaining done cached exact_cache conserved current =>
    dsimp only [move] at step;split at step
    · cases Option.some.inj step;trivial
    · rename_i stopped
      cases current with
      | approved | refused => cases Option.some.inj step;trivial
      | waiting | finishing | quoting | reserving =>
        have impossible := (Admission.stopped_iff_finished owner _).mp stopped
        cases impossible
  | searching current => exact False.elim unstarted

def State.creditMark : State owner → Admission.Credit.Mark all
  | .nativeChecking term _ _ _ _ _ current => Admission.Credit.mark owner term current
  | _ => .idle
def Action.creditLog : Action owner → Admission.Credit.Log all
  | .nativeAdmission term event => Admission.Credit.log owner term event
  | _ => .silent

private theorem moveProduct_credit_rule (remaining : Queue owner) (done : List (Raw owner)) (cached : List (Owned owner))
    (exact_cache : cached = done.filterMap (PublicPolicy.check owner.release.programme.actual.pool))
    (conserved : done++Product.denote (branches owner) remaining = sections owner.release.programme.actual.pool)
    {after : State owner} {event : Action owner}
    (observed : moveProduct owner remaining done cached exact_cache conserved = some (after,event)) :
    Admission.Credit.Rule .idle (event.creditLog owner) (after.creditMark owner) := by
  dsimp only [moveProduct] at observed;split at observed
  · cases Option.some.inj observed;exact .fresh _ _ rfl
  · split at observed
    all_goals cases Option.some.inj observed
    all_goals exact .fresh _ _ rfl

theorem move_credit_rule {before after : State owner} {event : Action owner}
    (observed : move owner before = some (after,event)) :
    Admission.Credit.Rule (before.creditMark owner) (event.creditLog owner) (after.creditMark owner) := by
  cases before with
  | constructing remaining done cached exact_cache conserved =>
    cases remaining with
    | nil =>
          dsimp only [move] at observed
          exact moveProduct_credit_rule owner _ _ _ _ _ observed
    | cons task rest =>
      cases task with
      | build fields wrap =>
        cases fields with
        | nil =>
          dsimp only [move] at observed
          exact moveProduct_credit_rule owner _ _ _ _ _ observed
        | cons head tail => cases Option.some.inj observed;exact .fresh _ _ rfl
      | alternatives =>
          dsimp only [move] at observed
          exact moveProduct_credit_rule owner _ _ _ _ _ observed
  | loading =>
    dsimp only [move] at observed;split at observed
    all_goals cases Option.some.inj observed
    all_goals exact .fresh _ _ rfl
  | admitting => cases Option.some.inj observed;exact .fresh _ _ rfl
  | nativeChecking term remaining done cached exact_cache conserved current =>
    dsimp only [move] at observed;split at observed
    · rename_i next action tested
      cases Option.some.inj observed
      exact Admission.Credit.step_rule owner tested
    · rename_i stopped
      cases current with
      | approved | refused => cases Option.some.inj observed;exact .fresh _ _ rfl
      | waiting | finishing | quoting | reserving =>
        have impossible := (Admission.stopped_iff_finished owner _).mp stopped
        cases impossible
  | searching current =>
    dsimp only [move] at observed;split at observed
    · cases observed
    · cases Option.some.inj observed;exact .fresh _ _ rfl

theorem moveWith_credit_rule (supplied : List (Review.Probe all)) (exact_source : supplied = Review.probes all)
    (challengers : List (Offer all)) (exact_challengers : challengers = offers all)
    {before after : State owner} {event : Action owner}
    (observed : moveWith owner supplied exact_source challengers exact_challengers before = some (after,event)) :
    Admission.Credit.Rule (before.creditMark owner) (event.creditLog owner) (after.creditMark owner) := by
  rw [moveWith_eq] at observed
  exact move_credit_rule owner observed

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration
