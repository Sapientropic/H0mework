import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeSourceFrames
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeManifest
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Feedback.Authority.Trace
open Distributed.Recall.Information.Agency.Protocol
variable {Party Good Port Technology Instrument : Type}

/-- Source calls and image/list assembly, retaining the actual operands. Native
    record, image, history and primitive internals remain separate obligations. -/
inductive Event (Party Good Port Technology Instrument : Type) where
  | field (kind : Fin 5)
  | records (depth : Nat)
  | challenges (depth : Nat)
  | worldRead (ordinal : Nat) (value : Identity.OccurrenceImage Party Good Port (Mandate.State Party Technology) Instrument)
  | worldWrite (ordinal : Nat)
  | birthCheck (birth cutoff : Nat) (answer : Bool)
  | branch (taken : Bool)
  | grantBirth (birth : Nat)
  | grantProposal (value : ItemImage Party Good Port (Mandate.State Party Technology) Instrument)
  | grantAcceptance (value : ItemImage Party Good Port (Mandate.State Party Technology) Instrument)
  | grantInitial (value : GrantObligationImage Party Port)
  | grantFinal (value : GrantObligationImage Party Port)
  | grantHistory (value : List (GrantRecordImage Party Good Port Technology Instrument))
  | grantAssemble (birth last : Nat)
  | originalGrantWrite (birth : Nat)
  | candidateGrantWrite (birth : Nat)
  | challengeClaim (original : Bool) (value : ChallengeImage Party Good Port Technology Instrument)
  | challengeState (role : Fin 3) (value : ChallengeStateImage Party Good Port Technology Instrument)
  | challengeThrough (claim : ChallengeImage Party Good Port Technology Instrument) (finish : Nat)
  | originalChallengeWrite
  | candidateChallengeWrite
  | assemble
  deriving DecidableEq
private structure Part (α Party Good Port Technology Instrument : Type) where
  value : α
  work : List (Event Party Good Port Technology Instrument)
local notation "Result" => Part
private def map {α β : Type} : (items : List α) → (produce : α → Result β Party Good Port Technology Instrument) → Result (List β) Party Good Port Technology Instrument
  | [],_ => ⟨[],[]⟩
  | head::tail,produce => let first := produce head;let rest := map tail produce
      ⟨first.value::rest.value,first.work++rest.work⟩
private def flatMap {α β : Type} : (items : List α) → (produce : α → Result (List β) Party Good Port Technology Instrument) → Result (List β) Party Good Port Technology Instrument
  | [],_ => ⟨[],[]⟩
  | head::tail,produce => let first := produce head;let rest := flatMap tail produce
      ⟨first.value++rest.value,first.work++rest.work⟩
private theorem map_value {α β : Type} (items : List α) (produce : α → Result β Party Good Port Technology Instrument) :
    (map items produce).value = items.map (fun item => (produce item).value) := by
  induction items <;> simp_all [map]
private theorem flatMap_value {α β : Type} (items : List α) (produce : α → Result (List β) Party Good Port Technology Instrument) :
    (flatMap items produce).value = items.flatMap (fun item => (produce item).value) := by
  induction items <;> simp_all [flatMap]
private theorem map_work {α β : Type} (items : List α) (produce : α → Result β Party Good Port Technology Instrument)
    (budget : Nat) (bounded : ∀ item,(produce item).work.length ≤ budget) :
    (map items produce).work.length ≤ items.length*budget := by
  induction items with
  | nil => simp [map]
  | cons head tail ih =>
    simp only [map,List.length_append,List.length_cons,Nat.succ_mul]
    exact Nat.add_le_add (bounded head) ih |>.trans (by omega)
private theorem flatMap_work {α β : Type} (items : List α) (produce : α → Result (List β) Party Good Port Technology Instrument)
    (budget : Nat) (bounded : ∀ item,(produce item).work.length ≤ budget) :
    (flatMap items produce).work.length ≤ items.length*budget := by
  induction items with
  | nil => simp [flatMap]
  | cons head tail ih =>
    simp only [flatMap,List.length_append,List.length_cons,Nat.succ_mul]
    exact Nat.add_le_add (bounded head) ih |>.trans (by omega)
private theorem filtered_map {α β : Type} (items : List α) (test : α → Bool) (value : α → β) :
    items.flatMap (fun item => if test item then [value item] else []) = (items.filter test).map value := by
  induction items with
  | nil => rfl
  | cons head tail ih => cases h : test head <;> simp [h,ih]

variable [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (start span : Nat)
private def grant (birth last : Nat) (record : Authority.TracedGrant bound birth last) :
    Result (GrantImage Party Good Port Technology Instrument) Party Good Port Technology Instrument :=
  let proposal := itemImage bound.source.code record.admission.grant.proposal.item.val
  let acceptance := itemImage bound.source.code record.admission.grant.acceptance.item.val
  let initial := grantObligationImage (Mandate.Lifecycle.original bound.base bound.scope
    (Authority.currentAt bound) (Authority.wordAt bound) birth record.admission.grant)
  let final := grantObligationImage record.continuation.obligation
  let history := grantHistoryImage bound.source.code record.continuation
  ⟨⟨birth,proposal,acceptance,initial,final,history⟩,
    [.grantBirth birth,.grantProposal proposal,.grantAcceptance acceptance,.grantInitial initial,.grantFinal final,
      .grantHistory history,.grantAssemble birth last]⟩
private theorem grant_exact (birth last : Nat) (record : Authority.TracedGrant bound birth last) :
    (grant bound birth last record).value = grantImage bound birth last record := rfl
private def worlds : Result (List (Identity.OccurrenceImage Party Good Port (Mandate.State Party Technology) Instrument)) Party Good Port Technology Instrument :=
  map (List.range (Window.finish start span)) fun ordinal =>
    let image := Identity.occurrenceImage bound.source.code bound.source.input (ProgrammeHistory.visitAt bound.source.input ordinal).current
    ⟨image,[.worldRead ordinal image,.worldWrite ordinal]⟩
private def originals : Result (List (GrantImage Party Good Port Technology Instrument × GrantImage Party Good Port Technology Instrument)) Party Good Port Technology Instrument :=
  flatMap (Authority.recordsAt bound start) fun record =>
    if record.1.val < start then
      let before := grant bound record.1.val (start-1) (Authority.traceGrant bound record.1.val (start-1) record.2.admission.grant)
      let after := grant bound record.1.val (start+span-1) (Authority.traceGrant bound record.1.val (start+span-1) record.2.admission.grant)
      ⟨[(before.value,after.value)],[.birthCheck record.1.val start true,.branch true] ++ before.work ++ after.work ++ [.originalGrantWrite record.1.val]⟩
    else ⟨[],[.birthCheck record.1.val start false,.branch false]⟩
private def candidates : Result (List (GrantImage Party Good Port Technology Instrument)) Party Good Port Technology Instrument :=
  flatMap (Authority.recordsAt bound (start+span)) fun record =>
    if record.1.val < start+span then
      let image := grant bound record.1.val (start+span-1) (Authority.traceGrant bound record.1.val (start+span-1) record.2.admission.grant)
      ⟨[image.value],[.birthCheck record.1.val (start+span) true,.branch true] ++ image.work ++ [.candidateGrantWrite record.1.val]⟩
    else ⟨[],[.birthCheck record.1.val (start+span) false,.branch false]⟩
private def originalChallenges : Result (List (ChallengeImage Party Good Port Technology Instrument × ChallengeStateImage Party Good Port Technology Instrument × ChallengeStateImage Party Good Port Technology Instrument)) Party Good Port Technology Instrument :=
  map (Authority.challengesAt bound (start+1)) fun record =>
    let claim := challengeImage bound.source.code (Authority.programme bound) (Authority.sourceIndex bound) record.1
    let before := challengeStateImage bound.source.code (Authority.programme bound) (Authority.sourceIndex bound) record.2.state.current
    let through := Mandate.Challenge.through (Authority.programme bound) (Authority.sourceIndex bound) record.1 (Window.finish start span)
    let after := challengeStateImage bound.source.code (Authority.programme bound) (Authority.sourceIndex bound) through.state.current
    ⟨(claim,before,after),[.challengeClaim true claim,.challengeState 0 before,.challengeThrough claim (Window.finish start span),
      .challengeState 1 after,.originalChallengeWrite]⟩
private def candidateChallenges : Result (List (ChallengeImage Party Good Port Technology Instrument × ChallengeStateImage Party Good Port Technology Instrument)) Party Good Port Technology Instrument :=
  map (Authority.challengesAt bound (Window.finish start span)) fun record =>
    let claim := challengeImage bound.source.code (Authority.programme bound) (Authority.sourceIndex bound) record.1
    let current := challengeStateImage bound.source.code (Authority.programme bound) (Authority.sourceIndex bound) record.2.state.current
    ⟨(claim,current),[.challengeClaim false claim,.challengeState 2 current,.candidateChallengeWrite]⟩
private def generate : Result (Manifest Party Good Port Technology Instrument) Party Good Port Technology Instrument :=
  let world := worlds bound start span
  let oldGrant := originals bound start span
  let oldChallenge := originalChallenges bound start span
  let newGrant := candidates bound start span
  let newChallenge := candidateChallenges bound start span
  ⟨⟨world.value,oldGrant.value,oldChallenge.value,newGrant.value,newChallenge.value⟩,
    [.field 0] ++ world.work ++ [.records start,.field 1] ++ oldGrant.work ++
    [.challenges (start+1),.field 2] ++ oldChallenge.work ++ [.records (start+span),.field 3] ++ newGrant.work ++
    [.challenges (Window.finish start span),.field 4] ++ newChallenge.work ++ [.assemble]⟩
private theorem generated_exact : (generate bound start span).value = Window.manifest bound start span := by
  dsimp only [generate]
  congr 1
  · simp [worlds,map_value]
  · simp only [originals,flatMap_value,apply_ite]
    simp only [grant_exact]
    simpa only [decide_eq_true_eq] using filtered_map (Authority.recordsAt bound start)
      (fun record => decide (record.1.val < start)) (fun record =>
        (grantImage bound record.1.val (start-1) (Authority.traceGrant bound record.1.val (start-1) record.2.admission.grant),
         grantImage bound record.1.val (start+span-1) (Authority.traceGrant bound record.1.val (start+span-1) record.2.admission.grant)))
  · simp [originalChallenges,map_value]
  · simp only [candidates,flatMap_value,apply_ite]
    simp only [grant_exact]
    simpa only [Window.grants,decide_eq_true_eq] using filtered_map (Authority.recordsAt bound (start+span))
      (fun record => decide (record.1.val < start+span)) (fun record =>
        grantImage bound record.1.val (start+span-1) (Authority.traceGrant bound record.1.val (start+span-1) record.2.admission.grant))
  · simp [candidateChallenges,map_value]

/-- All records may pass their birth checks; only source shapes enter the quote. -/
def budget : Nat :=
  10 + 2*(Window.finish start span) + 17*(Authority.recordsAt bound start).length +
    5*(Authority.challengesAt bound (start+1)).length + 10*(Authority.recordsAt bound (start+span)).length +
    3*(Authority.challengesAt bound (Window.finish start span)).length
private theorem worlds_work : (worlds bound start span).work.length ≤ 2*(Window.finish start span) := by
  simpa only [worlds,List.length_range,Nat.mul_comm] using map_work (List.range (Window.finish start span))
    (fun ordinal => let image := Identity.occurrenceImage bound.source.code bound.source.input (ProgrammeHistory.visitAt bound.source.input ordinal).current
      ⟨image,[.worldRead ordinal image,.worldWrite ordinal]⟩) 2 (fun _ => Nat.le_refl _)
private theorem originals_work : (originals bound start span).work.length ≤ 17*(Authority.recordsAt bound start).length := by
  unfold originals
  apply (flatMap_work _ _ 17 ?_).trans (by omega)
  intro record;split <;> simp [grant]
private theorem candidates_work : (candidates bound start span).work.length ≤ 10*(Authority.recordsAt bound (start+span)).length := by
  unfold candidates
  apply (flatMap_work _ _ 10 ?_).trans (by omega)
  intro record;split <;> simp [grant]
private theorem originalChallenges_work : (originalChallenges bound start span).work.length ≤ 5*(Authority.challengesAt bound (start+1)).length := by
  unfold originalChallenges
  apply (map_work _ _ 5 (fun _ => Nat.le_refl _)).trans (by omega)
private theorem candidateChallenges_work : (candidateChallenges bound start span).work.length ≤ 3*(Authority.challengesAt bound (Window.finish start span)).length := by
  unfold candidateChallenges
  apply (map_work _ _ 3 (fun _ => Nat.le_refl _)).trans (by omega)
private theorem generated_work_bound : (generate bound start span).work.length ≤ budget bound start span := by
  have a := worlds_work bound start span
  have b := originals_work bound start span
  have c := originalChallenges_work bound start span
  have d := candidates_work bound start span
  have e := candidateChallenges_work bound start span
  simp only [generate,List.length_append,List.length_cons,List.length_nil,budget]
  omega
structure Compilation where
  private mk ::
  manifest : Manifest Party Good Port Technology Instrument
  work : List (Event Party Good Port Technology Instrument)
  exact : manifest = Window.manifest bound start span
  private generated : manifest = (generate bound start span).value ∧ work = (generate bound start span).work

def compile : Compilation bound start span :=
  let made := generate bound start span
  ⟨made.value,made.work,generated_exact bound start span,⟨rfl,rfl⟩⟩
theorem work_bound : (compile bound start span).work.length ≤ budget bound start span := generated_work_bound bound start span

private theorem finRange_values (n : Nat) : (List.finRange n).map (fun i => i.val) = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ_last,List.map_append,List.map_map,List.range_succ]
    simpa only [Function.comp_def,Fin.val_castSucc,List.map_cons,List.map_nil,Fin.val_last] using
      congrArg (fun items => items++[n]) ih
omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
private theorem map_reindex {α β γ : Type} (items : List α) (reindex : α → β)
    (produce : β → Result γ Party Good Port Technology Instrument) :
    map items (fun item => produce (reindex item)) = map (items.map reindex) produce := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [map,List.map_cons,ih]
private def worldsFrom (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) :
    Result (List (Identity.OccurrenceImage Party Good Port (Mandate.State Party Technology) Instrument)) Party Good Port Technology Instrument :=
  map (List.finRange (Window.finish start span)) fun ordinal =>
    let image := Identity.occurrenceImage bound.source.code bound.source.input (frames.visits ordinal).current
    ⟨image,[.worldRead ordinal.val image,.worldWrite ordinal.val]⟩
private theorem worldsFrom_exact (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) :
    worldsFrom bound start span frames = worlds bound start span := by
  simp only [worldsFrom,frames.visit_exact]
  rw [map_reindex (List.finRange (Window.finish start span)) (fun ordinal => ordinal.val)
    (fun ordinal => let image := Identity.occurrenceImage bound.source.code bound.source.input (ProgrammeHistory.visitAt bound.source.input ordinal).current; ⟨image,[.worldRead ordinal image,.worldWrite ordinal]⟩),finRange_values]
  rfl
private def generateFrom (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) :
    Result (Manifest Party Good Port Technology Instrument) Party Good Port Technology Instrument :=
  let world := worldsFrom bound start span frames
  let old := originals bound start span
  let oldChallenges := originalChallenges bound start span
  let fresh := candidates bound start span
  let freshChallenges := candidateChallenges bound start span
  ⟨⟨world.value,old.value,oldChallenges.value,fresh.value,freshChallenges.value⟩,
    [.field 0]++world.work++[.records start,.field 1]++old.work++
    [.challenges (start+1),.field 2]++oldChallenges.work++
    [.records (start+span),.field 3]++fresh.work++
    [.challenges (Window.finish start span),.field 4]++freshChallenges.work++[.assemble]⟩
private theorem generateFrom_exact (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) :
    generateFrom bound start span frames = generate bound start span := by
  simp only [generateFrom,generate,worldsFrom_exact]
def compileFrom (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) : Compilation bound start span :=
  let made := generateFrom bound start span frames
  ⟨made.value,made.work,by dsimp only [made];rw [generateFrom_exact];exact generated_exact bound start span,
    by dsimp only [made];rw [generateFrom_exact];exact ⟨rfl,rfl⟩⟩
theorem workFrom_bound (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) :
    (compileFrom bound start span frames).work.length ≤ budget bound start span := by
  simp only [compileFrom,generateFrom_exact]
  exact generated_work_bound bound start span

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeManifest
