import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Lawful
set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeInventory
open Institutions.Capitalism.Universal.Root
open Feedback.Authority.Trace
variable {Party Good Port Technology Instrument : Type}
abbrev Key := Lawful.Key Party Good Port Technology Instrument

/-- Typed reads and writes in the source-manifest census. Image construction and
    the internals of copying an opaque field remain upstream obligations. -/
inductive Event (Party Good Port Technology Instrument : Type) where
  | group (kind : Fin 4)
  | grantBirth (value : Nat)
  | grantProposal (value : ItemImage Party Good Port (Mandate.State Party Technology) Instrument)
  | grantAcceptance (value : ItemImage Party Good Port (Mandate.State Party Technology) Instrument)
  | grantInitial (value : GrantObligationImage Party Port)
  | challengeContext (original : Bool) (claim : ChallengeImage Party Good Port Technology Instrument)
  | challengeAdmission (value : ChallengeEventImage Party Good Port Technology Instrument)
  | challengeBearer (value : Identity.ActorImage Party Good Port (Mandate.State Party Technology) Instrument)
  | challengeAdmittedScope (value : Identity.OriginImage Party Good Port (Mandate.State Party Technology) Instrument)
  | challengeContent (value : ChallengeImage Party Good Port Technology Instrument)
  | challengeBeneficiary (value : TaskImage Party Good)
  | challengeScope (value : Identity.OriginImage Party Good Port (Mandate.State Party Technology) Instrument)
  | challengeLineage (value : Identity.OriginImage Party Good Port (Mandate.State Party Technology) Instrument)
  | constructed (key : Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  | admitted (key : Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  | lifecycle (live : Bool)
  | due (key : Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  | archived (key : Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  deriving DecidableEq

private structure Produced (Party Good Port Technology Instrument : Type) where
  inventory : Lawful.Inventory (Lawful.Key Party Good Port Technology Instrument)
  work : List (Event Party Good Port Technology Instrument)
local notation "Result" => Produced Party Good Port Technology Instrument
private def empty : Result := ⟨⟨[],[]⟩,[]⟩
private def join (left right : Result) : Result :=
  ⟨⟨left.inventory.admitted ++ right.inventory.admitted,left.inventory.due ++ right.inventory.due⟩,left.work ++ right.work⟩
private def prepend (events : List (Event Party Good Port Technology Instrument)) (made : Result) : Result :=
  ⟨made.inventory,events ++ made.work⟩
private def emit (key : Key (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (live : Bool)
    (reads : List (Event Party Good Port Technology Instrument)) : Result :=
  ⟨⟨[key],if live then [key] else []⟩,
    reads ++ [.constructed key,.admitted key,.lifecycle live] ++ [if live then .due key else .archived key]⟩
private def scan {α : Type} (produce : α → Result) : List α → Result
  | [] => empty
  | head::tail => join (produce head) (scan produce tail)

private def grant (original : Bool) (image : GrantImage Party Good Port Technology Instrument) : Result :=
  let key : Lawful.GrantKey Party Good Port Technology Instrument :=
    ⟨image.birth,image.proposal,image.acceptance,image.initial⟩
  emit (if original then .originalGrant key else .candidateGrant key) true
    [.grantBirth image.birth,.grantProposal image.proposal,.grantAcceptance image.acceptance,.grantInitial image.initial]
private def challenge (original : Bool) (claim : ChallengeImage Party Good Port Technology Instrument)
    (slot : ChallengeSlotImage Party Good Port Technology Instrument) : Result :=
  let (obligation,live) := match slot with
    | .live obligation => (obligation,true)
    | .terminal obligation _ => (obligation,false)
  let key : Lawful.ChallengeKey Party Good Port Technology Instrument :=
    ⟨obligation.admission,obligation.admittedBearer,obligation.admittedScope,obligation.content,
      obligation.beneficiary,obligation.scope,obligation.lineage⟩
  emit (if original then .originalChallenge claim key else .candidateChallenge claim key) live
    [.challengeAdmission obligation.admission,.challengeBearer obligation.admittedBearer,
     .challengeAdmittedScope obligation.admittedScope,.challengeContent obligation.content,
     .challengeBeneficiary obligation.beneficiary,.challengeScope obligation.scope,.challengeLineage obligation.lineage]
private def challenges (original : Bool) (claim : ChallengeImage Party Good Port Technology Instrument)
    (state : ChallengeStateImage Party Good Port Technology Instrument) : Result :=
  prepend [.challengeContext original claim] (scan (challenge original claim) state.slots)
private def generate (manifest : Manifest Party Good Port Technology Instrument) : Result :=
  join (prepend [.group 0] (scan (fun row => grant true row.2) manifest.originalGrants))
    (join (prepend [.group 1] (scan (grant false) manifest.candidateGrants))
      (join (prepend [.group 2] (scan (fun row => challenges true row.1 row.2.2) manifest.originalChallenges))
        (prepend [.group 3] (scan (fun row => challenges false row.1 row.2) manifest.candidateChallenges))))

private theorem scan_admitted {α : Type} (produce : α → Result) (items : List α) :
    (scan produce items).inventory.admitted = items.flatMap (fun item => (produce item).inventory.admitted) := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [scan,join,List.flatMap_cons,ih]
private theorem scan_due {α : Type} (produce : α → Result) (items : List α) :
    (scan produce items).inventory.due = items.flatMap (fun item => (produce item).inventory.due) := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [scan,join,List.flatMap_cons,ih]
private theorem scan_work {α : Type} (produce : α → Result) (items : List α) :
    (scan produce items).work.length = (items.map (fun item => (produce item).work.length)).sum := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [scan,join,List.length_append,List.map_cons,List.sum_cons,ih]
private theorem challenge_admitted (original : Bool) (claim : ChallengeImage Party Good Port Technology Instrument)
    (state : ChallengeStateImage Party Good Port Technology Instrument) :
    (challenges original claim state).inventory.admitted =
      (Lawful.challengeRows (if original then .originalChallenge claim else .candidateChallenge claim) state).map Prod.fst := by
  cases original <;> simp only [challenges,prepend,scan_admitted,Lawful.challengeRows,List.map_map]
  all_goals induction state.slots with
    | nil => rfl
    | cons slot tail ih => cases slot <;> simp_all [challenge,emit,Lawful.challengeKey]
private theorem challenge_due (original : Bool) (claim : ChallengeImage Party Good Port Technology Instrument)
    (state : ChallengeStateImage Party Good Port Technology Instrument) :
    (challenges original claim state).inventory.due =
      ((Lawful.challengeRows (if original then .originalChallenge claim else .candidateChallenge claim) state).filter Prod.snd).map Prod.fst := by
  cases original <;> simp only [challenges,prepend,scan_due,Lawful.challengeRows,List.filter_map]
  all_goals induction state.slots with
    | nil => rfl
    | cons slot tail ih => cases slot <;> simp_all [challenge,emit,Lawful.challengeKey]

@[simp] private theorem flatMap_one {α β : Type} (items : List α) (f : α → β) :
    items.flatMap (fun item => [f item]) = items.map f := by
  induction items <;> simp_all

private theorem inventory_eq {a b : Lawful.Inventory (Lawful.Key Party Good Port Technology Instrument)}
    (admitted : a.admitted = b.admitted) (due : a.due = b.due) : a = b := by
  cases a;cases b;simp_all

/-- Both outputs are generated jointly; terminal admissions stay in the archive. -/
private theorem generate_exact (manifest : Manifest Party Good Port Technology Instrument) :
    (generate manifest).inventory = Lawful.inventory manifest := by
  apply inventory_eq <;>
    simp only [generate,join,prepend,scan_admitted,scan_due,Lawful.inventory,Lawful.rows,
      List.map_append,List.filter_append,List.map_flatMap,List.filter_flatMap,List.append_assoc]
  · congr 1
    · simp [grant,emit,Lawful.grantKey]
    · congr 1
      · simp [grant,emit,Lawful.grantKey]
      · congr 1 <;> congr 1 <;> funext row <;> apply challenge_admitted
  · congr 1
    · simp [grant,emit,Lawful.grantKey,List.filter_map,Function.comp_def]
    · congr 1
      · simp [grant,emit,Lawful.grantKey,List.filter_map,Function.comp_def]
      · congr 1 <;> congr 1 <;> funext row <;> apply challenge_due

/-- A shape-only bound avoids constructing identities while quoting a census. -/
def rowCount (manifest : Manifest Party Good Port Technology Instrument) : Nat :=
  manifest.originalGrants.length + manifest.candidateGrants.length +
    (manifest.originalChallenges.map (fun row => row.2.2.slots.length)).sum +
    (manifest.candidateChallenges.map (fun row => row.2.slots.length)).sum

theorem admitted_length (manifest : Manifest Party Good Port Technology Instrument) :
    (Lawful.inventory manifest).admitted.length = rowCount manifest := by
  simp [Lawful.inventory,Lawful.rows,Lawful.challengeRows,List.length_flatMap,rowCount,Nat.add_assoc]

theorem due_length_bound (manifest : Manifest Party Good Port Technology Instrument) :
    (Lawful.inventory manifest).due.length ≤ rowCount manifest := by
  rw [← admitted_length manifest]
  simp only [Lawful.inventory,List.length_map]
  exact List.length_filter_le _ _

/-- Fixed instruction count from source list shapes, before either comparison answer. -/
def budget (manifest : Manifest Party Good Port Technology Instrument) : Nat :=
  4 + 8 * (manifest.originalGrants.length + manifest.candidateGrants.length) +
    manifest.originalChallenges.length + manifest.candidateChallenges.length +
    11 * ((manifest.originalChallenges.map (fun row => row.2.2.slots.length)).sum +
      (manifest.candidateChallenges.map (fun row => row.2.slots.length)).sum)
private theorem challenge_work (original : Bool) (claim : ChallengeImage Party Good Port Technology Instrument)
    (state : ChallengeStateImage Party Good Port Technology Instrument) :
    (challenges original claim state).work.length = 1 + 11 * state.slots.length := by
  simp only [challenges,prepend,List.length_append,List.length_singleton,scan_work]
  have each : ∀ slot : ChallengeSlotImage Party Good Port Technology Instrument,
      (challenge original claim slot).work.length = 11 := by
    intro slot; cases slot <;> simp [challenge,emit]
  simp [each,Nat.mul_comm]
private theorem generate_work (manifest : Manifest Party Good Port Technology Instrument) :
    (generate manifest).work.length = budget manifest := by
  simp only [generate,join,prepend,List.length_append,List.length_singleton,scan_work]
  simp only [grant,emit,List.length_append,List.length_cons,List.length_nil]
  simp only [challenge_work]
  simp [budget,List.sum_map_add,List.sum_map_mul_left]
  omega

structure Compilation (manifest : Manifest Party Good Port Technology Instrument) where
  private mk ::
  inventory : Lawful.Inventory (Lawful.Key Party Good Port Technology Instrument)
  work : List (Event Party Good Port Technology Instrument)
  exact : inventory = Lawful.inventory manifest
  private generated : inventory = (generate manifest).inventory ∧ work = (generate manifest).work

def compile (manifest : Manifest Party Good Port Technology Instrument) : Compilation manifest :=
  let made := generate manifest
  ⟨made.inventory,made.work,generate_exact manifest,⟨rfl,rfl⟩⟩
theorem work_exact (manifest : Manifest Party Good Port Technology Instrument) :
    (compile manifest).work.length = budget manifest := generate_work manifest
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeInventory
