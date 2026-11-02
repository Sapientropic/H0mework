import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Bound.Body.Source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.BodySource
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} (prepared : Prepared input)
local infixl:65 " ⊞ " => fun a b : Nat => a+b+1
local infixl:70 " ⊠ " => fun a b : Nat => a+b+1

namespace Present

def unitLists {α : Type} (left right : List α) := BodySource.lists (fun _ _ => 1) left right

def profile (new previous : Settlement.Profile P G O (Mandate.State P T) I) : Nat :=
  unitLists new.originalDebts previous.originalDebts ⊞ unitLists new.newbornDebts previous.newbornDebts ⊞
  BodySource.lists unitLists new.rights previous.rights ⊞ unitLists new.uncoveredClaims previous.uncoveredClaims ⊞
  unitLists new.firstServices previous.firstServices ⊞ 1

def slotSum {α β : Type} (slots : α → List β) : List α → Nat
  | [] => 2
  | row::rest => BodySource.length (slots row) + slotSum slots rest + 2

def rowCount (manifest : Feedback.Authority.Trace.Manifest P G O T I) : Nat :=
  BodySource.length manifest.originalGrants ⊞ BodySource.length manifest.candidateGrants ⊞
  slotSum (fun row => row.2.2.slots) manifest.originalChallenges ⊞ slotSum (fun row => row.2.slots) manifest.candidateChallenges

def inventory (manifest : Feedback.Authority.Trace.Manifest P G O T I) : Nat :=
  1 ⊞ 1 ⊠ (BodySource.length manifest.originalGrants ⊞ BodySource.length manifest.candidateGrants) ⊞
  BodySource.length manifest.originalChallenges ⊞ BodySource.length manifest.candidateChallenges ⊞
  1 ⊠ (slotSum (fun row => row.2.2.slots) manifest.originalChallenges ⊞ slotSum (fun row => row.2.slots) manifest.candidateChallenges)

def subperm (left right : Nat) := left ⊠ (1 ⊠ (left ⊞ right) ⊞ 1)
def inventoryPair (new previous : Feedback.Authority.Trace.Manifest P G O T I) :=
  inventory new ⊞ inventory previous ⊞ (subperm (rowCount previous) (rowCount new) ⊞ 1 ⊞ subperm (rowCount new) (rowCount previous))

variable {actual : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {driver : Feedback.Input actual.source.code}
def present (cursor : Cursor actual driver) (new previous : Evaluation cursor.source.val.code) :=
  1 ⊞ profile new.profile previous.profile ⊞ inventoryPair new.native previous.native ⊞
  1 ⊠ BodySource.length (Window.axes cursor.model cursor.depth)

theorem unitLists_exact {α : Type} (left right : List α) :
    (Budget.PresentShape.unitLists prepared left right).work.length = unitLists left right :=
  BodySource.lists_exact prepared _ _ _ (fun _ _ => rfl) _ _

theorem profile_exact (new previous : Settlement.Profile P G O (Mandate.State P T) I) :
    (Budget.PresentShape.profile prepared new previous).work.length = profile new previous := by
  unfold Budget.PresentShape.profile profile
  repeat' first | rw [BodySource.plus_units prepared] | rw [unitLists_exact prepared] |
    rw [BodySource.lists_exact prepared _ _ _ (unitLists_exact prepared)] | rw [BodySource.literal_units prepared]

theorem slotSum_exact {α β : Type} (slots : α → List β) (rows : List α) :
    (Budget.PresentShape.slotSum prepared slots rows).work.length = slotSum slots rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    rw [Budget.PresentShape.slotSum,BodySource.mark_units prepared,BodySource.plus_units prepared,BodySource.length_exact prepared,ih]
    simp only [slotSum]

theorem rowCount_exact (manifest : Feedback.Authority.Trace.Manifest P G O T I) :
    (Budget.PresentShape.rowCount prepared manifest).work.length = rowCount manifest := by
  unfold Budget.PresentShape.rowCount rowCount
  repeat' first | rw [BodySource.plus_units prepared] | rw [BodySource.length_exact prepared] | rw [slotSum_exact prepared]

theorem inventory_exact (manifest : Feedback.Authority.Trace.Manifest P G O T I) :
    (Budget.PresentShape.inventory prepared manifest).work.length = inventory manifest := by
  unfold Budget.PresentShape.inventory inventory
  repeat' first | rw [BodySource.plus_units prepared] | rw [BodySource.times_units prepared] |
    rw [BodySource.length_exact prepared] | rw [slotSum_exact prepared] | rw [BodySource.literal_units prepared]

theorem subperm_exact {a b : Nat} (left : Unit → Budget.Run prepared a) (right : Unit → Budget.Run prepared b)
    (x y : Nat) (lx : (left ()).work.length = x) (ry : (right ()).work.length = y) :
    (Budget.PresentShape.subperm prepared left right).work.length = subperm x y := by
  unfold Budget.PresentShape.subperm subperm
  repeat' first | rw [BodySource.plus_units prepared] | rw [BodySource.times_units prepared] | rw [BodySource.literal_units prepared] | rw [lx] | rw [ry]

theorem inventoryPair_exact (new previous : Feedback.Authority.Trace.Manifest P G O T I) :
    (Budget.PresentShape.inventoryPair prepared new previous).work.length = inventoryPair new previous := by
  unfold Budget.PresentShape.inventoryPair inventoryPair
  repeat' first | rw [BodySource.plus_units prepared] | rw [BodySource.literal_units prepared] | rw [inventory_exact prepared] |
    rw [subperm_exact prepared _ _ _ _ (rowCount_exact prepared _) (rowCount_exact prepared _)]

theorem present_exact (cursor : Cursor actual driver) (new previous : Evaluation cursor.source.val.code) :
    (Budget.PresentShape.present prepared cursor new previous).work.length = present cursor new previous := by
  unfold Budget.PresentShape.present present
  repeat' first | rw [BodySource.plus_units prepared] | rw [BodySource.times_units prepared] | rw [BodySource.literal_units prepared] |
    rw [profile_exact prepared] | rw [inventoryPair_exact prepared] | rw [BodySource.length_exact prepared]
end Present

namespace Source
open private SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.NativeSourceShape.acquired SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.NativeSourceShape.withNat from H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget

theorem acquired_units {n : Nat} (event : Budget.Event prepared) (valid : event.Valid prepared) (made : Budget.Run prepared n) :
    (SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.NativeSourceShape.acquired event valid made).work.length = made.work.length+1 := by
  change (event::made.work).length = _
  simp only [List.length_cons]
theorem withNat_units {n : Nat} (earlier : Budget.Run prepared n) (cost : Nat → Nat)
    (step : (i : Nat) → Budget.Run prepared (cost i)) :
    (SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.NativeSourceShape.withNat earlier cost step).work.length = earlier.work.length+(step n).work.length := by
  change (earlier.work ++ (step earlier.value).work).length = _
  rw [List.length_append,earlier.exact]

def payload (request : Request P G O (Mandate.State P T) I) : Nat :=
  match request.operation with | .use _ goods _ => BodySource.length goods+1 | _ => 2

def validity (law : RawLaw P G O (Mandate.State P T) I) (current : RawCurrent P G (Mandate.State P T) I)
    (request : Request P G O (Mandate.State P T) I) : Nat :=
  (BodySource.length (law.debit current request)+1) + (BodySource.length (law.credit current request)+1) +
  (BodySource.length (law.requiredPorts current request)+1) + (BodySource.length request.consents+1) + (payload request+1) +
  ((1 ⊞ 1) ⊠ 1 ⊞ (1 ⊠ 1 ⊞ 1) ⊠ 1 ⊞ 1 ⊠ 1 ⊞ 1 ⊠ 1 ⊞ 1)

def instruction (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (origin : Financial.InstructionOrigin source) :=
  match origin.instruction? source with | none => 3 | some item => validity source.law item.before item.request+4

def movement (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (origin : Financial.InstructionOrigin source)
    (before : (Financial.process source).GeneratedState) :=
  BodySource.length before.current.slots + instruction source origin+6

def frameFold (source : ProgrammeSource.Input P G O (Mandate.State P T) I) :
    List (Financial.InstructionOrigin source) → (Financial.process source).GeneratedState → Nat
  | [],_ => 2
  | origin::rest,before => movement source origin before +
      frameFold source rest ((Financial.consume source origin before).next source)+5

def frames (source : ProgrammeSource.Input P G O (Mandate.State P T) I) : Nat → Nat
  | 0 => 2
  | count+1 => frames source count + frameFold source
      (Financial.inventoryAt source (Institutions.Capitalism.Universal.Root.ProgrammeHistory.visitAt source count)) (Financial.accountAt source count)+7

variable (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I))
def profile (start span : Nat) :=
  (3+(BodySource.length (Financial.accountAt bound.source.input (start+1)).current.slots+1)) +
  (5+(BodySource.length (Financial.accountAt bound.source.input (Window.finish start span)).current.slots+1)) +
  (BodySource.length bound.source.code.parties+1) + (BodySource.length bound.source.code.instruments+1) +
  (BodySource.length bound.source.code.task.slots+1) +
  (1 ⊞ 1 ⊠ 1 ⊞ 1 ⊠ 1 ⊞ 1 ⊠ (1 ⊞ 1 ⊠ 1) ⊞ 1 ⊠ (1 ⊠ (1 ⊠ 1)) ⊞ 1 ⊠ 1)

def manifest (start span : Nat) :=
  5 + (BodySource.length (Authority.recordsAt bound start)+1) +
  (3+(BodySource.length (Authority.challengesAt bound (start+1))+1)) +
  (3+(BodySource.length (Authority.recordsAt bound (start+span))+1)) +
  (5+(BodySource.length (Authority.challengesAt bound (Window.finish start span))+1)) +
  (1 ⊞ 1 ⊠ 1 ⊞ 1 ⊠ 1 ⊞ 1 ⊠ 1 ⊞ 1 ⊠ 1 ⊞ 1 ⊠ 1)

def evaluation (start span : Nat) := frames bound.source.input (Window.finish start span) + profile bound start span + manifest bound start span+7

variable {bound}
theorem payload_exact (request : Request P G O (Mandate.State P T) I) :
    (Budget.NativeSourceShape.payload prepared request).work.length = payload request := by
  rcases request with ⟨signer,consents,purpose,gates,operation⟩
  cases operation with
  | use bearer goods kind =>
    with_unfolding_all change (Budget.mark .operation (Budget.length (prepared := prepared) goods)).work.length = BodySource.length goods+1
    rw [BodySource.mark_units prepared,BodySource.length_exact prepared]
  | _ => with_unfolding_all rfl


theorem validity_exact (law : RawLaw P G O (Mandate.State P T) I) (current : RawCurrent P G (Mandate.State P T) I)
    (request : Request P G O (Mandate.State P T) I) :
    (Budget.NativeSourceShape.validity prepared law current request).work.length = validity law current request := by
  unfold Budget.NativeSourceShape.validity validity
  simp only [Budget.retain,List.length_append]
  repeat' first | rw [BodySource.plus_units prepared] | rw [BodySource.times_units prepared] |
    rw [BodySource.literal_units prepared] | rw [acquired_units prepared] | rw [BodySource.length_exact prepared] | rw [payload_exact prepared]
  simp only [Budget.borrow,List.length_singleton]
  omega

theorem cast_units {a b : Nat} (same : a = b) (made : Budget.Run prepared b) :
    ((congrArg (Budget.Run prepared) same).mpr made).work.length = made.work.length := by
  cases same
  rfl

theorem instruction_exact (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (origin : Financial.InstructionOrigin source) :
    (Budget.NativeSourceShape.instruction prepared source origin).work.length = instruction source origin := by
  unfold Budget.NativeSourceShape.instruction instruction
  rw [acquired_units prepared]
  split
  · rename_i actual
    simp only [actual]
    have size : Financial.InstructionSource.budget source origin = 1 := by simp only [Financial.InstructionSource.budget,actual]
    change ((congrArg (Budget.Run prepared) size).mpr (Budget.mark .nativeRow (Budget.lit 1))).work.length+1 = 3
    rw [cast_units prepared size]
    rfl
  · rename_i item actual
    simp only [actual]
    have size : Financial.InstructionSource.budget source origin = RawLaw.ValiditySource.budget source.law item.before item.request+2 := by
      simp only [Financial.InstructionSource.budget,actual]
    change ((congrArg (Budget.Run prepared) size).mpr (Budget.mark .nativeRow (Budget.plus
      (Budget.NativeSourceShape.validity prepared source.law item.before item.request) (Budget.lit 2)))).work.length+1 = _
    rw [cast_units prepared size,BodySource.mark_units prepared,BodySource.plus_units prepared,BodySource.literal_units prepared,validity_exact prepared]

theorem movement_exact (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (origin : Financial.InstructionOrigin source)
    (before : (Financial.process source).GeneratedState) :
    (Budget.NativeSourceShape.movement prepared source origin before).work.length = movement source origin before := by
  unfold Budget.NativeSourceShape.movement movement
  repeat' first | rw [acquired_units prepared] | rw [BodySource.plus_units prepared] | rw [BodySource.times_units prepared] |
    rw [BodySource.literal_units prepared] | rw [BodySource.length_exact prepared] | rw [instruction_exact prepared]
  all_goals omega

theorem frameFold_exact (source : ProgrammeSource.Input P G O (Mandate.State P T) I)
    (origins : List (Financial.InstructionOrigin source)) (before : (Financial.process source).GeneratedState) :
    (Budget.NativeSourceShape.frameFold prepared source origins before).work.length = frameFold source origins before := by
  induction origins generalizing before with
  | nil => rfl
  | cons origin rest ih =>
    rw [Budget.NativeSourceShape.frameFold,BodySource.mark_units prepared]
    repeat' first | rw [acquired_units prepared] | rw [BodySource.plus_units prepared] |
      rw [BodySource.literal_units prepared] | rw [movement_exact prepared] | rw [ih]
    simp only [frameFold];omega

theorem frames_exact (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (count : Nat) :
    (Budget.NativeSourceShape.frames prepared source count).work.length = frames source count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [Budget.NativeSourceShape.frames,BodySource.mark_units prepared]
    repeat' first | rw [acquired_units prepared] | rw [BodySource.plus_units prepared] |
      rw [BodySource.literal_units prepared] | rw [frameFold_exact prepared] | rw [ih]
    simp only [frames];omega

theorem finish_exact (start span : Nat) : (Budget.NativeSourceShape.finish prepared start span).work.length = 5 := by
  unfold Budget.NativeSourceShape.finish
  repeat' first | rw [BodySource.plus_units prepared] | rw [BodySource.literal_units prepared]

theorem profile_exact (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I))
    (start span : Nat) : (Budget.NativeSourceShape.profile prepared bound start span).work.length = profile bound start span := by
  unfold Budget.NativeSourceShape.profile profile
  simp only [Budget.retain,List.length_append]
  repeat' first | rw [withNat_units prepared] | rw [acquired_units prepared] | rw [BodySource.plus_units prepared] |
    rw [BodySource.times_units prepared] | rw [BodySource.literal_units prepared] | rw [finish_exact prepared] | rw [BodySource.length_exact prepared]
  simp only [Budget.borrow,List.length_singleton]
  omega

theorem manifest_exact (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I))
    (start span : Nat) : (Budget.NativeSourceShape.manifest prepared bound start span).work.length = manifest bound start span := by
  unfold Budget.NativeSourceShape.manifest manifest
  simp only [Budget.retain,List.length_append]
  repeat' first | rw [withNat_units prepared] | rw [acquired_units prepared] | rw [BodySource.plus_units prepared] |
    rw [BodySource.times_units prepared] | rw [BodySource.literal_units prepared] | rw [finish_exact prepared] | rw [BodySource.length_exact prepared]
  simp only [Budget.borrow,List.length_singleton]
  omega

theorem evaluation_exact (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I))
    (start span : Nat) : (Budget.NativeSourceShape.evaluation prepared bound start span).work.length = evaluation bound start span := by
  unfold Budget.NativeSourceShape.evaluation evaluation
  repeat' first | rw [BodySource.plus_units prepared] | rw [withNat_units prepared] | rw [finish_exact prepared] |
    rw [profile_exact prepared] | rw [manifest_exact prepared] | rw [frames_exact prepared]
  omega

end Source
namespace FutureShape
variable {actual : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {driver : Feedback.Input actual.source.code}
def report (cursor : Cursor actual driver) (new previous : Future.Recovery.Assessment.Report cursor.model) :=
  1 ⊞ Present.profile new.evaluation.profile previous.evaluation.profile ⊞
  Present.inventoryPair new.evaluation.native previous.evaluation.native ⊞ 1 ⊠ BodySource.length (Window.axes cursor.model cursor.depth)
def comparison (cursor : Cursor actual driver) :
    Option (Future.Recovery.Assessment.Report cursor.model) → Option (Future.Recovery.Assessment.Report cursor.model) → Nat
  | some current,some original => report cursor current original+3
  | none,none | some _,none | none,some _ => 2

theorem report_exact (cursor : Cursor actual driver) (new previous : Future.Recovery.Assessment.Report cursor.model) :
    (Budget.NativeFutureShape.report prepared cursor new previous).work.length = report cursor new previous := by
  unfold Budget.NativeFutureShape.report report
  repeat' first | rw [BodySource.plus_units prepared] | rw [BodySource.times_units prepared] | rw [BodySource.literal_units prepared] |
    rw [Present.profile_exact prepared] | rw [Present.inventoryPair_exact prepared] | rw [BodySource.length_exact prepared]

theorem comparison_exact (cursor : Cursor actual driver)
    (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) :
    (Budget.NativeFutureShape.comparison prepared cursor new previous).work.length = comparison cursor new previous := by
  cases new <;> cases previous
  all_goals
    unfold Budget.NativeFutureShape.comparison comparison
    repeat' first | rw [BodySource.mark_units prepared] | rw [BodySource.plus_units prepared] |
      rw [BodySource.literal_units prepared] | rw [report_exact prepared]
end FutureShape

namespace BenefitShape
variable {actual : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {driver : Feedback.Input actual.source.code}
def inventoryDue (new previous : Feedback.Authority.Trace.Manifest P G O T I) :=
  Present.inventory new ⊞ Present.inventory previous ⊞ Present.subperm (Present.rowCount new) (Present.rowCount previous)
def present (cursor : Cursor actual driver) (new previous : Evaluation cursor.source.val.code) :=
  1 ⊞ inventoryDue new.native previous.native ⊞ 1 ⊠ BodySource.length (Window.axes cursor.model cursor.depth)
def future (cursor : Cursor actual driver) :
    Option (Future.Recovery.Assessment.Report cursor.model) → Option (Future.Recovery.Assessment.Report cursor.model) → Nat
  | some current,some original => present cursor current.evaluation original.evaluation+3
  | none,none | some _,none | none,some _ => 2

theorem inventoryDue_exact (new previous : Feedback.Authority.Trace.Manifest P G O T I) :
    (Budget.NativeBenefitShape.inventoryDue prepared new previous).work.length = inventoryDue new previous := by
  unfold Budget.NativeBenefitShape.inventoryDue inventoryDue
  repeat' first | rw [BodySource.plus_units prepared] | rw [Present.inventory_exact prepared] |
    rw [Present.subperm_exact prepared _ _ _ _ (Present.rowCount_exact prepared _) (Present.rowCount_exact prepared _)]

theorem present_exact (cursor : Cursor actual driver) (new previous : Evaluation cursor.source.val.code) :
    (Budget.NativeBenefitShape.present prepared cursor new previous).work.length = present cursor new previous := by
  unfold Budget.NativeBenefitShape.present present
  repeat' first | rw [BodySource.plus_units prepared] | rw [BodySource.times_units prepared] | rw [BodySource.literal_units prepared] |
    rw [inventoryDue_exact prepared] | rw [BodySource.length_exact prepared]

theorem future_exact (cursor : Cursor actual driver)
    (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) :
    (Budget.NativeBenefitShape.future prepared cursor new previous).work.length = future cursor new previous := by
  cases new <;> cases previous
  all_goals
    unfold Budget.NativeBenefitShape.future future
    repeat' first | rw [BodySource.mark_units prepared] | rw [BodySource.plus_units prepared] |
      rw [BodySource.literal_units prepared] | rw [present_exact prepared]
end BenefitShape

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.BodySource
