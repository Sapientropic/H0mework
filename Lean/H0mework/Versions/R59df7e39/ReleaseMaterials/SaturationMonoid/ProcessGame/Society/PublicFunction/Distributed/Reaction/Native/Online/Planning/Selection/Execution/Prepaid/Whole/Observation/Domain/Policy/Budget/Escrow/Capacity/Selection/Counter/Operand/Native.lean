import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Operand.Core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Expand
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
 {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
 {input : Input seed} {prepared : Prepared input} {snapshot : Snapshot prepared}
 {catalogue : Catalogue snapshot} {pool : Comparison.Pool catalogue}
namespace Count
local infixl:65 " ⊞ " => fun a b : Formula => a+b+1
local infixl:70 " ⊠ " => fun a b : Formula => a+b+1
namespace Present
def unitLists {α : Type} (left right : List α) : Formula := Count.lists (fun _ _ => 1) left right

def profile (new previous : Settlement.Profile P G O (Mandate.State P T) I) : Formula :=
  unitLists new.originalDebts previous.originalDebts ⊞ unitLists new.newbornDebts previous.newbornDebts ⊞
  Count.lists unitLists new.rights previous.rights ⊞ unitLists new.uncoveredClaims previous.uncoveredClaims ⊞
  unitLists new.firstServices previous.firstServices ⊞ 1

def slotSum {α β : Type} (slots : α → List β) : List α → Formula
  | [] => 2
  | row::rest => Count.length (slots row) + slotSum slots rest + 2

def rowCount (manifest : Feedback.Authority.Trace.Manifest P G O T I) : Formula :=
  Count.length manifest.originalGrants ⊞ Count.length manifest.candidateGrants ⊞
  slotSum (fun row => row.2.2.slots) manifest.originalChallenges ⊞ slotSum (fun row => row.2.slots) manifest.candidateChallenges

def inventory (manifest : Feedback.Authority.Trace.Manifest P G O T I) : Formula :=
  1 ⊞ 1 ⊠ (Count.length manifest.originalGrants ⊞ Count.length manifest.candidateGrants) ⊞
  Count.length manifest.originalChallenges ⊞ Count.length manifest.candidateChallenges ⊞
  1 ⊠ (slotSum (fun row => row.2.2.slots) manifest.originalChallenges ⊞ slotSum (fun row => row.2.slots) manifest.candidateChallenges)

def subperm (left right : Formula) : Formula := left ⊠ (1 ⊠ (left ⊞ right) ⊞ 1)

def inventoryPair (new previous : Feedback.Authority.Trace.Manifest P G O T I) : Formula :=
  inventory new ⊞ inventory previous ⊞ (subperm (rowCount previous) (rowCount new) ⊞ 1 ⊞ subperm (rowCount new) (rowCount previous))

variable {actual : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {driver : Feedback.Input actual.source.code}
def present (cursor : Cursor actual driver) (new previous : Evaluation cursor.source.val.code) : Formula :=
  1 ⊞ profile new.profile previous.profile ⊞ inventoryPair new.native previous.native ⊞
  1 ⊠ Count.length (Window.axes cursor.model cursor.depth)

theorem unitLists_value {α : Type} (left right : List α) : (unitLists left right).value = BodySource.Present.unitLists left right := Count.lists_value _ _ _
omit [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I] in
theorem profile_value (new previous : Settlement.Profile P G O (Mandate.State P T) I) : (profile new previous).value = BodySource.Present.profile new previous := by
  simp only [profile,BodySource.Present.profile,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,unitLists_value,Count.lists_value]
theorem slotSum_value {α β : Type} (slots : α → List β) (rows : List α) : (slotSum slots rows).value = BodySource.Present.slotSum slots rows := by
  induction rows with
  | nil => rfl
  | cons head tail ih => simp only [slotSum,BodySource.Present.slotSum,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Count.length_value,ih]
omit [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I] in
theorem rowCount_value (manifest : Feedback.Authority.Trace.Manifest P G O T I) : (rowCount manifest).value = BodySource.Present.rowCount manifest := by
  simp only [rowCount,BodySource.Present.rowCount,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Count.length_value,slotSum_value]
omit [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I] in
theorem inventory_value (manifest : Feedback.Authority.Trace.Manifest P G O T I) : (inventory manifest).value = BodySource.Present.inventory manifest := by
  simp only [inventory,BodySource.Present.inventory,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Count.length_value,slotSum_value]
theorem subperm_value (left right : Formula) : (subperm left right).value = BodySource.Present.subperm left.value right.value := by
  simp only [subperm,BodySource.Present.subperm,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value]
omit [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I] in
theorem inventoryPair_value (new previous : Feedback.Authority.Trace.Manifest P G O T I) : (inventoryPair new previous).value = BodySource.Present.inventoryPair new previous := by
  simp only [inventoryPair,BodySource.Present.inventoryPair,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,inventory_value,subperm_value,rowCount_value]
theorem present_value (cursor : Cursor actual driver) (new previous : Evaluation cursor.source.val.code) : (present cursor new previous).value = BodySource.Present.present cursor new previous := by
  simp only [present,BodySource.Present.present,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,profile_value,inventoryPair_value,Count.length_value]
end Present
namespace Source
def payload (request : Request P G O (Mandate.State P T) I) : Formula :=
  match request.operation with | .use _ goods _ => Count.length goods+1 | _ => 2

def validity (law : RawLaw P G O (Mandate.State P T) I) (current : RawCurrent P G (Mandate.State P T) I)
    (request : Request P G O (Mandate.State P T) I) : Formula :=
  (Count.length (law.debit current request)+1) + (Count.length (law.credit current request)+1) +
  (Count.length (law.requiredPorts current request)+1) + (Count.length request.consents+1) + (payload request+1) +
  ((1 ⊞ 1) ⊠ 1 ⊞ (1 ⊠ 1 ⊞ 1) ⊠ 1 ⊞ 1 ⊠ 1 ⊞ 1 ⊠ 1 ⊞ 1)

def instruction (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (origin : Financial.InstructionOrigin source) : Formula :=
  match origin.instruction? source with | none => 3 | some item => validity source.law item.before item.request+4

def movement (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (origin : Financial.InstructionOrigin source)
    (before : (Financial.process source).GeneratedState) : Formula :=
  Count.length before.current.slots + instruction source origin+6

def frameFold (source : ProgrammeSource.Input P G O (Mandate.State P T) I) :
    List (Financial.InstructionOrigin source) → (Financial.process source).GeneratedState → Formula
  | [],_ => 2
  | origin::rest,before => movement source origin before +
      frameFold source rest ((Financial.consume source origin before).next source)+5

def frames (source : ProgrammeSource.Input P G O (Mandate.State P T) I) : Nat → Formula
  | 0 => 2
  | count+1 => frames source count + frameFold source
      (Financial.inventoryAt source (Institutions.Capitalism.Universal.Root.ProgrammeHistory.visitAt source count)) (Financial.accountAt source count)+7

variable (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I))
def profile (start span : Nat) : Formula :=
  (3+(Count.length (Financial.accountAt bound.source.input (start+1)).current.slots+1)) +
  (5+(Count.length (Financial.accountAt bound.source.input (Window.finish start span)).current.slots+1)) +
  (Count.length bound.source.code.parties+1) + (Count.length bound.source.code.instruments+1) +
  (Count.length bound.source.code.task.slots+1) +
  (1 ⊞ 1 ⊠ 1 ⊞ 1 ⊠ 1 ⊞ 1 ⊠ (1 ⊞ 1 ⊠ 1) ⊞ 1 ⊠ (1 ⊠ (1 ⊠ 1)) ⊞ 1 ⊠ 1)

def manifest (start span : Nat) : Formula :=
  5 + (Count.length (Authority.recordsAt bound start)+1) +
  (3+(Count.length (Authority.challengesAt bound (start+1))+1)) +
  (3+(Count.length (Authority.recordsAt bound (start+span))+1)) +
  (5+(Count.length (Authority.challengesAt bound (Window.finish start span))+1)) +
  (1 ⊞ 1 ⊠ 1 ⊞ 1 ⊠ 1 ⊞ 1 ⊠ 1 ⊞ 1 ⊠ 1 ⊞ 1 ⊠ 1)

def evaluation (start span : Nat) : Formula := frames bound.source.input (Window.finish start span) + profile bound start span + manifest bound start span+7

variable {bound}
omit [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I] in
theorem payload_value (request : Request P G O (Mandate.State P T) I) : (payload request).value = BodySource.Source.payload request := by
  rcases request with ⟨signer,consents,purpose,gates,operation⟩
  cases operation <;> simp only [payload,BodySource.Source.payload,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Count.length_value]
omit [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I] in
theorem validity_value (law : RawLaw P G O (Mandate.State P T) I) (current : RawCurrent P G (Mandate.State P T) I)
    (request : Request P G O (Mandate.State P T) I) : (validity law current request).value = BodySource.Source.validity law current request := by
  simp only [validity,BodySource.Source.validity,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Count.length_value,payload_value]
omit [DecidableEq O] [DecidableEq T] in
theorem instruction_value (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (origin : Financial.InstructionOrigin source) :
    (instruction source origin).value = BodySource.Source.instruction source origin := by
  unfold instruction BodySource.Source.instruction
  split <;> simp_all only [add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,validity_value]
omit [DecidableEq T] in
theorem movement_value (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (origin : Financial.InstructionOrigin source)
    (before : (Financial.process source).GeneratedState) : (movement source origin before).value = BodySource.Source.movement source origin before := by
  simp only [movement,BodySource.Source.movement,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Count.length_value,instruction_value]
omit [DecidableEq T] in
theorem frameFold_value (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (origins : List (Financial.InstructionOrigin source))
    (before : (Financial.process source).GeneratedState) : (frameFold source origins before).value = BodySource.Source.frameFold source origins before := by
  induction origins generalizing before with
  | nil => rfl
  | cons head tail ih => simp only [frameFold,BodySource.Source.frameFold,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,movement_value,ih]
omit [DecidableEq T] in
theorem frames_value (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (count : Nat) :
    (frames source count).value = BodySource.Source.frames source count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [frames,BodySource.Source.frames,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,frameFold_value,ih]
theorem profile_value (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat) :
    (profile bound start span).value = BodySource.Source.profile bound start span := by
  simp only [profile,BodySource.Source.profile,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Count.length_value]
theorem manifest_value (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat) :
    (manifest bound start span).value = BodySource.Source.manifest bound start span := by
  simp only [manifest,BodySource.Source.manifest,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Count.length_value]
theorem evaluation_value (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat) :
    (evaluation bound start span).value = BodySource.Source.evaluation bound start span := by
  simp only [evaluation,BodySource.Source.evaluation,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,frames_value,profile_value,manifest_value]
end Source
namespace FutureShape
variable {actual : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {driver : Feedback.Input actual.source.code}
def report (cursor : Cursor actual driver) (new previous : Future.Recovery.Assessment.Report cursor.model) : Formula :=
  1 ⊞ Present.profile new.evaluation.profile previous.evaluation.profile ⊞
  Present.inventoryPair new.evaluation.native previous.evaluation.native ⊞ 1 ⊠ Count.length (Window.axes cursor.model cursor.depth)

def comparison (cursor : Cursor actual driver) :
    Option (Future.Recovery.Assessment.Report cursor.model) → Option (Future.Recovery.Assessment.Report cursor.model) → Formula
  | some current,some original => report cursor current original+3
  | none,none | some _,none | none,some _ => 2

theorem report_value (cursor : Cursor actual driver) (new previous : Future.Recovery.Assessment.Report cursor.model) :
    (report cursor new previous).value = BodySource.FutureShape.report cursor new previous := by
  simp only [report,BodySource.FutureShape.report,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Present.profile_value,Present.inventoryPair_value,Count.length_value]
theorem comparison_value (cursor : Cursor actual driver) (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) :
    (comparison cursor new previous).value = BodySource.FutureShape.comparison cursor new previous := by
  cases new <;> cases previous <;> simp only [comparison,BodySource.FutureShape.comparison,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,report_value]
end FutureShape
namespace BenefitShape
variable {actual : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {driver : Feedback.Input actual.source.code}
def inventoryDue (new previous : Feedback.Authority.Trace.Manifest P G O T I) : Formula :=
  Present.inventory new ⊞ Present.inventory previous ⊞ Present.subperm (Present.rowCount new) (Present.rowCount previous)

def present (cursor : Cursor actual driver) (new previous : Evaluation cursor.source.val.code) : Formula :=
  1 ⊞ inventoryDue new.native previous.native ⊞ 1 ⊠ Count.length (Window.axes cursor.model cursor.depth)

def future (cursor : Cursor actual driver) :
    Option (Future.Recovery.Assessment.Report cursor.model) → Option (Future.Recovery.Assessment.Report cursor.model) → Formula
  | some current,some original => present cursor current.evaluation original.evaluation+3
  | none,none | some _,none | none,some _ => 2

omit [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I] in
theorem inventoryDue_value (new previous : Feedback.Authority.Trace.Manifest P G O T I) :
    (inventoryDue new previous).value = BodySource.BenefitShape.inventoryDue new previous := by
  simp only [inventoryDue,BodySource.BenefitShape.inventoryDue,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Present.inventory_value,Present.subperm_value,Present.rowCount_value]
theorem present_value (cursor : Cursor actual driver) (new previous : Evaluation cursor.source.val.code) :
    (present cursor new previous).value = BodySource.BenefitShape.present cursor new previous := by
  simp only [present,BodySource.BenefitShape.present,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,inventoryDue_value,Count.length_value]
theorem future_value (cursor : Cursor actual driver) (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) :
    (future cursor new previous).value = BodySource.BenefitShape.future cursor new previous := by
  cases new <;> cases previous <;> simp only [future,BodySource.BenefitShape.future,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,present_value]
end BenefitShape
end Count
namespace Amount
def length {α : Type} : List α → Formula
  | [] => 0
  | _::tail => length tail+1
theorem length_value {α : Type} (items : List α) : (length items).value = items.length := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [length,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,ih,List.length_cons]
namespace Present
def unitLists {α : Type} (left right : List α) := Amount.lists (fun _ _ => 1) left right
def profile (new previous : Settlement.Profile P G O (Mandate.State P T) I) : Formula :=
  unitLists new.originalDebts previous.originalDebts + unitLists new.newbornDebts previous.newbornDebts +
  Amount.lists unitLists new.rights previous.rights + unitLists new.uncoveredClaims previous.uncoveredClaims +
  unitLists new.firstServices previous.firstServices + 6
def slotSum {α β : Type} (slots : α → List β) : List α → Formula
  | [] => 0
  | row::rest => Amount.length (slots row) + slotSum slots rest
def rowCount (manifest : Feedback.Authority.Trace.Manifest P G O T I) : Formula :=
  Amount.length manifest.originalGrants + Amount.length manifest.candidateGrants +
  slotSum (fun row => row.2.2.slots) manifest.originalChallenges + slotSum (fun row => row.2.slots) manifest.candidateChallenges
def inventory (manifest : Feedback.Authority.Trace.Manifest P G O T I) : Formula :=
  4+8*(Amount.length manifest.originalGrants + Amount.length manifest.candidateGrants) +
  Amount.length manifest.originalChallenges + Amount.length manifest.candidateChallenges +
  11*(slotSum (fun row => row.2.2.slots) manifest.originalChallenges+slotSum (fun row => row.2.slots) manifest.candidateChallenges)
def subperm (left right : Formula) := left*(3*(left+right)+2)
def inventoryPair (new previous : Feedback.Authority.Trace.Manifest P G O T I) :=
  inventory new+inventory previous+(subperm (rowCount previous) (rowCount new)+1+subperm (rowCount new) (rowCount previous))
variable {actual : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {driver : Feedback.Input actual.source.code}
def present (cursor : Cursor actual driver) (new previous : Evaluation cursor.source.val.code) :=
  6+profile new.profile previous.profile+inventoryPair new.native previous.native+2*Amount.length (Window.axes cursor.model cursor.depth)
theorem unitLists_value {α : Type} (left right : List α) : (unitLists left right).value = NativeAdmission.listsBudget (fun _ _ => 1) left right := Amount.lists_value _ _ _
omit [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I] in
theorem profile_value (new previous : Settlement.Profile P G O (Mandate.State P T) I) : (profile new previous).value = NativeAdmission.profileBudget new previous := by
  simp only [profile,NativeAdmission.profileBudget,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,unitLists_value,Amount.lists_value]
theorem slotSum_value {α β : Type} (slots : α → List β) (rows : List α) : (slotSum slots rows).value = (rows.map (fun row => (slots row).length)).sum := by
  induction rows with
  | nil => rfl
  | cons head tail ih => simp only [slotSum,add_value,Amount.length_value,ih,List.map_cons,List.sum_cons]
omit [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I] in
theorem rowCount_value (manifest : Feedback.Authority.Trace.Manifest P G O T I) : (rowCount manifest).value = NativeInventory.rowCount manifest := by
  simp only [rowCount,NativeInventory.rowCount,add_value,Amount.length_value,slotSum_value]
omit [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I] in
theorem inventory_value (manifest : Feedback.Authority.Trace.Manifest P G O T I) : (inventory manifest).value = NativeInventory.budget manifest := by
  simp only [inventory,NativeInventory.budget,add_value,mul_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Amount.length_value,slotSum_value]
theorem subperm_value (left right : Formula) : (subperm left right).value = NativeBenefit.subpermBudget left.value right.value := by
  simp only [subperm,NativeBenefit.subpermBudget,add_value,mul_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value]
omit [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I] in
theorem inventoryPair_value (new previous : Feedback.Authority.Trace.Manifest P G O T I) : (inventoryPair new previous).value = NativeAdmission.inventoryBudget new previous := by
  simp only [inventoryPair,NativeAdmission.inventoryBudget,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,inventory_value,subperm_value,rowCount_value]
theorem present_value (cursor : Cursor actual driver) (new previous : Evaluation cursor.source.val.code) : (present cursor new previous).value = NativeAdmission.presentBudget cursor new previous := by
  simp only [present,NativeAdmission.presentBudget,add_value,mul_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,profile_value,inventoryPair_value,Amount.length_value]
end Present
namespace Source
def payload (request : Request P G O (Mandate.State P T) I) : Formula :=
  match request.operation with | .use _ goods _ => Amount.length goods | _ => 0
def validity (law : RawLaw P G O (Mandate.State P T) I) (current : RawCurrent P G (Mandate.State P T) I)
    (request : Request P G O (Mandate.State P T) I) : Formula :=
  let debit := Amount.length (law.debit current request)
  (Amount.length request.consents+4)*Amount.length (law.requiredPorts current request)+
  (2*debit+6)*debit+2*Amount.length (law.credit current request)+2*payload request+20
def instruction (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (origin : Financial.InstructionOrigin source) : Formula :=
  match origin.instruction? source with | none => 1 | some item => validity source.law item.before item.request+2
def movement (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (origin : Financial.InstructionOrigin source)
    (before : (Financial.process source).GeneratedState) := 15*Amount.length before.current.slots+14+instruction source origin
def frameFold (source : ProgrammeSource.Input P G O (Mandate.State P T) I) : List (Financial.InstructionOrigin source) → (Financial.process source).GeneratedState → Formula
  | [],_ => 0
  | origin::tail,before => 2+movement source origin before+frameFold source tail ((Financial.consume source origin before).next source)
def frames (source : ProgrammeSource.Input P G O (Mandate.State P T) I) : Nat → Formula
  | 0 => 1
  | count+1 => frames source count+3+frameFold source (Financial.inventoryAt source (ProgrammeHistory.visitAt source count)) (Financial.accountAt source count)
def finish (start span : Nat) : Formula := .literal start + .literal span + 1
variable (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I))
def profile (start span : Nat) : Formula :=
  let first := Amount.length (Financial.accountAt bound.source.input (start+1)).current.slots
  let last := Amount.length (Financial.accountAt bound.source.input (Window.finish start span)).current.slots
  let parties := Amount.length bound.source.code.parties
  13+3*first+2*last+first*(1+3*parties)+Amount.length bound.source.code.instruments*(parties*(3*parties))+2*Amount.length bound.source.code.task.slots
def manifest (start span : Nat) : Formula :=
  10+2*finish start span+17*Amount.length (Authority.recordsAt bound start)+
  5*Amount.length (Authority.challengesAt bound (start+1))+10*Amount.length (Authority.recordsAt bound (start+span))+
  3*Amount.length (Authority.challengesAt bound (Window.finish start span))
def evaluation (start span : Nat) := frames bound.source.input (Window.finish start span)+profile bound start span+manifest bound start span
variable {bound}
omit [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I] in
theorem payload_value (request : Request P G O (Mandate.State P T) I) : (payload request).value = RawLaw.ValiditySource.payloadLength request := by
  rcases request with ⟨signer,consents,purpose,gates,operation⟩
  cases operation <;> simp only [payload,RawLaw.ValiditySource.payloadLength,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Amount.length_value]
omit [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I] in
theorem validity_value (law : RawLaw P G O (Mandate.State P T) I) (current : RawCurrent P G (Mandate.State P T) I)
    (request : Request P G O (Mandate.State P T) I) : (validity law current request).value = RawLaw.ValiditySource.budget law current request := by
  simp only [validity,RawLaw.ValiditySource.budget,add_value,mul_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Amount.length_value,payload_value]
omit [DecidableEq O] [DecidableEq T] in
theorem instruction_value (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (origin : Financial.InstructionOrigin source) :
    (instruction source origin).value = Financial.InstructionSource.budget source origin := by
  unfold instruction Financial.InstructionSource.budget
  split <;> simp_all only [add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,validity_value]
omit [DecidableEq T] in
theorem movement_value (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (origin : Financial.InstructionOrigin source)
    (before : (Financial.process source).GeneratedState) : (movement source origin before).value = NativeMovement.budget source origin before := by
  simp only [movement,NativeMovement.budget,add_value,mul_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Amount.length_value,instruction_value]
omit [DecidableEq T] in
theorem frameFold_value (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (origins : List (Financial.InstructionOrigin source))
    (before : (Financial.process source).GeneratedState) : (frameFold source origins before).value = NativeSourceFrames.foldBudget source origins before := by
  induction origins generalizing before with
  | nil => rfl
  | cons head tail ih => simp only [frameFold,NativeSourceFrames.foldBudget,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,movement_value,ih]
omit [DecidableEq T] in
theorem frames_value (source : ProgrammeSource.Input P G O (Mandate.State P T) I) (count : Nat) : (frames source count).value = NativeSourceFrames.budget source count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [frames,NativeSourceFrames.budget,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,frameFold_value,ih]
theorem finish_value (start span : Nat) : (finish start span).value = Window.finish start span := rfl
theorem profile_value (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat) :
    (profile bound start span).value = NativeProfile.budget bound start span := by
  simp only [profile,NativeProfile.budget,add_value,mul_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Amount.length_value]
theorem manifest_value (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat) :
    (manifest bound start span).value = NativeManifest.budget bound start span := by
  simp only [manifest,NativeManifest.budget,add_value,mul_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Amount.length_value,finish_value]
theorem evaluation_value (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat) :
    (evaluation bound start span).value = NativeTensor.evaluationBudget bound start span := by
  simp only [evaluation,NativeTensor.evaluationBudget,add_value,frames_value,profile_value,manifest_value]
end Source
namespace FutureShape
variable {actual : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {driver : Feedback.Input actual.source.code}
def report (cursor : Cursor actual driver) (new previous : Future.Recovery.Assessment.Report cursor.model) :=
  12+Present.profile new.evaluation.profile previous.evaluation.profile+Present.inventoryPair new.evaluation.native previous.evaluation.native+2*Amount.length (Window.axes cursor.model cursor.depth)
def comparison (cursor : Cursor actual driver) : Option (Future.Recovery.Assessment.Report cursor.model) → Option (Future.Recovery.Assessment.Report cursor.model) → Formula
  | some current,some original => report cursor current original+2
  | none,none | some _,none | none,some _ => 1
theorem report_value (cursor : Cursor actual driver) (new previous : Future.Recovery.Assessment.Report cursor.model) :
    (report cursor new previous).value = NativeAdmission.reportBudget cursor new previous := by
  simp only [report,NativeAdmission.reportBudget,add_value,mul_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,Present.profile_value,Present.inventoryPair_value,Amount.length_value]
theorem comparison_value (cursor : Cursor actual driver) (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) :
    (comparison cursor new previous).value = NativeAdmission.futureBudget cursor new previous := by
  cases new <;> cases previous <;> simp only [comparison,NativeAdmission.futureBudget,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,report_value]
end FutureShape
namespace BenefitShape
variable {actual : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {driver : Feedback.Input actual.source.code}
def inventoryDue (new previous : Feedback.Authority.Trace.Manifest P G O T I) := Present.inventory new+Present.inventory previous+Present.subperm (Present.rowCount new) (Present.rowCount previous)
def present (cursor : Cursor actual driver) (new previous : Evaluation cursor.source.val.code) := 9+inventoryDue new.native previous.native+2*Amount.length (Window.axes cursor.model cursor.depth)
def future (cursor : Cursor actual driver) : Option (Future.Recovery.Assessment.Report cursor.model) → Option (Future.Recovery.Assessment.Report cursor.model) → Formula
  | some current,some original => present cursor current.evaluation original.evaluation+3
  | none,none | some _,none | none,some _ => 1
omit [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I] in
theorem inventoryDue_value (new previous : Feedback.Authority.Trace.Manifest P G O T I) : (inventoryDue new previous).value = NativeBenefit.inventoryDueBudget new previous := by
  simp only [inventoryDue,NativeBenefit.inventoryDueBudget,add_value,Present.inventory_value,Present.subperm_value,Present.rowCount_value]
theorem present_value (cursor : Cursor actual driver) (new previous : Evaluation cursor.source.val.code) : (present cursor new previous).value = NativeBenefit.presentBudget cursor new previous := by
  simp only [present,NativeBenefit.presentBudget,add_value,mul_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,inventoryDue_value,Amount.length_value]
theorem future_value (cursor : Cursor actual driver) (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) : (future cursor new previous).value = NativeBenefit.futureBudget cursor new previous := by
  cases new <;> cases previous <;> simp only [future,NativeBenefit.futureBudget,add_value,Formula.value,Counter.Opcode.operation,PaidBudgetArithmetic.Operation.value,present_value]
end BenefitShape
end Amount

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Expand
