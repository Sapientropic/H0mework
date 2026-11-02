import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Work
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget
open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {input : Input seed} (prepared : Prepared input)

abbrev CellScope (index : Index prepared) :=
  Scope (initial input prepared.saved[index].point) input.pricing input.future
    (reference input prepared.saved[index].point) input.actor input.position

/-- Native ceiling internals and field acquisition keep their original source operands. -/
inductive Query where
  | field (left right : Work.SignatureKey (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  | useKind (left right : Use)
  | admission (index : Index prepared)
  | benefit (index : Index prepared)
  | sourceBudget (index : Index prepared) (scope : CellScope prepared index)
      (new previous : Whole.Intent scope) (table : Whole.Table scope)
  | comparisonBudget (index : Index prepared) (scope : CellScope prepared index)
      (current original : Evaluation (initial input prepared.saved[index].point).source.val.code)
  | rowBudget (index : Index prepared) (scope : CellScope prepared index)
      (previous new : Whole.Intent scope) (row : Whole.Decision.Row scope)
def Query.answer : Query prepared → Nat
  | .field .. | .useKind .. => 1
  | .admission index => Work.localAdmissionCeiling prepared.saved[index].stage
  | .benefit index => Work.localBenefitCeiling prepared.saved[index].stage
  | .sourceBudget _ scope new previous table => Whole.Work.sourcePresentBudget scope input.span new previous table
  | .comparisonBudget index _ current original => NativeAdmission.presentBudget (initial input prepared.saved[index].point) current original
  | .rowBudget _ scope previous new row => Whole.Work.admissionBudget scope input.span previous new row

inductive Tag where
  | listEnd | listPair | optionEnd | optionPair | operation | request | signature | ceilingEnd | ceilingPair | lengthEnd | lengthPair | nativeRow
  deriving DecidableEq
inductive Event where
  | literal (value : Nat)
  | query (source : Query prepared) (value : Nat)
  | add (left right result : Nat)
  | multiply (left right result : Nat)
  | maximum (left right result : Nat)
  | branch (tag : Tag)
  | reuse (slot value : Nat)
  | evaluation (index : Index prepared) (scope : CellScope prepared index)
      (intent : Whole.Intent scope) (table : Whole.Table scope)
  | sourceStep (index : Index prepared) (scope : CellScope prepared index)
      (intent : Whole.Intent scope) (table : Whole.Table scope)
      (event : NativeTensor.Event Party Good Port Technology Instrument)
  | comparisonShape (index : Index prepared) (scope : CellScope prepared index)
      (current original : Evaluation (initial input prepared.saved[index].point).source.val.code)
  | nativeFrameInputs (source : ProgrammeSource.Input Party Good Port (Mandate.State Party Technology) Instrument)
      (ordinal : Nat) (kind : Fin 3)
  | nativeInstructionInput (source : ProgrammeSource.Input Party Good Port (Mandate.State Party Technology) Instrument)
      (origin : Financial.InstructionOrigin source)
  | nativeTransitionInput (source : ProgrammeSource.Input Party Good Port (Mandate.State Party Technology) Instrument)
      (origin : Financial.InstructionOrigin source) (before : (Financial.process source).GeneratedState)
  | nativeMovementInputs (source : ProgrammeSource.Input Party Good Port (Mandate.State Party Technology) Instrument)
      (origin : Financial.InstructionOrigin source) (before : (Financial.process source).GeneratedState)
  | nativeValidityInputs (law : RawLaw Party Good Port (Mandate.State Party Technology) Instrument)
      (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
      (request : Request Party Good Port (Mandate.State Party Technology) Instrument) (kind : Fin 5)
  | nativeProfileInputs (bound : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (ordinal : Nat) (kind : Fin 5)
  | nativeManifestInputs (bound : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (ordinal : Nat) (challenge : Bool)
  | nativeFutureInputs (index : Index prepared) (scope : CellScope prepared index)
      (intent : Whole.Intent scope) (table : Whole.Table scope)
      (word : List (Future.Recovery.Action seed))
  | futureShape (index : Index prepared) (scope : CellScope prepared index)
      (current original : Option (Future.Recovery.Assessment.Report (initial input prepared.saved[index].point).model))
  | benefitInputs (index : Index prepared) (scope : CellScope prepared index)
      (tables : List (Whole.Table scope)) (intents : List (Whole.Intent scope))
      (words : List (List (Future.Recovery.Action seed)))
  | fundingInputs (index : Index prepared) (scope : CellScope prepared index)
      (previous new : Whole.Intent scope) (table : Whole.Table scope)
      (word : List (Future.Recovery.Action seed))
def Event.Valid : Event prepared → Prop
  | .literal _ | .branch _ | .reuse .. | .evaluation .. | .sourceStep .. | .comparisonShape .. | .nativeFrameInputs .. | .nativeInstructionInput .. | .nativeTransitionInput .. | .nativeMovementInputs .. | .nativeValidityInputs .. | .nativeProfileInputs .. | .nativeManifestInputs .. | .nativeFutureInputs .. | .futureShape .. | .benefitInputs .. | .fundingInputs .. => True
  | .query source value => value = source.answer prepared
  | .add left right result => result = left+right
  | .multiply left right result => result = left*right
  | .maximum left right result => result = max left right
instance (event : Event prepared) : Decidable (event.Valid prepared) := by
  cases event <;> unfold Event.Valid <;> infer_instance

structure Run (expected : Nat) where
  private mk ::
  value : Nat
  exact : value = expected
  work : List (Event prepared)
  sound : ∀ event ∈ work,event.Valid prepared
variable {prepared}
def lit (n : Nat) : Run prepared n := ⟨n,rfl,[.literal n],by simp [Event.Valid]⟩
def read (query : Query prepared) : Run prepared (query.answer prepared) :=
  ⟨query.answer prepared,rfl,[.query query (query.answer prepared)],by simp [Event.Valid]⟩
def mark {n : Nat} (tag : Tag) (made : Run prepared n) : Run prepared n :=
  ⟨made.value,made.exact,.branch tag :: made.work,by
    intro event member
    rcases List.mem_cons.mp member with same | later
    · subst event;trivial
    · exact made.sound event later⟩
private def combine {a b c : Nat} (left : Run prepared a) (right : Run prepared b)
    (result : Nat) (exact : result = c) (event : Event prepared) (valid : event.Valid prepared) : Run prepared c :=
  ⟨result,exact,left.work ++ right.work ++ [event],by
    intro item inside
    rcases List.mem_append.mp inside with earlier | last
    · rcases List.mem_append.mp earlier with first | second
      · exact left.sound item first
      · exact right.sound item second
    · have same := List.mem_singleton.mp last
      subst item;exact valid⟩
def plus {a b : Nat} (left : Run prepared a) (right : Run prepared b) : Run prepared (a+b) :=
  combine left right (left.value+right.value) (by rw [left.exact,right.exact]) (.add left.value right.value (left.value+right.value)) rfl
def times {a b : Nat} (left : Run prepared a) (right : Run prepared b) : Run prepared (a*b) :=
  combine left right (left.value*right.value) (by rw [left.exact,right.exact]) (.multiply left.value right.value (left.value*right.value)) rfl
def largest {a b : Nat} (left : Run prepared a) (right : Run prepared b) : Run prepared (max a b) :=
  combine left right (max left.value right.value) (by rw [left.exact,right.exact]) (.maximum left.value right.value (max left.value right.value)) rfl
/-- Reusing a cached source computation does not replay its generating work. -/
def borrow {n : Nat} (slot : Nat) (made : Run prepared n) : Run prepared n :=
  ⟨made.value,made.exact,[.reuse slot made.value],by simp [Event.Valid]⟩
def retain {a b : Nat} (earlier : Run prepared a) (later : Run prepared b) : Run prepared b :=
  ⟨later.value,later.exact,earlier.work ++ later.work,by
    intro event inside
    rcases List.mem_append.mp inside with first | second
    · exact earlier.sound event first
    · exact later.sound event second⟩
local infixl:65 " ⊞ " => plus
local infixl:70 " ⊠ " => times

def lists {α : Type} (cost : α → α → Nat) (run : (left right : α) → Run prepared (cost left right)) :
    (left right : List α) → Run prepared (NativeAdmission.listsBudget cost left right)
  | a::as,b::bs => mark .listPair (run a b ⊞ lit 1 ⊞ lists cost run as bs)
  | [],[] | [],_::_ | _::_,[] => mark .listEnd (lit 1)
def optional {α : Type} (cost : α → α → Nat) (run : (left right : α) → Run prepared (cost left right)) :
    (left right : Option α) → Run prepared (SignatureWork.optionalBudget cost left right)
  | some left,some right => mark .optionPair (lit 1 ⊞ run left right)
  | none,none | none,some _ | some _,none => mark .optionEnd (lit 1)

def field (left right : Work.SignatureKey (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) : Run prepared 1 := read (.field left right)
def parties (left right : List Party) : Run prepared (ActionWork.partiesBudget left right) :=
  lists (fun _ _ => 1) (fun left right => field (.party left) (.party right)) left right
def ports (left right : List Port) : Run prepared (ActionWork.portsBudget left right) :=
  lists (fun _ _ => 1) (fun left right => field (.port left) (.port right)) left right
def bundle (left right : Bundle Good) : Run prepared (ActionWork.bundleBudget left right) :=
  lists (fun _ _ => 3) (fun left right => (field (.good left.1) (.good right.1) ⊞ lit 1) ⊞ field (.quantity left.2) (.quantity right.2)) left right

def operation : (left right : Institutions.Capitalism.Universal.Source.Program.Operation Party Good (Mandate.State Party Technology) Instrument) →
    Run prepared (ActionWork.operationBudget left right)
  | .produce left,.produce right => mark .operation (lit 1 ⊞ field (.party left) (.party right))
  | .transfer a b goodsL,.transfer c d goodsR => mark .operation
      (lit 1 ⊞ (field (.party a) (.party c) ⊞ lit 1 ⊞ (field (.party b) (.party d) ⊞ lit 1 ⊞ bundle goodsL goodsR)))
  | .use a goodsL u,.use b goodsR v => mark .operation
      (lit 1 ⊞ (field (.party a) (.party b) ⊞ lit 1 ⊞ (bundle goodsL goodsR ⊞ lit 1 ⊞ read (.useKind u v))))
  | .issue i a b q,.issue j c d r => mark .operation
      (lit 1 ⊞ (field (.instrument i) (.instrument j) ⊞ lit 1 ⊞ (field (.party a) (.party c) ⊞ lit 1 ⊞ (field (.party b) (.party d) ⊞ lit 1 ⊞ field (.quantity q) (.quantity r)))))
  | .assign i a b c q,.assign j d e f r => mark .operation
      (lit 1 ⊞ (field (.instrument i) (.instrument j) ⊞ lit 1 ⊞ (field (.party a) (.party d) ⊞ lit 1 ⊞ (field (.party b) (.party e) ⊞ lit 1 ⊞ (field (.party c) (.party f) ⊞ lit 1 ⊞ field (.quantity q) (.quantity r))))))
  | .settle i a b q,.settle j c d r => mark .operation
      (lit 1 ⊞ (field (.instrument i) (.instrument j) ⊞ lit 1 ⊞ (field (.party a) (.party c) ⊞ lit 1 ⊞ (field (.party b) (.party d) ⊞ lit 1 ⊞ field (.quantity q) (.quantity r)))))
  | .revise a t,.revise b u => mark .operation
      (lit 1 ⊞ (field (.party a) (.party b) ⊞ lit 1 ⊞ field (.technology t) (.technology u)))
  | .produce _,.transfer _ _ _ => mark .operation (lit 1)
  | .produce _,.use _ _ _ => mark .operation (lit 1)
  | .produce _,.issue _ _ _ _ => mark .operation (lit 1)
  | .produce _,.assign _ _ _ _ _ => mark .operation (lit 1)
  | .produce _,.settle _ _ _ _ => mark .operation (lit 1)
  | .produce _,.revise _ _ => mark .operation (lit 1)
  | .produce _,.present => mark .operation (lit 1)
  | .transfer _ _ _,.produce _ => mark .operation (lit 1)
  | .transfer _ _ _,.use _ _ _ => mark .operation (lit 1)
  | .transfer _ _ _,.issue _ _ _ _ => mark .operation (lit 1)
  | .transfer _ _ _,.assign _ _ _ _ _ => mark .operation (lit 1)
  | .transfer _ _ _,.settle _ _ _ _ => mark .operation (lit 1)
  | .transfer _ _ _,.revise _ _ => mark .operation (lit 1)
  | .transfer _ _ _,.present => mark .operation (lit 1)
  | .use _ _ _,.produce _ => mark .operation (lit 1)
  | .use _ _ _,.transfer _ _ _ => mark .operation (lit 1)
  | .use _ _ _,.issue _ _ _ _ => mark .operation (lit 1)
  | .use _ _ _,.assign _ _ _ _ _ => mark .operation (lit 1)
  | .use _ _ _,.settle _ _ _ _ => mark .operation (lit 1)
  | .use _ _ _,.revise _ _ => mark .operation (lit 1)
  | .use _ _ _,.present => mark .operation (lit 1)
  | .issue _ _ _ _,.produce _ => mark .operation (lit 1)
  | .issue _ _ _ _,.transfer _ _ _ => mark .operation (lit 1)
  | .issue _ _ _ _,.use _ _ _ => mark .operation (lit 1)
  | .issue _ _ _ _,.assign _ _ _ _ _ => mark .operation (lit 1)
  | .issue _ _ _ _,.settle _ _ _ _ => mark .operation (lit 1)
  | .issue _ _ _ _,.revise _ _ => mark .operation (lit 1)
  | .issue _ _ _ _,.present => mark .operation (lit 1)
  | .assign _ _ _ _ _,.produce _ => mark .operation (lit 1)
  | .assign _ _ _ _ _,.transfer _ _ _ => mark .operation (lit 1)
  | .assign _ _ _ _ _,.use _ _ _ => mark .operation (lit 1)
  | .assign _ _ _ _ _,.issue _ _ _ _ => mark .operation (lit 1)
  | .assign _ _ _ _ _,.settle _ _ _ _ => mark .operation (lit 1)
  | .assign _ _ _ _ _,.revise _ _ => mark .operation (lit 1)
  | .assign _ _ _ _ _,.present => mark .operation (lit 1)
  | .settle _ _ _ _,.produce _ => mark .operation (lit 1)
  | .settle _ _ _ _,.transfer _ _ _ => mark .operation (lit 1)
  | .settle _ _ _ _,.use _ _ _ => mark .operation (lit 1)
  | .settle _ _ _ _,.issue _ _ _ _ => mark .operation (lit 1)
  | .settle _ _ _ _,.assign _ _ _ _ _ => mark .operation (lit 1)
  | .settle _ _ _ _,.revise _ _ => mark .operation (lit 1)
  | .settle _ _ _ _,.present => mark .operation (lit 1)
  | .revise _ _,.produce _ => mark .operation (lit 1)
  | .revise _ _,.transfer _ _ _ => mark .operation (lit 1)
  | .revise _ _,.use _ _ _ => mark .operation (lit 1)
  | .revise _ _,.issue _ _ _ _ => mark .operation (lit 1)
  | .revise _ _,.assign _ _ _ _ _ => mark .operation (lit 1)
  | .revise _ _,.settle _ _ _ _ => mark .operation (lit 1)
  | .revise _ _,.present => mark .operation (lit 1)
  | .present,.produce _ => mark .operation (lit 1)
  | .present,.transfer _ _ _ => mark .operation (lit 1)
  | .present,.use _ _ _ => mark .operation (lit 1)
  | .present,.issue _ _ _ _ => mark .operation (lit 1)
  | .present,.assign _ _ _ _ _ => mark .operation (lit 1)
  | .present,.settle _ _ _ _ => mark .operation (lit 1)
  | .present,.revise _ _ => mark .operation (lit 1)
  | .present,.present => mark .operation (lit 1)
def request (left right : Future.Recovery.Action seed) : Run prepared (ActionWork.budget left right) :=
  mark .request (lit 1 ⊞ (field (.party left.signer) (.party right.signer) ⊞ lit 1 ⊞
    (parties left.consents right.consents ⊞ lit 1 ⊞ (field (.port left.purpose) (.port right.purpose) ⊞ lit 1 ⊞
      (ports left.gates right.gates ⊞ lit 1 ⊞ operation left.operation right.operation)))))

def word (left right : List (Future.Recovery.Action seed)) : Run prepared (SignatureWork.Generic.wordBudget ActionWork.budget left right) := lists ActionWork.budget request left right
def words (left right : List (List (Future.Recovery.Action seed))) : Run prepared (SignatureWork.Generic.wordsBudget ActionWork.budget left right) := lists (SignatureWork.Generic.wordBudget ActionWork.budget) word left right
def invoice (left right : Option (List (Future.Recovery.Action seed))) : Run prepared (SignatureWork.Generic.invoiceBudget ActionWork.budget left right) := optional (SignatureWork.Generic.wordBudget ActionWork.budget) word left right
def control (left right : List (Option (List (List (Future.Recovery.Action seed))))) : Run prepared (SignatureWork.Generic.controlBudget ActionWork.budget left right) := lists (SignatureWork.optionalBudget (SignatureWork.Generic.wordsBudget ActionWork.budget)) (optional (SignatureWork.Generic.wordsBudget ActionWork.budget) words) left right

def signature : (left right : Signature (Future.Recovery.Action seed)) → Run prepared (SignatureWork.Generic.budget ActionWork.budget left right)
  | .keep a,.keep b => mark .signature (lit 1 ⊞ word a b)
  | .direct a c,.direct b d => mark .signature (lit 1 ⊞ (word a b ⊞ lit 1 ⊞ control c d))
  | .own a r c,.own b s d => mark .signature (lit 1 ⊞ (word a b ⊞ lit 1 ⊞ (word r s ⊞ lit 1 ⊞ control c d)))
  | .invoiced a r i c,.invoiced b s j d => mark .signature (lit 1 ⊞ (word a b ⊞ lit 1 ⊞ (word r s ⊞ lit 1 ⊞ (invoice i j ⊞ lit 1 ⊞ control c d))))
  | .stopped a,.stopped b => mark .signature (lit 1 ⊞ invoice a b)
  | .prefix a n,.prefix b m => mark .signature (lit 1 ⊞ (words a b ⊞ lit 1 ⊞ signature n m))
  | .keep _,.direct _ _ => mark .signature (lit 1)
  | .keep _,.own _ _ _ => mark .signature (lit 1)
  | .keep _,.invoiced _ _ _ _ => mark .signature (lit 1)
  | .keep _,.stopped _ => mark .signature (lit 1)
  | .keep _,.prefix _ _ => mark .signature (lit 1)
  | .direct _ _,.keep _ => mark .signature (lit 1)
  | .direct _ _,.own _ _ _ => mark .signature (lit 1)
  | .direct _ _,.invoiced _ _ _ _ => mark .signature (lit 1)
  | .direct _ _,.stopped _ => mark .signature (lit 1)
  | .direct _ _,.prefix _ _ => mark .signature (lit 1)
  | .own _ _ _,.keep _ => mark .signature (lit 1)
  | .own _ _ _,.direct _ _ => mark .signature (lit 1)
  | .own _ _ _,.invoiced _ _ _ _ => mark .signature (lit 1)
  | .own _ _ _,.stopped _ => mark .signature (lit 1)
  | .own _ _ _,.prefix _ _ => mark .signature (lit 1)
  | .invoiced _ _ _ _,.keep _ => mark .signature (lit 1)
  | .invoiced _ _ _ _,.direct _ _ => mark .signature (lit 1)
  | .invoiced _ _ _ _,.own _ _ _ => mark .signature (lit 1)
  | .invoiced _ _ _ _,.stopped _ => mark .signature (lit 1)
  | .invoiced _ _ _ _,.prefix _ _ => mark .signature (lit 1)
  | .stopped _,.keep _ => mark .signature (lit 1)
  | .stopped _,.direct _ _ => mark .signature (lit 1)
  | .stopped _,.own _ _ _ => mark .signature (lit 1)
  | .stopped _,.invoiced _ _ _ _ => mark .signature (lit 1)
  | .stopped _,.prefix _ _ => mark .signature (lit 1)
  | .prefix _ _,.keep _ => mark .signature (lit 1)
  | .prefix _ _,.direct _ _ => mark .signature (lit 1)
  | .prefix _ _,.own _ _ _ => mark .signature (lit 1)
  | .prefix _ _,.invoiced _ _ _ _ => mark .signature (lit 1)
  | .prefix _ _,.stopped _ => mark .signature (lit 1)

def length {α : Type} : (items : List α) → Run prepared items.length
  | [] => mark .lengthEnd (lit 0)
  | _::tail => mark .lengthPair (length tail ⊞ lit 1)
def ceiling {α : Type} (cost : α → Nat) (run : (item : α) → Run prepared (cost item)) :
    (items : List α) → Run prepared (Work.ceiling cost items)
  | [] => mark .ceilingEnd (lit 0)
  | head::tail => mark .ceilingPair (largest (run head) (ceiling cost run tail))

variable (prepared)
def signatureAt (term : Section prepared) (first second : Index prepared) : Run prepared (Work.signatureBudget prepared term first second) :=
  signature (Work.cachedShape prepared.saved[first].stage (readTerm prepared term first))
    (Work.cachedShape prepared.saved[second].stage (readTerm prepared term second))
def signatureCeiling : Run prepared (Work.signatureCeiling prepared) :=
  ceiling _ (fun term => ceiling _ (fun first => ceiling _ (signatureAt prepared term first) (keys prepared)) (keys prepared)) (sections prepared)
private theorem policy_ceiling_eq_foldr {α : Type} (cost : α → Nat) (items : List α) :
    Work.ceiling cost items = items.foldr (fun item total => max (cost item) total) 0 := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [Work.ceiling,List.foldr_cons,ih]

namespace PresentShape
def unitLists {α : Type} (left right : List α) :
    Run prepared (NativeAdmission.listsBudget (fun _ _ => 1) left right) :=
  lists (fun _ _ => 1) (fun _ _ => lit 1) left right

def profile (new previous : Settlement.Profile Party Good Port (Mandate.State Party Technology) Instrument) :
    Run prepared (NativeAdmission.profileBudget new previous) :=
  unitLists prepared new.originalDebts previous.originalDebts ⊞
  unitLists prepared new.newbornDebts previous.newbornDebts ⊞
  lists (NativeAdmission.listsBudget (fun _ _ => 1)) (unitLists prepared) new.rights previous.rights ⊞
  unitLists prepared new.uncoveredClaims previous.uncoveredClaims ⊞
  unitLists prepared new.firstServices previous.firstServices ⊞ lit 6

def slotSum {α β : Type} (slots : α → List β) :
    (rows : List α) → Run prepared ((rows.map (fun row => (slots row).length)).sum)
  | [] => mark .lengthEnd (lit 0)
  | row::rest => mark .lengthPair (length (slots row) ⊞ slotSum slots rest)

def rowCount (manifest : Feedback.Authority.Trace.Manifest Party Good Port Technology Instrument) :
    Run prepared (NativeInventory.rowCount manifest) :=
  length manifest.originalGrants ⊞ length manifest.candidateGrants ⊞
    slotSum prepared (fun row => row.2.2.slots) manifest.originalChallenges ⊞
    slotSum prepared (fun row => row.2.slots) manifest.candidateChallenges

def inventory (manifest : Feedback.Authority.Trace.Manifest Party Good Port Technology Instrument) :
    Run prepared (NativeInventory.budget manifest) :=
  lit 4 ⊞ lit 8 ⊠ (length manifest.originalGrants ⊞ length manifest.candidateGrants) ⊞
    length manifest.originalChallenges ⊞ length manifest.candidateChallenges ⊞
    lit 11 ⊠ (slotSum prepared (fun row => row.2.2.slots) manifest.originalChallenges ⊞
      slotSum prepared (fun row => row.2.slots) manifest.candidateChallenges)

def subperm {leftLength rightLength : Nat}
    (left : Unit → Run prepared leftLength) (right : Unit → Run prepared rightLength) :
    Run prepared (NativeBenefit.subpermBudget leftLength rightLength) :=
  left () ⊠ (lit 3 ⊠ (left () ⊞ right ()) ⊞ lit 2)

def inventoryPair (new previous : Feedback.Authority.Trace.Manifest Party Good Port Technology Instrument) :
    Run prepared (NativeAdmission.inventoryBudget new previous) :=
  inventory prepared new ⊞ inventory prepared previous ⊞
    (subperm prepared (fun _ => rowCount prepared previous) (fun _ => rowCount prepared new) ⊞ lit 1 ⊞
      subperm prepared (fun _ => rowCount prepared new) (fun _ => rowCount prepared previous))

variable {actual : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input actual.source.code}
def present (cursor : Cursor actual driver) (new previous : Evaluation cursor.source.val.code) :
    Run prepared (NativeAdmission.presentBudget cursor new previous) :=
  lit 6 ⊞ profile prepared new.profile previous.profile ⊞ inventoryPair prepared new.native previous.native ⊞
    lit 2 ⊠ length (Window.axes cursor.model cursor.depth)

end PresentShape

namespace NativeSourceShape
variable {prepared}
private def acquired {n : Nat} (event : Event prepared) (valid : event.Valid prepared)
    (made : Run prepared n) : Run prepared n :=
  ⟨made.value,made.exact,event :: made.work,by
    intro item inside
    rcases List.mem_cons.mp inside with same | later
    · subst item;exact valid
    · exact made.sound item later⟩
private def withNat {n : Nat} (earlier : Run prepared n) (cost : Nat → Nat)
    (step : (i : Nat) → Run prepared (cost i)) : Run prepared (cost n) :=
  let later := step earlier.value
  ⟨later.value,later.exact.trans (congrArg cost earlier.exact),earlier.work ++ later.work,by
    intro event inside
    rcases List.mem_append.mp inside with first | second
    · exact earlier.sound event first
    · exact later.sound event second⟩

variable (prepared)
def payload (request : Request Party Good Port (Mandate.State Party Technology) Instrument) :
    Run prepared (RawLaw.ValiditySource.payloadLength request) :=
  match original : request.operation with
  | .use _ goods _ => by simpa only [RawLaw.ValiditySource.payloadLength,original] using mark .operation (length goods)
  | .produce _ => by simpa only [RawLaw.ValiditySource.payloadLength,original] using mark .operation (lit 0)
  | .transfer _ _ _ => by simpa only [RawLaw.ValiditySource.payloadLength,original] using mark .operation (lit 0)
  | .issue _ _ _ _ => by simpa only [RawLaw.ValiditySource.payloadLength,original] using mark .operation (lit 0)
  | .assign _ _ _ _ _ => by simpa only [RawLaw.ValiditySource.payloadLength,original] using mark .operation (lit 0)
  | .settle _ _ _ _ => by simpa only [RawLaw.ValiditySource.payloadLength,original] using mark .operation (lit 0)
  | .revise _ _ => by simpa only [RawLaw.ValiditySource.payloadLength,original] using mark .operation (lit 0)
  | .present => by simpa only [RawLaw.ValiditySource.payloadLength,original] using mark .operation (lit 0)

def validity (law : RawLaw Party Good Port (Mandate.State Party Technology) Instrument)
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (request : Request Party Good Port (Mandate.State Party Technology) Instrument) :
    Run prepared (RawLaw.ValiditySource.budget law current request) :=
  let debit := acquired (.nativeValidityInputs law current request 0) (by trivial) (length (law.debit current request))
  let credit := acquired (.nativeValidityInputs law current request 1) (by trivial) (length (law.credit current request))
  let ports := acquired (.nativeValidityInputs law current request 2) (by trivial) (length (law.requiredPorts current request))
  let consents := acquired (.nativeValidityInputs law current request 3) (by trivial) (length request.consents)
  let goods := acquired (.nativeValidityInputs law current request 4) (by trivial) (payload prepared request)
  let made := (borrow 3 consents ⊞ lit 4) ⊠ borrow 2 ports ⊞
    (lit 2 ⊠ borrow 0 debit ⊞ lit 6) ⊠ borrow 0 debit ⊞ lit 2 ⊠ borrow 1 credit ⊞
    lit 2 ⊠ borrow 4 goods ⊞ lit 20
  retain debit (retain credit (retain ports (retain consents (retain goods made))))

def instruction (source : ProgrammeSource.Input Party Good Port (Mandate.State Party Technology) Instrument)
    (origin : Financial.InstructionOrigin source) :
    Run prepared (Financial.InstructionSource.budget source origin) :=
  acquired (.nativeInstructionInput source origin) (by trivial)
    (match original : origin.instruction? source with
    | none => by simpa only [Financial.InstructionSource.budget,original] using mark .nativeRow (lit 1)
    | some item => by simpa only [Financial.InstructionSource.budget,original] using
        (mark .nativeRow (validity prepared source.law item.before item.request ⊞ lit 2)))

def movement (source : ProgrammeSource.Input Party Good Port (Mandate.State Party Technology) Instrument)
    (origin : Financial.InstructionOrigin source) (before : (Financial.process source).GeneratedState) :
    Run prepared (NativeMovement.budget source origin before) :=
  acquired (.nativeMovementInputs source origin before) (by trivial)
    (lit 15 ⊠ length before.current.slots ⊞ lit 14 ⊞ instruction prepared source origin)

def frameFold (source : ProgrammeSource.Input Party Good Port (Mandate.State Party Technology) Instrument) :
    (origins : List (Financial.InstructionOrigin source)) →
    (before : (Financial.process source).GeneratedState) →
    Run prepared (NativeSourceFrames.foldBudget source origins before)
  | [],_ => mark .lengthEnd (lit 0)
  | origin::tail,before => mark .lengthPair
      (lit 2 ⊞ movement prepared source origin before ⊞
        acquired (.nativeTransitionInput source origin before) (by trivial)
          (frameFold source tail ((Financial.consume source origin before).next source)))

def frames (source : ProgrammeSource.Input Party Good Port (Mandate.State Party Technology) Instrument) :
    (count : Nat) → Run prepared (NativeSourceFrames.budget source count)
  | 0 => mark .lengthEnd (lit 1)
  | count+1 => mark .lengthPair (frames source count ⊞ lit 3 ⊞
      acquired (.nativeFrameInputs source count 0) (by trivial)
        (acquired (.nativeFrameInputs source count 1) (by trivial)
          (acquired (.nativeFrameInputs source count 2) (by trivial)
            (frameFold prepared source (Financial.inventoryAt source (ProgrammeHistory.visitAt source count))
              (Financial.accountAt source count)))))

def finish (start span : Nat) : Run prepared (Window.finish start span) := lit start ⊞ lit span ⊞ lit 1

def profile (bound : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (start span : Nat) :
    Run prepared (NativeProfile.budget bound start span) :=
  let first := withNat (lit start ⊞ lit 1) _ (fun ordinal =>
    acquired (.nativeProfileInputs bound ordinal 0) (by trivial)
      (length (Financial.accountAt bound.source.input ordinal).current.slots))
  let last := withNat (finish prepared start span) _ (fun ordinal =>
    acquired (.nativeProfileInputs bound ordinal 1) (by trivial)
      (length (Financial.accountAt bound.source.input ordinal).current.slots))
  let parties := acquired (.nativeProfileInputs bound start 2) (by trivial) (length bound.source.code.parties)
  let instruments := acquired (.nativeProfileInputs bound start 3) (by trivial) (length bound.source.code.instruments)
  let tasks := acquired (.nativeProfileInputs bound start 4) (by trivial) (length bound.source.code.task.slots)
  let made := lit 13 ⊞ lit 3 ⊠ borrow 0 first ⊞ lit 2 ⊠ borrow 1 last ⊞
    borrow 0 first ⊠ (lit 1 ⊞ lit 3 ⊠ borrow 2 parties) ⊞
    borrow 3 instruments ⊠ (borrow 2 parties ⊠ (lit 3 ⊠ borrow 2 parties)) ⊞ lit 2 ⊠ borrow 4 tasks
  retain first (retain last (retain parties (retain instruments (retain tasks made))))

def manifest (bound : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (start span : Nat) :
    Run prepared (NativeManifest.budget bound start span) :=
  let worlds := finish prepared start span
  let original := acquired (.nativeManifestInputs bound start false) (by trivial) (length (Authority.recordsAt bound start))
  let oldChallenges := withNat (lit start ⊞ lit 1) _ (fun ordinal =>
    acquired (.nativeManifestInputs bound ordinal true) (by trivial) (length (Authority.challengesAt bound ordinal)))
  let candidate := withNat (lit start ⊞ lit span) _ (fun ordinal =>
    acquired (.nativeManifestInputs bound ordinal false) (by trivial) (length (Authority.recordsAt bound ordinal)))
  let newChallenges := withNat (finish prepared start span) _ (fun ordinal =>
    acquired (.nativeManifestInputs bound ordinal true) (by trivial) (length (Authority.challengesAt bound ordinal)))
  let made := lit 10 ⊞ lit 2 ⊠ borrow 0 worlds ⊞ lit 17 ⊠ borrow 1 original ⊞
    lit 5 ⊠ borrow 2 oldChallenges ⊞ lit 10 ⊠ borrow 3 candidate ⊞ lit 3 ⊠ borrow 4 newChallenges
  retain worlds (retain original (retain oldChallenges (retain candidate (retain newChallenges made))))

def evaluation (bound : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (start span : Nat) :
    Run prepared (NativeTensor.evaluationBudget bound start span) :=
  withNat (finish prepared start span) _ (fun count => frames prepared bound.source.input count) ⊞
    profile prepared bound start span ⊞ manifest prepared bound start span


def pair (index : Index prepared) (scope : CellScope prepared index)
    (previous new : Whole.Intent scope) (table : Whole.Table scope) :
    Run prepared (Whole.Work.sourcePresentBudget scope input.span new previous table) :=
  evaluation prepared (Whole.Materialization.bound scope input.span new (Whole.opponent scope table))
    (initial input prepared.saved[index].point).depth (Whole.extent scope input.span new) ⊞
  evaluation prepared (Whole.Materialization.bound scope input.span previous (Whole.opponent scope table))
    (initial input prepared.saved[index].point).depth (Whole.extent scope input.span previous)

theorem pair_is_original_and_every_operation_is_valid (index : Index prepared)
    (scope : CellScope prepared index) (previous new : Whole.Intent scope) (table : Whole.Table scope) :
    (pair prepared index scope previous new table).value =
        Whole.Work.sourcePresentBudget scope input.span new previous table ∧
      ∀ event ∈ (pair prepared index scope previous new table).work,event.Valid prepared :=
  ⟨(pair prepared index scope previous new table).exact,(pair prepared index scope previous new table).sound⟩

end NativeSourceShape

def presentRow (index : Index prepared) (scope : CellScope prepared index)
    (previous new : Whole.Intent scope) (table : Whole.Table scope) :
    Run prepared (Whole.Work.admissionBudget scope input.span previous new (.present table)) :=
  let current := Whole.Materialization.present scope input.span new (Whole.opponent scope table)
  let original := Whole.Materialization.present scope input.span previous (Whole.opponent scope table)
  let made := plus (NativeSourceShape.pair prepared index scope previous new table)
    (PresentShape.present prepared (initial input prepared.saved[index].point) current.value original.value)
  ⟨made.value,by
    rw [made.exact]
    dsimp only [Query.answer,Whole.Work.admissionBudget]
    rw [Whole.Materialization.present_exact,Whole.Materialization.present_exact],
    [.evaluation index scope new table] ++ current.work.map (Event.sourceStep index scope new table) ++
      [.evaluation index scope previous table] ++ original.work.map (Event.sourceStep index scope previous table) ++
      [.comparisonShape index scope current.value original.value] ++ made.work,by
    intro event inside
    simp only [List.mem_append,List.mem_singleton,List.mem_map] at inside
    rcases inside with ((((same | ⟨_,_,same⟩) | same) | ⟨_,_,same⟩) | same) | last
    · subst event;trivial
    · subst event;trivial
    · subst event;trivial
    · subst event;trivial
    · subst event;trivial
    · exact made.sound event last⟩

namespace NativeFutureShape
variable (index : Index prepared) (scope : CellScope prepared index)
  (intent : Whole.Intent scope) (table : Whole.Table scope) (word : List (Future.Recovery.Action seed))

structure Emission where
  private mk ::
  value : Option (Future.Recovery.Assessment.Report (initial input prepared.saved[index].point).model)
  work : List (NativeTensor.Event Party Good Port Technology Instrument)
  budget : Run prepared (Whole.Materialization.futureBudget scope input.span intent (Whole.opponent scope table) word)
  value_exact : value = (Whole.Materialization.future scope input.span intent (Whole.opponent scope table) word).value
  work_exact : work = (Whole.Materialization.future scope input.span intent (Whole.opponent scope table) word).work

private def acquired {n : Nat} (made : Run prepared n) : Run prepared n :=
  ⟨made.value,made.exact,.nativeFutureInputs index scope intent table word :: made.work,by
    intro event inside
    rcases List.mem_cons.mp inside with same | later
    · subst event;trivial
    · exact made.sound event later⟩

def produce : Emission prepared index scope intent table word :=
  let source := Whole.target scope input.span intent (Whole.opponent scope table)
  match actual : Future.produce (initial input prepared.saved[index].point).model
      (initial input prepared.saved[index].point).depth source.indexed
      (Whole.count scope input.span intent) word with
  | .inl _ => by
    dsimp only [source] at actual
    have cost : Run prepared (Whole.Materialization.futureBudget scope input.span intent (Whole.opponent scope table) word) := by
      simpa only [Whole.Materialization.futureBudget,actual] using (mark .nativeRow (lit 0) : Run prepared 0)
    exact ⟨none,[],acquired prepared index scope intent table word cost,
      by simp only [Whole.Materialization.future,actual],by simp only [Whole.Materialization.future,actual]⟩
  | .inr receipt => by
    dsimp only [source] at actual
    let restored := Future.Recovery.produceWith (old := (initial input prepared.saved[index].point).model) input.pricing receipt
    let emitted := NativeTensor.report restored (initial input prepared.saved[index].point).depth source.property
    let calculated := NativeSourceShape.evaluation prepared restored.bound
      (initial input prepared.saved[index].point).depth
      (restored.walk.finish.depth-(initial input prepared.saved[index].point).depth)
    have cost : Run prepared (Whole.Materialization.futureBudget scope input.span intent (Whole.opponent scope table) word) := by
      simpa only [Whole.Materialization.futureBudget,actual,NativeTensor.reportBudget] using calculated
    exact ⟨some emitted.value,emitted.work,acquired prepared index scope intent table word cost,
      by simp only [Whole.Materialization.future,actual];rfl,
      by simp only [Whole.Materialization.future,actual];rfl⟩

variable {actual : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input actual.source.code}
def report (cursor : Cursor actual driver) (new previous : Future.Recovery.Assessment.Report cursor.model) :
    Run prepared (NativeAdmission.reportBudget cursor new previous) :=
  lit 12 ⊞ PresentShape.profile prepared new.evaluation.profile previous.evaluation.profile ⊞
    PresentShape.inventoryPair prepared new.evaluation.native previous.evaluation.native ⊞
    lit 2 ⊠ length (Window.axes cursor.model cursor.depth)

def comparison (cursor : Cursor actual driver) :
    (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) →
    Run prepared (NativeAdmission.futureBudget cursor new previous)
  | some current,some original => mark .nativeRow (report prepared cursor current original ⊞ lit 2)
  | none,none | some _,none | none,some _ => mark .nativeRow (lit 1)
end NativeFutureShape


def futureRow (index : Index prepared) (scope : CellScope prepared index)
    (previous new : Whole.Intent scope) (table : Whole.Table scope) (word : List (Future.Recovery.Action seed)) :
    Run prepared (Whole.Work.admissionBudget scope input.span previous new (.future table word)) :=
  let current := NativeFutureShape.produce prepared index scope new table word
  let original := NativeFutureShape.produce prepared index scope previous table word
  let made := current.budget ⊞ original.budget ⊞
    NativeFutureShape.comparison prepared (initial input prepared.saved[index].point) current.value original.value
  ⟨made.value,by
    simpa only [Whole.Work.admissionBudget,Whole.Work.sourceFutureBudget,
      current.value_exact,original.value_exact,Whole.Materialization.future_exact] using made.exact,
    [.futureShape index scope current.value original.value] ++
      current.work.map (Event.sourceStep index scope new table) ++
      original.work.map (Event.sourceStep index scope previous table) ++ made.work,by
    intro event inside
    simp only [List.mem_append,List.mem_singleton,List.mem_map] at inside
    rcases inside with ((same | ⟨_,_,same⟩) | ⟨_,_,same⟩) | last
    · subst event;trivial
    · subst event;trivial
    · subst event;trivial
    · exact made.sound event last⟩


def fundingRow (index : Index prepared) (scope : CellScope prepared index)
    (previous new : Whole.Intent scope) (table : Whole.Table scope) (word : List (Future.Recovery.Action seed)) :
    Run prepared (Whole.Work.admissionBudget scope input.span previous new (.funding table word)) :=
  let made : Run prepared 3 := lit 3
  ⟨made.value,made.exact,.fundingInputs index scope previous new table word :: made.work,by
    intro event inside
    rcases List.mem_cons.mp inside with same | later
    · subst event;trivial
    · exact made.sound event later⟩

def admissionRow (index : Index prepared) (scope : CellScope prepared index)
    (previous new : Whole.Intent scope) : (row : Whole.Decision.Row scope) →
    Run prepared (Whole.Work.admissionBudget scope input.span previous new row)
  | .deployment => mark .nativeRow (lit 1)
  | .present table => mark .nativeRow (presentRow prepared index scope previous new table)
  | .future table word => mark .nativeRow (futureRow prepared index scope previous new table word)
  | .funding table word => mark .nativeRow (fundingRow prepared index scope previous new table word)

def admissionScope (index : Index prepared) (scope : CellScope prepared index) :
    Run prepared (Whole.Work.admissionCeiling scope input.span) :=
  let made := ceiling _ (fun previous => ceiling _ (fun new =>
    ceiling _ (admissionRow prepared index scope previous new) (Whole.Decision.rows scope))
      (Whole.intents scope)) (Whole.intents scope)
  ⟨made.value,made.exact.trans (by
    unfold Whole.Work.admissionCeiling
    simp only [policy_ceiling_eq_foldr,Whole.Work.ceiling_eq_foldr]),made.work,made.sound⟩

def admissionStage (index : Index prepared) : (stage : Stage input prepared.saved[index].point) →
    Run prepared (Work.localAdmissionCeiling stage)
  | .ready scope => admissionScope prepared index scope
  | .stopped _ | .blocked _ => mark .nativeRow (lit 1)

def nativeAdmissionCeiling : Run prepared (Work.nativeAdmissionCeiling prepared) :=
  largest (lit 1) (ceiling _ (fun index => admissionStage prepared index prepared.saved[index].stage) (keys prepared))
def admissionCeiling : Run prepared (Work.admissionCeiling prepared) := largest (nativeAdmissionCeiling prepared) (signatureCeiling prepared)


namespace NativeBenefitShape
variable {prepared}
def sumCosts {α : Type} (cost : α → Nat) (run : (item : α) → Run prepared (cost item)) :
    (items : List α) → Run prepared (List.sum (items.map cost))
  | [] => mark .listEnd (lit 0)
  | head::tail => mark .listPair (run head ⊞ sumCosts cost run tail)

variable (prepared)
def inventoryDue (new previous : Feedback.Authority.Trace.Manifest Party Good Port Technology Instrument) :
    Run prepared (NativeBenefit.inventoryDueBudget new previous) :=
  PresentShape.inventory prepared new ⊞ PresentShape.inventory prepared previous ⊞
    PresentShape.subperm prepared (fun _ => PresentShape.rowCount prepared new)
      (fun _ => PresentShape.rowCount prepared previous)

variable {actual : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input actual.source.code}
def present (cursor : Cursor actual driver) (new previous : Evaluation cursor.source.val.code) :
    Run prepared (NativeBenefit.presentBudget cursor new previous) :=
  lit 9 ⊞ inventoryDue prepared new.native previous.native ⊞
    lit 2 ⊠ length (Window.axes cursor.model cursor.depth)

def future (cursor : Cursor actual driver) :
    (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) →
    Run prepared (NativeBenefit.futureBudget cursor new previous)
  | some current,some original => mark .nativeRow (present prepared cursor current.evaluation original.evaluation ⊞ lit 3)
  | none,none | some _,none | none,some _ => mark .nativeRow (lit 1)

def presentAtom (index : Index prepared) (scope : CellScope prepared index)
    (previous new : Whole.Intent scope) (table : Whole.Table scope) :
    Run prepared (Whole.Work.presentAtomBudget scope input.span new previous table) :=
  let current := Whole.Materialization.present scope input.span new (Whole.opponent scope table)
  let original := Whole.Materialization.present scope input.span previous (Whole.opponent scope table)
  let made : Run prepared (Whole.Work.sourcePresentBudget scope input.span new previous table +
      NativeBenefit.presentBudget (initial input prepared.saved[index].point) current.value original.value) :=
    NativeSourceShape.pair prepared index scope previous new table ⊞ present prepared (initial input prepared.saved[index].point) current.value original.value
  ⟨made.value,by
    rw [made.exact]
    dsimp only [Whole.Work.presentAtomBudget]
    rw [Whole.Materialization.present_exact,Whole.Materialization.present_exact],
    [.evaluation index scope new table] ++ current.work.map (Event.sourceStep index scope new table) ++
      [.evaluation index scope previous table] ++ original.work.map (Event.sourceStep index scope previous table) ++
      [.comparisonShape index scope current.value original.value] ++ made.work,by
    intro event inside
    simp only [List.mem_append,List.mem_singleton,List.mem_map] at inside
    rcases inside with ((((same | ⟨_,_,same⟩) | same) | ⟨_,_,same⟩) | same) | last
    · subst event;trivial
    · subst event;trivial
    · subst event;trivial
    · subst event;trivial
    · subst event;trivial
    · exact made.sound event last⟩

def futureAtom (index : Index prepared) (scope : CellScope prepared index)
    (previous new : Whole.Intent scope) (table : Whole.Table scope) (word : List (Future.Recovery.Action seed)) :
    Run prepared (Whole.Work.futureAtomBudget scope input.span new previous table word) :=
  let current := NativeFutureShape.produce prepared index scope new table word
  let original := NativeFutureShape.produce prepared index scope previous table word
  let made : Run prepared (Whole.Work.sourceFutureBudget scope input.span new previous table word +
      NativeBenefit.futureBudget (initial input prepared.saved[index].point) current.value original.value) :=
    current.budget ⊞ original.budget ⊞ future prepared (initial input prepared.saved[index].point) current.value original.value
  ⟨made.value,by
    simpa only [Whole.Work.futureAtomBudget,Whole.Work.sourceFutureBudget,
      current.value_exact,original.value_exact,Whole.Materialization.future_exact] using made.exact,
    [.futureShape index scope current.value original.value] ++
      current.work.map (Event.sourceStep index scope new table) ++
      original.work.map (Event.sourceStep index scope previous table) ++ made.work,by
    intro event inside
    simp only [List.mem_append,List.mem_singleton,List.mem_map] at inside
    rcases inside with ((same | ⟨_,_,same⟩) | ⟨_,_,same⟩) | later
    · subst event;trivial
    · subst event;trivial
    · subst event;trivial
    · exact made.sound event later⟩

def table (index : Index prepared) (scope : CellScope prepared index)
    (previous new : Whole.Intent scope) (rival : Whole.Table scope) :
    Run prepared (Whole.Work.benefitTableBudget scope input.span new previous rival) :=
  let words := Future.Recovery.capabilities (initial input prepared.saved[index].point).model
    (initial input prepared.saved[index].point).depth
  presentAtom prepared index scope previous new rival ⊞
    sumCosts (fun word => Whole.Work.futureAtomBudget scope input.span new previous rival word+1)
      (fun word => futureAtom prepared index scope previous new rival word ⊞ lit 1) words ⊞
    lit 4 ⊠ length words ⊞ lit 3

def pair (index : Index prepared) (scope : CellScope prepared index)
    (previous new : Whole.Intent scope) : Run prepared (Whole.Work.benefitBudget scope input.span new previous) :=
  sumCosts (fun rival => Whole.Work.benefitTableBudget scope input.span new previous rival+1)
    (fun rival => table prepared index scope previous new rival ⊞ lit 1) (Whole.tables scope)

def scope (index : Index prepared) (cell : CellScope prepared index) :
    Run prepared (Whole.Work.benefitCeiling cell input.span) :=
  let made := ceiling (fun new => Work.ceiling (Whole.Work.benefitBudget cell input.span new) (Whole.intents cell))
    (fun new => ceiling (Whole.Work.benefitBudget cell input.span new)
      (fun previous => pair prepared index cell previous new) (Whole.intents cell)) (Whole.intents cell)
  ⟨made.value,made.exact.trans (by
    unfold Whole.Work.benefitCeiling
    simp only [policy_ceiling_eq_foldr,Whole.Work.ceiling_eq_foldr]),
    .benefitInputs index cell (Whole.tables cell) (Whole.intents cell)
      (Future.Recovery.capabilities (initial input prepared.saved[index].point).model
        (initial input prepared.saved[index].point).depth) :: made.work,by
    intro event inside
    rcases List.mem_cons.mp inside with same | later
    · subst event;trivial
    · exact made.sound event later⟩

def stage (index : Index prepared) : (current : Stage input prepared.saved[index].point) →
    Run prepared (Work.localBenefitCeiling current)
  | .ready cell => scope prepared index cell
  | .stopped _ | .blocked _ => mark .nativeRow (lit 1)

end NativeBenefitShape
set_option maxHeartbeats 6000000

def benefitCeiling : Run prepared (Work.benefitCeiling prepared) := ceiling (fun index => Work.localBenefitCeiling prepared.saved[index].stage)
  (fun index => NativeBenefitShape.stage prepared index prepared.saved[index].stage) (keys prepared)

/-- The same cached operands generate all arithmetic; no finished workBudget is read as a leaf. -/
def generate : Run prepared (Work.workBudget prepared) :=
  let count := length (sections prepared)
  let admission := length (rows prepared) ⊠ (admissionCeiling prepared ⊞ lit 1)
  let benefit := length (keys prepared) ⊠ (benefitCeiling prepared ⊞ lit 1)
  let strict := lit 2 ⊠ borrow 2 benefit ⊞ lit 2
  let verification := borrow 1 admission ⊞ lit 1 ⊞
    (borrow 0 count ⊠ (borrow 1 admission ⊞ borrow 3 strict ⊞ lit 3))
  let result := (borrow 0 count ⊠ (borrow 1 admission ⊞ lit 1)) ⊞
    (borrow 0 count ⊠ (borrow 3 strict ⊞ lit 1)) ⊞ borrow 4 verification ⊞
    (borrow 0 count ⊠ borrow 1 admission) ⊞ lit 1
  retain count (retain admission (retain benefit (retain strict (retain verification result))))

variable {prepared}
def Event.expanded : Event prepared → Bool
  | .branch _ | .sourceStep .. => true
  | _ => false
def controlSteps {n : Nat} (made : Run prepared n) : Nat := (made.work.filter Event.expanded).length
def pending {n : Nat} (made : Run prepared n) : List (Event prepared) := made.work.filter (fun event => !event.expanded)

theorem every_event_is_either_structural_or_retained {n : Nat} (made : Run prepared n) (event : Event prepared)
    (inside : event ∈ made.work) : event.expanded = true ∨ event ∈ pending made := by
  cases kind : event.expanded with
  | true => exact Or.inl rfl
  | false => exact Or.inr (List.mem_filter.mpr ⟨inside,by simp [kind]⟩)

theorem present_row_counts_exactly_its_evaluation_and_both_shape_traces (index : Index prepared)
    (scope : CellScope prepared index) (previous new : Whole.Intent scope) (table : Whole.Table scope) :
    controlSteps (presentRow prepared index scope previous new table) =
      (Whole.Materialization.present scope input.span new (Whole.opponent scope table)).work.length+
      (Whole.Materialization.present scope input.span previous (Whole.opponent scope table)).work.length+
      (controlSteps (NativeSourceShape.pair prepared index scope previous new table) +
      controlSteps (PresentShape.present prepared (initial input prepared.saved[index].point)
        (Whole.Materialization.present scope input.span new (Whole.opponent scope table)).value
        (Whole.Materialization.present scope input.span previous (Whole.opponent scope table)).value)) := by
  have mapped (intent : Whole.Intent scope) (events : List (NativeTensor.Event Party Good Port Technology Instrument)) :
      ((events.map (Event.sourceStep index scope intent table)).filter Event.expanded).length = events.length := by
    induction events with
    | nil => rfl
    | cons head tail ih => simpa only [List.map_cons,List.filter_cons,Event.expanded,if_true,List.length_cons] using congrArg Nat.succ ih
  simp only [controlSteps,presentRow,plus,combine,List.filter_append,List.filter_cons,
    Event.expanded,Bool.false_eq_true,if_false,List.filter_nil,List.length_append,List.length_nil,Nat.add_zero,Nat.zero_add]
  rw [mapped,mapped]

variable (prepared)
theorem generated_budget_is_original_and_every_operation_is_valid :
    (generate prepared).value = Work.workBudget prepared ∧
    ∀ event ∈ (generate prepared).work,event.Valid prepared :=
  ⟨(generate prepared).exact,(generate prepared).sound⟩

theorem generated_signature_budget_covers_the_original_comparison (term : Section prepared) (first second : Index prepared) :
    Work.controlSteps prepared (Work.signature prepared term first second).work ≤ (signatureAt prepared term first second).value := by
  rw [(signatureAt prepared term first second).exact]
  exact Work.signature_cost_bound prepared term first second

theorem future_row_counts_exactly_its_evaluation_and_both_shape_traces (index : Index prepared)
    (scope : CellScope prepared index) (previous new : Whole.Intent scope) (table : Whole.Table scope)
    (word : List (Future.Recovery.Action seed)) :
    controlSteps (futureRow prepared index scope previous new table word) =
      (NativeFutureShape.produce prepared index scope new table word).work.length +
      (NativeFutureShape.produce prepared index scope previous table word).work.length +
      (controlSteps (NativeFutureShape.produce prepared index scope new table word).budget +
        controlSteps (NativeFutureShape.produce prepared index scope previous table word).budget +
        controlSteps (NativeFutureShape.comparison prepared (initial input prepared.saved[index].point)
          (NativeFutureShape.produce prepared index scope new table word).value
          (NativeFutureShape.produce prepared index scope previous table word).value)) := by
  have mapped (intent : Whole.Intent scope) (events : List (NativeTensor.Event Party Good Port Technology Instrument)) :
      ((events.map (Event.sourceStep index scope intent table)).filter Event.expanded).length = events.length := by
    induction events with
    | nil => rfl
    | cons head tail ih => simpa only [List.map_cons,List.filter_cons,Event.expanded,if_true,List.length_cons] using congrArg Nat.succ ih
  simp only [controlSteps,futureRow,plus,combine,List.filter_append,List.filter_cons,
    Event.expanded,Bool.false_eq_true,if_false,List.filter_nil,List.length_append,List.length_nil,Nat.add_zero,Nat.zero_add]
  rw [mapped,mapped]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget
