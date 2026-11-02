import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeSourceFrames
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeProfile
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
variable {Party Good Port Technology Instrument : Type}

/-- Source-level calls and assembly instructions. The called account/image/history
    kernels and scalar/memory primitive internals retain their native obligations. -/
inductive Event (Party Good Port Technology Instrument : Type) where
  | account (depth : Nat)
  | terminal (depth : Nat)
  | field (index : Fin 6)
  | skipOriginal
  | debtRead (newborn : Bool) (value : Identity.DebtImage Party Good Port (Mandate.State Party Technology) Instrument)
  | debtWrite (newborn : Bool) (value : Identity.DebtImage Party Good Port (Mandate.State Party Technology) Instrument)
  | rightRow (slot : Nat)
  | holding (slot : Nat) (holder : Party) (remaining received : ℚ)
  | add (left right : ℚ)
  | rightWrite (value : ℚ)
  | claim (instrument : Instrument) (debtor creditor : Party) (raw ledger : ℚ)
  | subtract (left right : ℚ)
  | claimWrite (value : ℚ)
  | service (slot : Nat) (first : Option Nat)
  | serviceWrite (first : Option Nat)
  | technology (value : Mandate.State Party Technology)
  | clock (value : ℚ)
  | round (value : Nat)
  | assemble
  deriving DecidableEq
local notation "Events" => List (Event Party Good Port Technology Instrument)
private structure Part (α : Type) (Party Good Port Technology Instrument : Type) where
  value : α
  work : List (Event Party Good Port Technology Instrument)
local notation "Result" => Part
private def map {α β : Type} (produce : α → Result β Party Good Port Technology Instrument) : List α → Result (List β) Party Good Port Technology Instrument
  | [] => ⟨[],[]⟩
  | head::tail => let first := produce head;let rest := map produce tail
      ⟨first.value::rest.value,first.work++rest.work⟩
private def flatMap {α β : Type} (produce : α → Result (List β) Party Good Port Technology Instrument) : List α → Result (List β) Party Good Port Technology Instrument
  | [] => ⟨[],[]⟩
  | head::tail => let first := produce head;let rest := flatMap produce tail
      ⟨first.value++rest.value,first.work++rest.work⟩
private def drop {α : Type} : Nat → List α → Result (List α) Party Good Port Technology Instrument
  | 0,items => ⟨items,[]⟩
  | _+1,[] => ⟨[],[]⟩
  | count+1,_::tail => let rest := drop count tail;⟨rest.value,.skipOriginal::rest.work⟩
private theorem map_value {α β : Type} (produce : α → Result β Party Good Port Technology Instrument) (items : List α) :
    (map produce items).value = items.map (fun item => (produce item).value) := by
  induction items <;> simp_all [map]
private theorem flatMap_value {α β : Type} (produce : α → Result (List β) Party Good Port Technology Instrument) (items : List α) :
    (flatMap produce items).value = items.flatMap (fun item => (produce item).value) := by
  induction items <;> simp_all [flatMap]
private theorem map_work {α β : Type} (produce : α → Result β Party Good Port Technology Instrument) (items : List α) :
    (map produce items).work.length = (items.map (fun item => (produce item).work.length)).sum := by
  induction items <;> simp_all [map]
private theorem flatMap_work {α β : Type} (produce : α → Result (List β) Party Good Port Technology Instrument) (items : List α) :
    (flatMap produce items).work.length = (items.map (fun item => (produce item).work.length)).sum := by
  induction items <;> simp_all [flatMap]
private theorem drop_value {α : Type} (count : Nat) (items : List α) :
    (drop (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) count items).value = items.drop count := by
  induction count generalizing items with
  | zero => rfl
  | succ count ih => cases items <;> simp [drop,ih]
private theorem drop_work {α : Type} (count : Nat) (items : List α) :
    (drop (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) count items).work.length ≤ count := by
  induction count generalizing items with
  | zero => simp [drop]
  | succ count ih => cases items <;> simp [drop];exact ih _

variable [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (start span : Nat)
local notation "Profile" => Settlement.Profile Party Good Port (Mandate.State Party Technology) Instrument
private def debts (newborn : Bool) (slots : List (ResponsibilityLifecycle.ObligationSlot (Financial.vocabulary bound.source.input))) : Result (List (Identity.DebtImage Party Good Port (Mandate.State Party Technology) Instrument)) Party Good Port Technology Instrument :=
  map (fun slot => let image := Identity.debtImage bound.source.code bound.source.input slot
    ⟨image,[.debtRead newborn image,.debtWrite newborn image]⟩) slots
private def rights : Result (List (List ℚ)) Party Good Port Technology Instrument :=
  map (fun index : Fin (Window.first bound start).current.slots.length =>
    let actual := Window.migration bound start span index
    let holders := map (fun holder =>
      let remaining := Financial.slotBalance bound.source.input actual.slot holder
      let received := actual.path.receivedBy bound.source.input holder
      ⟨remaining+received,[.holding index.val holder remaining received,.add remaining received,.rightWrite (remaining+received)]⟩) bound.source.code.parties
    ⟨holders.value,.rightRow index.val::holders.work⟩) (List.finRange (Window.first bound start).current.slots.length)
private def claims : Result (List ℚ) Party Good Port Technology Instrument :=
  flatMap (fun instrument => flatMap (fun debtor => map (fun creditor =>
    let raw := (Window.terminal bound start span).claims instrument debtor creditor
    let ledger := Financial.BalanceConservation.ledgerClaims bound.source.input (Window.last bound start span).current instrument debtor creditor
    ⟨raw-ledger,[.claim instrument debtor creditor raw ledger,.subtract raw ledger,.claimWrite (raw-ledger)]⟩)
    bound.source.code.parties) bound.source.code.parties) bound.source.code.instruments
private def services : Result (List (Option Nat)) Party Good Port Technology Instrument :=
  map (fun index : Fin bound.source.code.task.slots.length =>
    let first := Identity.firstService bound.source start index
    ⟨first,[.service index.val first,.serviceWrite first]⟩) (List.finRange bound.source.code.task.slots.length)
private def generate : Result Profile Party Good Port Technology Instrument :=
  let original := debts bound false (Window.first bound start).current.slots
  let skipped := drop (Window.first bound start).current.slots.length (Window.last bound start span).current.slots
  let newborn := debts bound true skipped.value
  let held := rights bound start span
  let uncovered := claims bound start span
  let served := services bound start
  let current := Window.terminal bound start span
  ⟨⟨original.value,newborn.value,held.value,uncovered.value,served.value,⟨current.technology,current.clock,current.round⟩⟩,
    [.account (start+1),.account (Window.finish start span),.terminal (Window.finish start span),.field 0] ++ original.work ++
    [.field 1] ++ skipped.work ++ newborn.work ++ [.field 2] ++ held.work ++ [.field 3] ++ uncovered.work ++
    [.field 4] ++ served.work ++ [.field 5,.technology current.technology,.clock current.clock,.round current.round,.assemble]⟩
private theorem generated_exact : (generate bound start span).value = Window.profile bound start span := by
  dsimp only [generate]
  congr 1
  · simp [debts,map_value,Identity.financeImage]
  · simp [debts,map_value,drop_value,Identity.financeImage,List.map_drop]
  · simp [rights,map_value,Window.holdings,Settlement.rights,List.finRange,Function.comp_def]
  · simp [claims,flatMap_value,map_value]
  · simp [services,map_value]

/-- The quote uses only source shapes, never a generated Profile or comparison answer. -/
def budget : Nat :=
  13 + 3*(Window.first bound start).current.slots.length + 2*(Window.last bound start span).current.slots.length +
    (Window.first bound start).current.slots.length*(1+3*bound.source.code.parties.length) +
    bound.source.code.instruments.length*(bound.source.code.parties.length*(3*bound.source.code.parties.length)) +
    2*bound.source.code.task.slots.length
private theorem debts_work (newborn : Bool) (slots : List (ResponsibilityLifecycle.ObligationSlot (Financial.vocabulary bound.source.input))) :
    (debts bound newborn slots).work.length = 2*slots.length := by
  simp [debts,map_work,Nat.mul_comm]
private theorem rights_work : (rights bound start span).work.length =
    (Window.first bound start).current.slots.length*(1+3*bound.source.code.parties.length) := by
  simp [rights,map_work,Nat.mul_comm,Nat.add_comm]
private theorem claims_work : (claims bound start span).work.length =
    bound.source.code.instruments.length*(bound.source.code.parties.length*(3*bound.source.code.parties.length)) := by
  simp [claims,flatMap_work,map_work,Nat.mul_comm]
private theorem services_work : (services bound start).work.length = 2*bound.source.code.task.slots.length := by
  simp [services,map_work,Nat.mul_comm]
private theorem generated_work_bound : (generate bound start span).work.length ≤ budget bound start span := by
  have skip := drop_work (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
    (Window.first bound start).current.slots.length (Window.last bound start span).current.slots
  have remaining : (drop (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
      (Window.first bound start).current.slots.length (Window.last bound start span).current.slots).value.length ≤
      (Window.last bound start span).current.slots.length := by
    rw [drop_value,List.length_drop];omega
  simp only [generate,List.length_append,List.length_cons,List.length_nil,debts_work,rights_work,claims_work,services_work,budget]
  omega

structure Compilation where
  private mk ::
  profile : Profile
  work : Events
  exact : profile = Window.profile bound start span
  private generated : profile = (generate bound start span).value ∧ work = (generate bound start span).work

def compile : Compilation bound start span :=
  let made := generate bound start span
  ⟨made.value,made.work,generated_exact bound start span,⟨rfl,rfl⟩⟩
theorem work_bound : (compile bound start span).work.length ≤ budget bound start span := generated_work_bound bound start span

def Compilation.evaluation (made : Compilation bound start span) : Evaluation bound.source.code where
  legal := Window.legal bound start span
  complete := (List.finRange bound.source.code.task.slots.length).all fun index =>
    (Identity.firstService bound.source (Window.finish start span-1) index).isSome
  profile := made.profile
  native := Window.manifest bound start span
  value := Window.value bound start span

theorem Compilation.evaluation_exact (made : Compilation bound start span) :
    made.evaluation = Window.evaluate bound start span := by
  unfold Compilation.evaluation
  rw [made.exact]
  rfl

def evaluation : Evaluation bound.source.code := (compile bound start span).evaluation
theorem evaluation_exact : evaluation bound start span = Window.evaluate bound start span :=
  Compilation.evaluation_exact _ _ _ _

private def firstFrom (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) :=
  frames.accounts ⟨start+1,by dsimp only [Window.finish];omega⟩
private def lastFrom (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) :=
  frames.endpoint bound.source.input
private theorem firstFrom_exact (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) :
    firstFrom bound start span frames = Window.first bound start := frames.account_exact _
private theorem lastFrom_exact (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) :
    lastFrom bound start span frames = Window.last bound start span := frames.endpoint_exact _
private def rightsUsing (first : (Financial.process bound.source.input).GeneratedState) (same : first = Window.first bound start) : Result (List (List ℚ)) Party Good Port Technology Instrument :=
  map (fun index : Fin first.current.slots.length =>
    let actual := Financial.Migration.actual bound.source.input (start+1) span index.val
      (first.current.slots.get index)
      (by
        change (Window.first bound start).current.slots[index.val]? = _
        rw [← same]
        exact List.getElem?_eq_getElem index.isLt)
    let holders := map (fun holder =>
      let remaining := Financial.slotBalance bound.source.input actual.slot holder
      let received := actual.path.receivedBy bound.source.input holder
      ⟨remaining+received,[.holding index.val holder remaining received,.add remaining received,.rightWrite (remaining+received)]⟩) bound.source.code.parties
    ⟨holders.value,.rightRow index.val::holders.work⟩) (List.finRange first.current.slots.length)
private theorem rightsUsing_exact (first : (Financial.process bound.source.input).GeneratedState) (same : first = Window.first bound start) :
    rightsUsing bound start span first same = rights bound start span := by
  subst first
  rfl
private def rightsFrom (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) :=
  rightsUsing bound start span (firstFrom bound start span frames) (firstFrom_exact bound start span frames)
private theorem rightsFrom_exact (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) :
    rightsFrom bound start span frames = rights bound start span := rightsUsing_exact bound start span _ _
private def claimsFrom (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) : Result (List ℚ) Party Good Port Technology Instrument :=
  flatMap (fun instrument => flatMap (fun debtor => map (fun creditor =>
    let raw := (Window.terminal bound start span).claims instrument debtor creditor
    let ledger := Financial.BalanceConservation.ledgerClaims bound.source.input (lastFrom bound start span frames).current instrument debtor creditor
    ⟨raw-ledger,[.claim instrument debtor creditor raw ledger,.subtract raw ledger,.claimWrite (raw-ledger)]⟩)
    bound.source.code.parties) bound.source.code.parties) bound.source.code.instruments
private theorem claimsFrom_exact (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) :
    claimsFrom bound start span frames = claims bound start span := by
  unfold claimsFrom
  simp only [lastFrom_exact]
  rfl
private def generateFrom (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) : Result Profile Party Good Port Technology Instrument :=
  let first := firstFrom bound start span frames
  let last := lastFrom bound start span frames
  let original := debts bound false first.current.slots
  let skipped := drop first.current.slots.length last.current.slots
  let newborn := debts bound true skipped.value
  let held := rightsFrom bound start span frames
  let uncovered := claimsFrom bound start span frames
  let served := services bound start
  let current := Window.terminal bound start span
  ⟨⟨original.value,newborn.value,held.value,uncovered.value,served.value,⟨current.technology,current.clock,current.round⟩⟩,
    [.account (start+1),.account (Window.finish start span),.terminal (Window.finish start span),.field 0] ++ original.work ++
    [.field 1] ++ skipped.work ++ newborn.work ++ [.field 2] ++ held.work ++ [.field 3] ++ uncovered.work ++
    [.field 4] ++ served.work ++ [.field 5,.technology current.technology,.clock current.clock,.round current.round,.assemble]⟩
private theorem generateFrom_exact (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) :
    generateFrom bound start span frames = generate bound start span := by
  simp only [generateFrom,generate,firstFrom_exact,lastFrom_exact,rightsFrom_exact,claimsFrom_exact]

/-- The shared prefix is sealed by its own source generator; no account result is a caller premise. -/
def compileFrom (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) : Compilation bound start span :=
  let made := generateFrom bound start span frames
  ⟨made.value,made.work,by dsimp only [made];rw [generateFrom_exact];exact generated_exact bound start span,
    by dsimp only [made];rw [generateFrom_exact];exact ⟨rfl,rfl⟩⟩
theorem workFrom_bound (frames : NativeSourceFrames.Compilation bound.source.input (Window.finish start span)) :
    (compileFrom bound start span frames).work.length ≤ budget bound start span := by
  simp only [compileFrom,generateFrom_exact]
  exact generated_work_bound bound start span

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeProfile
