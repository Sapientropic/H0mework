import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeMovement
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeSourceFrames
open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

/-- Iteration and writes are explicit; root and financial consume kernels retain their native costs. -/
inductive Event where
  | initial
  | visit (ordinal : Nat)
  | inventory (ordinal rows : Nat)
  | consume (ordinal row : Nat)
  | financial (ordinal row : Nat) (event : NativeMovement.Event)
  | write (ordinal row : Nat)
  | account (ordinal : Nat)
  deriving DecidableEq
private def fold (ordinal : Nat) : Nat → List (Financial.InstructionOrigin input) →
    (Financial.process input).GeneratedState → (Financial.process input).GeneratedState × List Event
  | _,[],state => (state,[])
  | row,origin::tail,state =>
      let made := NativeMovement.compile input origin state
      let rest := fold ordinal (row+1) tail (made.result.next input)
      (rest.1,[.consume ordinal row] ++ made.work.map (Event.financial ordinal row) ++ [.write ordinal row] ++ rest.2)
private theorem fold_exact (ordinal row : Nat) (origins : List (Financial.InstructionOrigin input))
    (state : (Financial.process input).GeneratedState) :
    (fold input ordinal row origins state).1 = Financial.consumeOrigins input origins state := by
  induction origins generalizing row state with
  | nil => rfl
  | cons origin tail ih =>
    simp only [fold,Financial.consumeOrigins]
    rw [ih,(NativeMovement.compile input origin state).exact]
/-- Quotation reads incoming source states; its own computation remains pending. -/
def foldBudget : List (Financial.InstructionOrigin input) → (Financial.process input).GeneratedState → Nat
  | [],_ => 0
  | origin::tail,state => 2 + NativeMovement.budget input origin state + foldBudget tail ((Financial.consume input origin state).next input)
private theorem fold_work (ordinal row : Nat) (origins : List (Financial.InstructionOrigin input))
    (state : (Financial.process input).GeneratedState) :
    (fold input ordinal row origins state).2.length ≤ foldBudget input origins state := by
  induction origins generalizing row state with
  | nil => rfl
  | cons origin tail ih =>
    have first := NativeMovement.work_bound input origin state
    have rest := ih (row+1) ((NativeMovement.compile input origin state).result.next input)
    rw [(NativeMovement.compile input origin state).exact] at rest
    simp only [fold,List.length_append,List.length_cons,List.length_nil,List.length_map]
    rw [(NativeMovement.compile input origin state).exact]
    dsimp only [foldBudget]
    omega

private structure Built (count : Nat) where
  visits : Fin count → RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot
  accounts : Fin (count+1) → (Financial.process input).GeneratedState
  work : List Event
private def nextVisit (count : Nat)
    (visits : Fin count → RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot) :=
  match count with
  | 0 => (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot.initialVisit
  | count+1 => (visits (Fin.last count)).next rfl
omit [DecidableEq Port] in
private theorem nextVisit_exact (count : Nat)
    (visits : Fin count → RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot)
    (exactVisits : ∀ i,visits i = ProgrammeHistory.visitAt input i.val) :
    nextVisit input count visits = ProgrammeHistory.visitAt input count := by
  cases count with
  | zero => rfl
  | succ count => simp only [nextVisit,exactVisits,Fin.val_last];rfl
private def generate : (count : Nat) → Built input count
  | 0 => ⟨Fin.elim0,fun _ => .initial (Financial.process input),[.initial]⟩
  | count+1 =>
      let previous := generate count
      let visit := nextVisit input count previous.visits
      let origins := Financial.inventoryAt input visit
      let after := fold input count 0 origins (previous.accounts (Fin.last count))
      ⟨Fin.lastCases visit previous.visits,Fin.lastCases after.1 previous.accounts,
        previous.work ++ [.visit count,.inventory count origins.length] ++ after.2 ++ [.account (count+1)]⟩
private theorem generated_visits (count : Nat) :
    ∀ i,(generate input count).visits i = ProgrammeHistory.visitAt input i.val := by
  induction count with
  | zero => intro i;exact Fin.elim0 i
  | succ count ih =>
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [generate,Fin.lastCases_last,Fin.val_last]
      exact nextVisit_exact input count _ ih
    · simpa only [generate,Fin.lastCases_castSucc,Fin.val_castSucc] using ih j
private theorem generated_accounts (count : Nat) :
    ∀ i,(generate input count).accounts i = Financial.accountAt input i.val := by
  induction count with
  | zero =>
    intro i
    have h : i.val = 0 := by omega
    simp only [generate,h,Financial.accountAt]
  | succ count ih =>
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [generate,Fin.lastCases_last,Fin.val_last,fold_exact,ih,Fin.val_last]
      rw [nextVisit_exact input count _ (generated_visits input count)]
      rfl
    · simpa only [generate,Fin.lastCases_castSucc,Fin.val_castSucc] using ih j

/-- The quote contains only the original inventory and incoming account shapes, never a comparison answer. -/
def budget : Nat → Nat
  | 0 => 1
  | count+1 => budget count + 3 + foldBudget input
      (Financial.inventoryAt input (ProgrammeHistory.visitAt input count)) (Financial.accountAt input count)
private theorem generated_work (count : Nat) : (generate input count).work.length ≤ budget input count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have step := fold_work input count 0
      (Financial.inventoryAt input (nextVisit input count (generate input count).visits))
      ((generate input count).accounts (Fin.last count))
    rw [nextVisit_exact input count _ (generated_visits input count),generated_accounts] at step
    simp only [Fin.val_last] at step
    simp only [generate,List.length_append,List.length_cons,List.length_nil,budget]
    rw [nextVisit_exact input count _ (generated_visits input count),generated_accounts]
    simp only [Fin.val_last]
    omega

structure Compilation (count : Nat) where
  private mk ::
  visits : Fin count → RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot
  accounts : Fin (count+1) → (Financial.process input).GeneratedState
  work : List Event
  visit_exact : ∀ i,visits i = ProgrammeHistory.visitAt input i.val
  account_exact : ∀ i,accounts i = Financial.accountAt input i.val
  private generated : visits = (generate input count).visits ∧ accounts = (generate input count).accounts ∧ work = (generate input count).work

def compile (count : Nat) : Compilation input count :=
  let made := generate input count
  ⟨made.visits,made.accounts,made.work,generated_visits input count,generated_accounts input count,⟨rfl,rfl,rfl⟩⟩
theorem work_bound (count : Nat) : (compile input count).work.length ≤ budget input count := generated_work input count

def Compilation.endpoint {count : Nat} (made : Compilation input count) := made.accounts (Fin.last count)
theorem Compilation.endpoint_exact {count : Nat} (made : Compilation input count) :
    made.endpoint input = Financial.accountAt input count := made.account_exact _
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeSourceFrames
