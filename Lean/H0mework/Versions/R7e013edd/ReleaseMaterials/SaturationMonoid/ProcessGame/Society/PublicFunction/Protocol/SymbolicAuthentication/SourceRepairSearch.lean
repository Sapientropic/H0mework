import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceptionArchive

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceRepairSearch
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewableCodeLineage

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 {root : Emitter (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)}
 (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))


-- Every offered instruction is parsed by the existing actual interface, including refusals.
def menu (state : JointReceptionSource.State root) : List RenewableArchiveSource.Command :=
 ((CommandWindowSource.menu state.actual.model).map fun input => .execute [input])++
 [.renew false false,.renew false true,.renew true false,.renew true true]

def execute (state : JointReceptionSource.State root) (commands : List RenewableArchiveSource.Command) : JointReceptionSource.State root :=
 commands.foldl (JointReceptionSource.advance contract) state

structure Branch (root : Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) where
 private mk ::
 commands : List RenewableArchiveSource.Command
 final : JointReceptionSource.State root

def cases : Nat → JointReceptionSource.State root → List (Branch root) :=
 Nat.rec (fun state => [⟨[],state⟩]) fun _ recur state =>
  ⟨[],state⟩::(menu state).flatMap fun command =>
   (recur (JointReceptionSource.advance contract state command)).map fun branch =>
    ⟨command::branch.commands,branch.final⟩

def Path : JointReceptionSource.State root → List RenewableArchiveSource.Command → Prop :=
 fun state commands =>
 (List.rec (motive := fun _ => JointReceptionSource.State root → Prop) (fun _ => True)
  (fun command _tail recur state => command∈menu state ∧
   recur (JointReceptionSource.advance contract state command)) commands) state

theorem every_generated_branch_replays_the_exact_original_commands
 (depth : Nat) (start : JointReceptionSource.State root) (branch : Branch root)
 (inside : branch∈cases contract depth start) :
 execute contract start branch.commands=branch.final ∧ Path contract start branch.commands ∧ branch.commands.length≤depth := by
 induction depth generalizing start branch with
 | zero =>
   cases List.mem_singleton.mp inside
   exact ⟨rfl,trivial,Nat.le_refl _⟩
 | succ depth ih =>
   rcases List.mem_cons.mp inside with same | more
   · cases same;exact ⟨rfl,trivial,Nat.zero_le _⟩
   · obtain ⟨command,registered,found⟩ := List.mem_flatMap.mp more
     obtain ⟨prior,member,rfl⟩ := List.mem_map.mp found
     obtain ⟨actual,path,bounded⟩ := ih _ prior member
     exact ⟨actual,⟨registered,path⟩,by simp only [List.length_cons];omega⟩

theorem every_bounded_original_source_path_is_generated
 (depth : Nat) (start : JointReceptionSource.State root) (commands : List RenewableArchiveSource.Command)
 (path : Path contract start commands) (bounded : commands.length≤depth) :
 ∃ branch∈cases contract depth start, branch.commands=commands ∧ branch.final=execute contract start commands := by
 induction depth generalizing start commands with
 | zero =>
   have empty : commands=[] := List.eq_nil_of_length_eq_zero (by omega)
   subst commands
   exact ⟨⟨[],start⟩,List.mem_singleton_self _,rfl,rfl⟩
 | succ depth ih =>
   cases commands with
   | nil => exact ⟨⟨[],start⟩,List.mem_cons_self,rfl,rfl⟩
   | cons command tail =>
     obtain ⟨registered,rest⟩ := path
     obtain ⟨branch,member,same,actual⟩ := ih (JointReceptionSource.advance contract start command) tail rest (by simp only [List.length_cons] at bounded;omega)
     refine ⟨⟨command::branch.commands,branch.final⟩,List.mem_cons_of_mem _ ?_,by rw [same],actual⟩
     exact List.mem_flatMap.mpr ⟨command,registered,List.mem_map.mpr ⟨branch,member,rfl⟩⟩

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law root) (origin : Cursor root) (past : List (EventHistory.Stage (code := root)))
 (scope : Scope) (value : Bool)

def debt (state : JointReceptionSource.State root) := (JointReceptionSource.pending vocabulary law origin past scope value state).card

def improves (start : JointReceptionSource.State root) (branch : Branch root) : Bool :=
 decide (debt vocabulary law origin past scope value branch.final<debt vocabulary law origin past scope value start)

inductive Result (start : JointReceptionSource.State root) (depth : Nat) where
 | complete (cleared : debt vocabulary law origin past scope value start=0)
 | repaired (branch : Branch root) (generated : branch∈cases contract depth start)
   (progress : improves vocabulary law origin past scope value start branch=true)
 | blocked (unresolved : 0<debt vocabulary law origin past scope value start)
   (exhausted : ∀ branch∈cases contract depth start,
    improves vocabulary law origin past scope value start branch=false)

def produce (start : JointReceptionSource.State root) (depth : Nat) : Result contract vocabulary law origin past scope value start depth :=
 if cleared : debt vocabulary law origin past scope value start=0 then .complete cleared
 else match found : (cases contract depth start).find? (improves vocabulary law origin past scope value start) with
 | some branch => .repaired branch (List.mem_of_find?_eq_some found) (List.find?_some found)
 | none => .blocked (Nat.pos_of_ne_zero cleared)
   (fun branch member => by simpa only [Bool.not_eq_true] using (List.find?_eq_none.mp found) branch member)

theorem a_computed_block_excludes_every_bounded_original_repair
 (start : JointReceptionSource.State root) (depth : Nat)
 (exhausted : ∀ branch∈cases contract depth start,improves vocabulary law origin past scope value start branch=false)
 (commands : List RenewableArchiveSource.Command) (path : Path contract start commands) (bounded : commands.length≤depth) :
 debt vocabulary law origin past scope value start≤debt vocabulary law origin past scope value (execute contract start commands) := by
 obtain ⟨branch,member,_,actual⟩ := every_bounded_original_source_path_is_generated contract depth start commands path bounded
 have failed := exhausted branch member
 have notLess := of_decide_eq_false failed
 rw [actual] at notLess
 omega

theorem zero_search_depth_cannot_mint_a_repair
 (start : JointReceptionSource.State root) (branch : Branch root)
 (inside : branch∈cases contract 0 start) :
 improves vocabulary law origin past scope value start branch=false := by
 cases List.mem_singleton.mp inside
 apply decide_eq_false_iff_not.mpr
 exact Nat.lt_irrefl _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceRepairSearch
