import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FreshSigningConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveSigningSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewableCodeLineage

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 [Fintype Party] [Fintype Instrument]
 {root : Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)}

abbrev current (state : JointReceptionSource.State root) := (EventStep.seed state.actual.point).current

def total (state : JointReceptionSource.State root) (good : Good) : ℚ :=
 ∑ party : Party, (current state).stock party good

def sameClaims (before after : JointReceptionSource.State root) : Prop :=
 ∀ instrument debtor creditor, (current after).claims instrument debtor creditor=(current before).claims instrument debtor creditor
instance (before after : JointReceptionSource.State root) : Decidable (sameClaims before after) := by
 unfold sameClaims;infer_instance

def productiveRow (row : RenewableCodeLineage.Row root) : Bool :=
 (StageTrace.items row.actual).any fun item => match item.request.operation with
 | .produce _ => decide (row.code.law.Valid item.before item.request)
 | _ => false

def freshProduction (before after : JointReceptionSource.State root) : Bool :=
 (after.rows.drop before.rows.length).any productiveRow

variable (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (laws : (model : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) → StageReception.Law model.source.code)
 (request : FreshSigningSource.Request (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
 (good : Good) (quota : ℚ) (threshold : Nat)

abbrev prepared (branch : SourceRepairSearch.Branch root) := FreshSigningSource.prepared contract branch.final request
abbrev endpoint (branch : SourceRepairSearch.Branch root) := FreshSigningSource.cycle contract base laws branch.final request

def decisions (branch : SourceRepairSearch.Branch root) :
 List (Fin (prepared contract request branch).actual.model.source.code.sites × Bool) :=
 (List.finRange (prepared contract request branch).actual.model.source.code.sites).filterMap fun recipient =>
  match FreshSigningConsumer.decision contract base laws (prepared contract request branch) request recipient threshold with
  | .blocked _ => none
  | .decided answer => some (recipient,answer)

def accepts (before : JointReceptionSource.State root) (branch : SourceRepairSearch.Branch root) : Bool :=
 decide (total before good+quota≤total (endpoint contract base laws request branch) good ∧
  sameClaims before (endpoint contract base laws request branch)) &&
 freshProduction before (endpoint contract base laws request branch) &&
 !(decisions contract base laws request threshold branch).isEmpty

inductive Result (before : JointReceptionSource.State root) (depth : Nat) where
 | invalidDemand (nonpositive : ¬0<quota)
 | produced (branch : SourceRepairSearch.Branch root) (positive : 0<quota)
   (generated : branch∈SourceRepairSearch.cases contract depth before)
   (checked : accepts contract base laws request good quota threshold before branch=true)
 | blocked (positive : 0<quota)
   (exhausted : ∀ branch∈SourceRepairSearch.cases contract depth before,
    accepts contract base laws request good quota threshold before branch=false)

def produce (before : JointReceptionSource.State root) (depth : Nat) :
 Result contract base laws request good quota threshold before depth :=
 if positive : 0<quota then
  match found : (SourceRepairSearch.cases contract depth before).find?
   (accepts contract base laws request good quota threshold before) with
  | some branch => .produced branch positive (List.mem_of_find?_eq_some found) (List.find?_some found)
  | none => .blocked positive (fun branch member => by
    simpa only [Bool.not_eq_true] using (List.find?_eq_none.mp found) branch member)
 else .invalidDemand positive

theorem acceptance_checks_the_actual_full_cycle
 (before : JointReceptionSource.State root) (branch : SourceRepairSearch.Branch root)
 (checked : accepts contract base laws request good quota threshold before branch=true) :
 total before good+quota≤total (endpoint contract base laws request branch) good ∧
 sameClaims before (endpoint contract base laws request branch) ∧
 freshProduction before (endpoint contract base laws request branch)=true ∧
 (decisions contract base laws request threshold branch).isEmpty=false := by
 obtain ⟨⟨resources,production⟩,decision⟩ := Bool.and_eq_true_iff.mp checked |>.imp_left Bool.and_eq_true_iff.mp
 obtain ⟨stock,claims⟩ := of_decide_eq_true resources
 exact ⟨stock,claims,production,by simpa only [Bool.not_eq_true'] using decision⟩

theorem a_real_accepted_source_branch_is_found
 (before : JointReceptionSource.State root) (depth : Nat) (positive : 0<quota)
 (candidate : SourceRepairSearch.Branch root) (member : candidate∈SourceRepairSearch.cases contract depth before)
 (accepted : accepts contract base laws request good quota threshold before candidate=true) :
 ∃ branch generated checked,
 produce contract base laws request good quota threshold before depth=.produced branch positive generated checked := by
 unfold produce
 rw [dif_pos positive]
 split
 · rename_i branch found
   exact ⟨branch,List.mem_of_find?_eq_some found,List.find?_some found,rfl⟩
 · rename_i found
   have missing := (List.find?_eq_none.mp found) candidate member
   rw [accepted] at missing
   contradiction

def next (before : JointReceptionSource.State root) (depth : Nat) : JointReceptionSource.State root :=
 match produce contract base laws request good quota threshold before depth with
 | .produced branch _ _ _ => endpoint contract base laws request branch
 | .blocked _ _ | .invalidDemand _ => before

def increment (before : JointReceptionSource.State root) (depth : Nat) : Nat :=
 match produce contract base laws request good quota threshold before depth with
 | .produced _ _ _ _ => 1
 | .blocked _ _ | .invalidDemand _ => 0

def run (before : JointReceptionSource.State root) (depth : Nat) : Nat → JointReceptionSource.State root :=
 Nat.rec before fun _ current => next contract base laws request good quota threshold current depth

def producedCount (before : JointReceptionSource.State root) (depth : Nat) : Nat → Nat :=
 Nat.rec 0 fun ordinal previous => previous+
  increment contract base laws request good quota threshold
   (run contract base laws request good quota threshold before depth ordinal) depth

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveSigningSource
