import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Meter.Arithmetic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Meter.Compiler
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {position : Nat}
local notation "Produced" => Number (Key := Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I))

def inventory (new previous : Feedback.Authority.Trace.Manifest P G O T I) : Produced (CapacityBound.Shapes.inventory new previous) :=
  let current := Feedback.Authority.Trace.Lawful.inventory new
  let original := Feedback.Authority.Trace.Lawful.inventory previous
  pair (subperm (fun _ _ => literal 4) current.due original.due)
    (fun _ => lists (fun _ _ => literal 4) current.admitted original.admitted)

def profile (new previous : Settlement.Profile P G O (Mandate.State P T) I) : Produced (CapacityBound.Shapes.profile new previous) :=
  lift (pair (lists (fun _ _ => literal 4) new.originalDebts previous.originalDebts)
    (fun _ => pair (lists (fun _ _ => literal 4) new.newbornDebts previous.newbornDebts)
      (fun _ => pair (lists (fun left right => lists (fun _ _ => literal 4) left right) new.rights previous.rights)
        (fun _ => pair (lists (fun _ _ => literal 4) new.uncoveredClaims previous.uncoveredClaims)
          (fun _ => pair (lists (fun _ _ => literal 4) new.firstServices previous.firstServices) (fun _ => literal 4))))))

variable {driver : Feedback.Input seed.source.code} (cursor : Online.Cursor seed driver)
def evaluation (new previous : Evaluation cursor.source.val.code) : Produced (CapacityBound.Shapes.evaluation cursor new previous) :=
  lift (pair (pair (literal 2) (fun _ => literal 2))
    (fun _ => pair (pair (literal 2) (fun _ => literal 2))
      (fun _ => pair (inventory new.native previous.native)
        (fun _ => pair (profile new.profile previous.profile)
          (fun _ => rows (fun _ => literal 2) (Window.axes cursor.model cursor.depth))))))

def future : (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) → Produced (CapacityBound.Shapes.future cursor new previous)
  | some current,some original => pair (literal 2) (fun _ => evaluation cursor current.evaluation original.evaluation)
  | none,_ | some _,none => literal 1

def tensor (new previous : Planning.Tensor cursor) : Produced (CapacityBound.Shapes.tensor cursor new previous) :=
  pair (evaluation cursor new.present previous.present)
    (fun _ => pair (rows (fun word => future cursor (new.future cursor word) (previous.future cursor word)) (Future.Recovery.capabilities cursor.model cursor.depth))
      (fun _ => rows (fun _ => pair (literal 2) (fun _ => literal 2)) (Future.Recovery.capabilities cursor.model cursor.depth)))

variable (pool : List (Offer (prepared := prepared) (position := position)))
def responsibility (new previous : Offer (prepared := prepared) (position := position)) : Produced (CapacityBound.Shapes.responsibility pool new previous) := by
  unfold CapacityBound.Shapes.responsibility
  apply lift
  apply pair
  · apply rows
    intro index
    apply rows
    intro table
    exact tensor (Policy.initial input prepared.saved[index].point) ((new.view index).tensor (Choice.rival pool index table))
      ((previous.view index).tensor (Choice.rival pool index table))
  intro _
  apply pair
  · exact rows (fun _ : Index prepared => pair (literal 2) (fun _ => literal 2)) (keys prepared)
  intro _
  exact pair (literal 2) (fun _ => pair (literal 2) (fun _ => literal 2))

def strict (previous new : Offer (prepared := prepared) (position := position)) : Produced (CapacityBound.Shapes.strict pool previous new) :=
  pair (responsibility pool new previous) (fun _ => lift (responsibility pool previous new))

def maximum : Produced (CapacityBound.maximum pool) := maxPairs (strict pool) pool pool

-- Only the actually returned arithmetic values feed later arithmetic and the selection reservation.
def program : Produced (CapacityBound.budget pool) :=
  .bind (length pool) fun count => .bind (maximum pool) fun largest =>
    .bind (add largest.val 3) fun padded => .bind (multiply count.val padded.val) fun product =>
      .bind (add product.val 9) fun answer => .pure ⟨answer.val,by
        rw [answer.property,product.property,padded.property,count.property,largest.property]
        exact Nat.add_comm _ _⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Meter.Compiler
