import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.CapacityBound.Core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.CapacityBound.Shapes
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {position : Nat}

theorem nativeEqual_bound (left right : NativeBenefit.NativeKey (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) :
    (Query.Source.nativeEqual left right).cost ≤ 4 := equal_bound _ _ left right

def inventory (new previous : Feedback.Authority.Trace.Manifest P G O T I) :=
  let current := Feedback.Authority.Trace.Lawful.inventory new
  let original := Feedback.Authority.Trace.Lawful.inventory previous
  pair (subperm (fun _ _ => 4) current.due original.due) (lists (fun _ _ => 4) current.admitted original.admitted)

theorem inventory_bound (new previous : Feedback.Authority.Trace.Manifest P G O T I) :
    (Query.Source.inventory new previous).cost ≤ inventory new previous := by
  dsimp only [Query.Source.inventory,inventory]
  apply conjunction_bound
  · exact subperm_bound _ _ nativeEqual_bound _ _
  exact lists_bound _ _ nativeEqual_bound _ _

def profile (new previous : Settlement.Profile P G O (Mandate.State P T) I) :=
  lift (pair (lists (fun _ _ => 4) new.originalDebts previous.originalDebts)
    (pair (lists (fun _ _ => 4) new.newbornDebts previous.newbornDebts)
      (pair (lists (lists (fun _ _ => 4)) new.rights previous.rights)
        (pair (lists (fun _ _ => 4) new.uncoveredClaims previous.uncoveredClaims)
          (pair (lists (fun _ _ => 4) new.firstServices previous.firstServices) 4)))))

theorem profile_bound (new previous : Settlement.Profile P G O (Mandate.State P T) I) :
    (Query.Source.profile new previous).cost ≤ profile new previous := by
  dsimp only [Query.Source.profile,profile]
  apply transport_bound
  apply conjunction_bound
  · exact lists_bound _ _ (fun left right => equal_bound _ _ left right) _ _
  apply conjunction_bound
  · exact lists_bound _ _ (fun left right => equal_bound _ _ left right) _ _
  apply conjunction_bound
  · exact lists_bound _ _ (fun left right => lists_bound _ _ (fun a b => equal_bound _ _ a b) left right) _ _
  apply conjunction_bound
  · exact lists_bound _ _ (fun left right => equal_bound _ _ left right) _ _
  apply conjunction_bound
  · exact lists_bound _ _ (fun left right => equal_bound _ _ left right) _ _
  exact equal_bound _ _ _ _

variable {driver : Feedback.Input seed.source.code} (cursor : Online.Cursor seed driver)
def evaluation (new previous : Evaluation cursor.source.val.code) :=
  lift (pair (pair 2 2) (pair (pair 2 2) (pair (inventory new.native previous.native)
    (pair (profile new.profile previous.profile) (rows (fun _ => 2) (Window.axes cursor.model cursor.depth))))))

theorem evaluation_bound (new previous : Evaluation cursor.source.val.code) :
    (Query.Source.evaluation cursor new previous).cost ≤ evaluation cursor new previous := by
  dsimp only [Query.Source.evaluation,evaluation]
  apply transport_bound
  apply conjunction_bound
  · exact implication_bound _ _ (Nat.le_refl 2) (Nat.le_refl 2)
  apply conjunction_bound
  · exact implication_bound _ _ (Nat.le_refl 2) (Nat.le_refl 2)
  apply conjunction_bound
  · exact inventory_bound _ _
  apply conjunction_bound
  · exact profile_bound _ _
  exact rows_bound _ _ _ (fun _ => Nat.le_refl 2) _

def future : (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) → Nat
  | some current,some original => pair 2 (evaluation cursor current.evaluation original.evaluation)
  | _,_ => 1

theorem future_bound (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) :
    (Query.Source.future cursor new previous).cost ≤ future cursor new previous := by
  cases new with
  | none => cases previous <;> exact Nat.le_refl 1
  | some current => cases previous with
    | none => exact Nat.le_refl 1
    | some original =>
        dsimp only [Query.Source.future,future]
        apply conjunction_bound
        · exact Nat.le_refl 2
        exact evaluation_bound cursor _ _

def tensor (new previous : Planning.Tensor cursor) :=
  pair (evaluation cursor new.present previous.present)
    (pair (rows (fun word => future cursor (new.future cursor word) (previous.future cursor word)) (Future.Recovery.capabilities cursor.model cursor.depth))
      (rows (fun _ => pair 2 2) (Future.Recovery.capabilities cursor.model cursor.depth)))

theorem tensor_bound (new previous : Planning.Tensor cursor) :
    (Query.Source.tensor cursor new previous).cost ≤ tensor cursor new previous :=
  conjunction_bound _ _ (evaluation_bound cursor _ _) (conjunction_bound _ _
    (rows_bound _ _ _ (fun word => future_bound cursor (new.future cursor word) (previous.future cursor word)) _)
    (rows_bound _ _ _ (fun _ => implication_bound _ _ (Nat.le_refl 2) (Nat.le_refl 2)) _))

variable (pool : List (Offer (prepared := prepared) (position := position)))
def responsibility (new previous : Offer (prepared := prepared) (position := position)) :=
  let tensors := rows (fun index => rows (fun table =>
    tensor (Policy.initial input prepared.saved[index].point) ((new.view index).tensor (Choice.rival pool index table))
      ((previous.view index).tensor (Choice.rival pool index table))) (Choice.tables pool index)) (keys prepared)
  let costs := rows (fun _ : Index prepared => pair 2 2) (keys prepared)
  lift (pair tensors (pair costs (pair 2 (pair 2 2))))

theorem responsibility_bound (new previous : Offer (prepared := prepared) (position := position)) :
    (Query.Source.responsibility pool new previous).cost ≤ responsibility pool new previous := by
  dsimp only [Query.Source.responsibility,responsibility]
  apply transport_bound
  apply conjunction_bound
  · exact rows_bound _ _ _ (fun index => rows_bound _ _ _ (fun table => tensor_bound _ _ _) _) _
  apply conjunction_bound
  · exact rows_bound _ _ _ (fun _ => conjunction_bound _ _ (Nat.le_refl 2) (Nat.le_refl 2)) _
  exact conjunction_bound _ _ (Nat.le_refl 2) (conjunction_bound _ _ (Nat.le_refl 2) (Nat.le_refl 2))

def strict (previous new : Offer (prepared := prepared) (position := position)) :=
  pair (responsibility pool new previous) (lift (responsibility pool previous new))

theorem strict_bound (previous new : Offer (prepared := prepared) (position := position)) :
    (Query.Source.strict pool previous new).cost ≤ strict pool previous new :=
  conjunction_bound _ _ (responsibility_bound pool new previous) (negative_bound _ (responsibility_bound pool previous new))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.CapacityBound.Shapes
