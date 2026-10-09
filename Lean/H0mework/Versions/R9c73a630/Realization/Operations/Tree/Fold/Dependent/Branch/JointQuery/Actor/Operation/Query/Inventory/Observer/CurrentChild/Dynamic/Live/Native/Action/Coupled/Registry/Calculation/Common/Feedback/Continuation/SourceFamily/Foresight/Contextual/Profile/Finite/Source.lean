import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Producer
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Payment
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource
namespace P
export Lower.SourceFamily.Foresight.Contextual.Profile.Producer (face disposition jointSource actionBinding)
end P
namespace B
export Lower.SourceFamily.Foresight.Contextual.Profile.BindingSource (complete_fibre actions original)
end B
namespace Core
export Lower.SourceFamily.Foresight.Contextual.Profile.SourceCore (source_fibre profile nativeSource nativeCursor sigma pair)
end Core
namespace F
export Lower.SourceFamily.Foresight (source_fibre frame cfg stage Word read action environment)
end F
namespace I
export Lower.SourceFamily.Foresight.Installed (nativeState)
end I
namespace C
export Lower.SourceFamily.Foresight.Contextual (actualIndex)
end C
namespace Act
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch frames)
end Act
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation (ofFrame frame_advance)
end O
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base actualOccurrence actualVisit)
end Q
namespace Owned
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw authoritativeRoot action whole)
namespace I
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (resultAt source_value source_history sourceMaterialAt)
end I
namespace Paid
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment (activePayment activeContinuation wellFounded)
end Paid
end Owned
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (seed:Lower.SourceFamily.Seed W X s n)
variable (frame:M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
abbrev index:=C.actualIndex n frame
abbrev source:=P.jointSource binding n seed (Act.epoch frame) (index n frame)
abbrev face:=P.face binding n seed (Act.epoch frame) (index n frame)
abbrev disposition:=P.disposition binding n seed (Act.epoch frame) (index n frame)
abbrev Word:=Formal ℤ (PairValue (Lower.Value W n)) X s
abbrev nativeState:=I.nativeState n seed (Act.epoch frame)
def actedWord (path:List PUnit.{u+1}) (word:Word (W:=W) (X:=X) (s:=s) n):=
 SourceGeneratedActionWords.run (B.actions (s:=s) binding n) path word
abbrev profileRead (path:List PUnit.{u+1}) (k:Nat) (word:Word (W:=W) (X:=X) (s:=s) n):=
 evaluation (R:=ℤ) (Core.pair (Core.sigma binding n)
  ((Core.nativeCursor n (Act.epoch frame) (index n frame)).advance k)) (actedWord binding n path word)
abbrev nativeWord (path:List PUnit.{u+1}) (k:Nat) (word:Word (W:=W) (X:=X) (s:=s) n):=
 AlgebraicDependent.advance (F.action binding (nativeState n seed frame) s) 0 k (actedWord binding n path word)
abbrev nativeRead (path:List PUnit.{u+1}) (k:Nat) (word:Word (W:=W) (X:=X) (s:=s) n):=
 F.read binding (nativeState n seed frame) s (0+k) (nativeWord binding n seed frame path k word)

theorem cursor_actual : Core.nativeCursor n (Act.epoch frame) (index n frame)=O.ofFrame frame:=rfl

theorem finite_source (word:Word (W:=W) (X:=X) (s:=s) n) (nonzero:source binding n seed frame word≠0):
 ∃path:List PUnit.{u+1}, (∃k,profileRead binding n frame path k word≠0) ∨
  (∃k,nativeRead binding n seed frame path k word≠0) :=by
 classical
 by_contra absent
 apply nonzero
 apply (B.complete_fibre binding n seed (Act.epoch frame) (index n frame) word 0).mpr
 intro path
 have allZero: (¬∃k,profileRead binding n frame path k word≠0) ∧
  (¬∃k,nativeRead binding n seed frame path k word≠0):=by
  constructor
  · intro witness; exact absent ⟨path,Or.inl witness⟩
  · intro witness; exact absent ⟨path,Or.inr witness⟩
 apply Prod.ext
 · apply (Core.source_fibre (Core.sigma binding n)
    (Core.nativeCursor n (Act.epoch frame) (index n frame)) _ _).mpr
   intro k
   have zero:profileRead binding n frame path k word=0:=by
    by_contra nonzero; exact allZero.1 ⟨k,nonzero⟩
   simpa only [profileRead,actedWord,map_zero] using zero
 · apply (F.source_fibre binding (nativeState n seed frame) s 0 _ _).mpr
   intro k
   have zero:nativeRead binding n seed frame path k word=0:=by
    by_contra nonzero; exact allZero.2 ⟨k,nonzero⟩
   change nativeRead binding n seed frame path k word=
    F.read binding (nativeState n seed frame) s (0+k)
     (AlgebraicDependent.advance (F.action binding (nativeState n seed frame) s) 0 k
      (SourceGeneratedActionWords.run (B.actions (s:=s) binding n) path 0))
   have zeroRun:SourceGeneratedActionWords.run (B.actions (s:=s) binding n) path 0=0:=map_zero _
   rw [zeroRun]
   exact zero.trans ((congrArg (F.read binding (nativeState n seed frame) s (0+k))
    (map_zero (AlgebraicDependent.advance (F.action binding (nativeState n seed frame) s) 0 k))).trans (map_zero _)).symm

variable (point:GeneratedRelationResidualCoordinateAt (face binding n seed frame))
theorem unsound_source : source binding n seed frame point.relation≠0:=by
 intro zero
 apply point.coordinate_ne_zero
 apply point.coordinate_eq.trans
 apply (Lower.SourceFamily.Foresight.Contextual.Forecast.Dispatch.free_evaluation seed (Act.epoch frame)
  (index n frame).2 (source binding n seed frame) point.relation).trans
 exact (canonicalResidual_eq_zero_iff _ _).mpr zero

def prefixWitness:=Classical.choose (finite_source binding n seed frame point.relation (unsound_source binding n seed frame point))
theorem prefix_witness : (∃k,profileRead binding n frame (prefixWitness binding n seed frame point) k point.relation≠0) ∨
 (∃k,nativeRead binding n seed frame (prefixWitness binding n seed frame point) k point.relation≠0):=
 Classical.choose_spec (finite_source binding n seed frame point.relation (unsound_source binding n seed frame point))

section Receipt
variable {T:Type u} {V Y:T→Type u} [∀t,AddCommGroup (V t)] {t:T}
variable (actualFrame:M.Frame (Value:=V) (Var:=Y) (sort:=t))
variable (env:Env (PairValue V) Y) (word:Formal ℤ (PairValue V) Y t)
abbrev queryRaw:Owned.Raw (Value:=PairValue V) (Var:=Y) (sort:=t):=⟨env,Coefficients.expression word⟩
abbrev queryReader {current:RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current actualFrame.registered}
 (_:SourceOperationInquiry.Context.Installation.Occurrence actualFrame (current:=current)):=queryRaw env word
abbrev queryResult:=Owned.I.resultAt (Q.base actualFrame).root.toAuthoritativeRoot (queryReader actualFrame env word) (Q.actualOccurrence actualFrame)
abbrev queryTrace:=(queryResult actualFrame env word).2.1.2
abbrev queryRoot:=Owned.authoritativeRoot (Q.base actualFrame).root.toAuthoritativeRoot
 (Q.actualVisit actualFrame).current (fun _=>queryRaw env word)
abbrev queryStage (count:Nat):=RootGeneratedDebtActivationJointSource.OwnerFree.Completion.state
 (Q.base actualFrame).root.toAuthoritativeRoot (Q.actualVisit actualFrame).current (fun _=>queryRaw env word) count
abbrev queryStageMaterial (count:Nat):=Owned.I.sourceMaterialAt (queryRoot actualFrame env word)
 ((queryRoot actualFrame env word).emitted (queryStage actualFrame env word count))
abbrev queryAction (count:Nat):=Owned.action (Q.base actualFrame).root.toAuthoritativeRoot
 (Q.actualVisit actualFrame).current (fun _=>queryRaw env word) (queryStage actualFrame env word count)
abbrev queryWhole (count:Nat):=Owned.whole (Q.base actualFrame).root.toAuthoritativeRoot
 (Q.actualVisit actualFrame).current (fun _=>queryRaw env word) (queryStage actualFrame env word count)
theorem query_value:(queryResult actualFrame env word).2.2.1=evaluation (R:=ℤ) env word:=
 (Owned.I.source_value _ _ _).trans (Coefficients.expression_eval word env)
theorem query_fee:(queryTrace actualFrame env word).length=Coefficients.cost word:=
 (Owned.I.source_history _ _ _).trans (Coefficients.expression_remaining word)
def queryMaterial:=(queryResult actualFrame env word,
 fun count:Fin (Coefficients.cost word+1)=>
  queryStageMaterial actualFrame env word count.1)
end Receipt

def profileFrame (k:Nat):=Act.frames frame k
abbrev profileEnv (k:Nat):=Core.pair (Core.sigma binding n) (O.ofFrame (profileFrame n frame k))
abbrev profileQuery (path:List PUnit.{u+1}) (k:Nat) (word:Word (W:=W) (X:=X) (s:=s) n):=
 queryMaterial (profileFrame n frame k) (profileEnv binding n frame k) (actedWord binding n path word)
theorem profile_query_value (path:List PUnit.{u+1}) (k:Nat) (word:Word (W:=W) (X:=X) (s:=s) n):
 (profileQuery binding n frame path k word).1.2.2.1=profileRead binding n frame path k word:=by
 apply (query_value _ _ _).trans
 change evaluation (R:=ℤ) (Core.pair (Core.sigma binding n) (O.ofFrame (Act.frames frame k))) _=
  evaluation (R:=ℤ) (Core.pair (Core.sigma binding n)
   ((Core.nativeCursor n (Act.epoch frame) (index n frame)).advance k)) _
 rw [cursor_actual,O.frame_advance]

abbrev nativeQuery (path:List PUnit.{u+1}) (k:Nat) (word:Word (W:=W) (X:=X) (s:=s) n):=
 queryMaterial (F.frame binding (nativeState n seed frame) (0+k))
  (F.environment binding (nativeState n seed frame) (0+k)) (nativeWord binding n seed frame path k word)
theorem native_query_value (path:List PUnit.{u+1}) (k:Nat) (word:Word (W:=W) (X:=X) (s:=s) n):
 (nativeQuery binding n seed frame path k word).1.2.2.1=nativeRead binding n seed frame path k word:=query_value _ _ _

def SelectedReceipt:=
 (Σpath:List PUnit.{u+1},Σk:Nat,
  {packet: type_of% (profileQuery binding n frame path k point.relation) //
   packet=(profileQuery binding n frame path k point.relation) ∧ packet.1.2.2.1≠0}) ⊕
 (Σpath:List PUnit.{u+1},Σk:Nat,
  {packet: type_of% (nativeQuery binding n seed frame path k point.relation) //
   packet=(nativeQuery binding n seed frame path k point.relation) ∧ packet.1.2.2.1≠0})

def selectReceipt:SelectedReceipt binding n seed frame point:=by
 classical
 let path:=prefixWitness binding n seed frame point
 by_cases profile:∃k,profileRead binding n frame path k point.relation≠0
 · let k:=Classical.choose profile
   have seen:=Classical.choose_spec profile
   exact .inl ⟨path,k,profileQuery binding n frame path k point.relation,rfl,
    fun zero=>seen ((profile_query_value binding n frame path k point.relation).symm.trans zero)⟩
 · have native:∃k,nativeRead binding n seed frame path k point.relation≠0:=
    (prefix_witness binding n seed frame point).resolve_left profile
   let k:=Classical.choose native
   have seen:=Classical.choose_spec native
   exact .inr ⟨path,k,nativeQuery binding n seed frame path k point.relation,rfl,
    fun zero=>seen ((native_query_value binding n seed frame path k point.relation).symm.trans zero)⟩

def OutputAt (phase:ResidualDispositionOutcome (face binding n seed frame)):=
 match phase with
 | .unsound _ point=>SelectedReceipt binding n seed frame point
 | .faithful _ _ _ | .kernelResidual _ _ _ | .coverageResidual _ _ _ =>PUnit

def output:OutputAt binding n seed frame (disposition binding n seed frame):=by
 generalize selected:disposition binding n seed frame=phase
 cases phase with
 | unsound _ point=>exact selectReceipt binding n seed frame point
 | faithful _ _ _ | kernelResidual _ _ _ | coverageResidual _ _ _=>exact PUnit.unit
end Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
