import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Programme
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Installation

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (seed:Lower.SourceFamily.Seed W X s n)
variable (frame:M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
variable (origin:Lower.SourceFamily.Foresight.Installed.OccurrenceIndex n frame)
abbrev source:=P.jointSource binding n seed frame origin
abbrev face:=P.face binding n seed frame origin
abbrev disposition:=P.disposition binding n seed frame origin
abbrev cursor:=Core.nativeCursor n frame origin
abbrev state:=I.nativeState n seed frame
abbrev profileRead (path:List PUnit.{u+1}) (k:Nat) (word:Word (W:=W) (X:=X) (s:=s) n):=
 evaluation (R:=ℤ) (Core.pair (Core.sigma binding n) ((cursor n frame origin).advance k))
  (actedWord binding n path word)
abbrev nativeWord (path:List PUnit.{u+1}) (k:Nat) (word:Word (W:=W) (X:=X) (s:=s) n):=
 AlgebraicDependent.advance (F.action binding (state n seed frame) s) 0 k (actedWord binding n path word)
abbrev nativeRead (path:List PUnit.{u+1}) (k:Nat) (word:Word (W:=W) (X:=X) (s:=s) n):=
 F.read binding (state n seed frame) s (0+k) (nativeWord binding n seed frame path k word)

theorem finite_source (word:Word (W:=W) (X:=X) (s:=s) n)
 (nonzero:source binding n seed frame origin word≠0):
 ∃path:List PUnit.{u+1}, (∃k,profileRead binding n frame origin path k word≠0) ∨
  (∃k,nativeRead binding n seed frame path k word≠0):=by
 classical
 by_contra absent
 apply nonzero
 apply (B.complete_fibre binding n seed frame origin word 0).mpr
 intro path
 have allZero:(¬∃k,profileRead binding n frame origin path k word≠0) ∧
  (¬∃k,nativeRead binding n seed frame path k word≠0):=by
  constructor
  · intro witness;exact absent ⟨path,Or.inl witness⟩
  · intro witness;exact absent ⟨path,Or.inr witness⟩
 apply Prod.ext
 · apply (Core.source_fibre (Core.sigma binding n) (cursor n frame origin) _ _).mpr
   intro k
   have zero:profileRead binding n frame origin path k word=0:=by
    by_contra nonzero;exact allZero.1 ⟨k,nonzero⟩
   simpa only [profileRead,actedWord,map_zero] using zero
 · apply (F.source_fibre binding (state n seed frame) s 0 _ _).mpr
   intro k
   have zero:nativeRead binding n seed frame path k word=0:=by
    by_contra nonzero;exact allZero.2 ⟨k,nonzero⟩
   change nativeRead binding n seed frame path k word=
    F.read binding (state n seed frame) s (0+k)
     (AlgebraicDependent.advance (F.action binding (state n seed frame) s) 0 k
      (SourceGeneratedActionWords.run (B.actions (s:=s) binding n) path 0))
   have zeroRun:SourceGeneratedActionWords.run (B.actions (s:=s) binding n) path 0=0:=map_zero _
   rw [zeroRun]
   exact zero.trans ((congrArg (F.read binding (state n seed frame) s (0+k))
    (map_zero (AlgebraicDependent.advance (F.action binding (state n seed frame) s) 0 k))).trans (map_zero _)).symm

variable (point:GeneratedRelationResidualCoordinateAt (face binding n seed frame origin))
theorem unsound_source:source binding n seed frame origin point.relation≠0:=by
 intro zero
 apply point.coordinate_ne_zero
 apply point.coordinate_eq.trans
 apply (Lower.SourceFamily.Foresight.Contextual.Forecast.Dispatch.free_evaluation seed frame origin.2
  (source binding n seed frame origin) point.relation).trans
 exact (canonicalResidual_eq_zero_iff _ _).mpr zero

def prefixWitness:=Classical.choose (finite_source binding n seed frame origin point.relation
 (unsound_source binding n seed frame origin point))
theorem prefix_witness:
 (∃k,profileRead binding n frame origin (prefixWitness binding n seed frame origin point) k point.relation≠0) ∨
 (∃k,nativeRead binding n seed frame (prefixWitness binding n seed frame origin point) k point.relation≠0):=
 Classical.choose_spec (finite_source binding n seed frame origin point.relation
  (unsound_source binding n seed frame origin point))

def profileRaw (path:List PUnit.{u+1}) (k:Nat):=
 queryRaw (Core.pair (Core.sigma binding n) ((cursor n frame origin).advance k))
  (actedWord binding n path point.relation)
def profileResult (path:List PUnit.{u+1}) (k:Nat):=
 Owned.I.resultAt (InstalledQuery.Q.base frame).root.toAuthoritativeRoot
  (fun {_current} _=>profileRaw binding n seed frame origin point path k) origin.2

def profileCalculation (path:List PUnit.{u+1}) (k:Nat):=
 (profileResult binding n seed frame origin point path k,
  ((cursor n frame origin).advance k).material,
  ((cursor n frame origin).advance k).action,
  fun count:Fin (Coefficients.cost (actedWord binding n path point.relation)+1)=>
   Owned.I.sourceMaterialAt
    (Owned.authoritativeRoot (InstalledQuery.Q.base frame).root.toAuthoritativeRoot origin.1
     (fun _=>profileRaw binding n seed frame origin point path k))
    ((Owned.authoritativeRoot (InstalledQuery.Q.base frame).root.toAuthoritativeRoot origin.1
     (fun _=>profileRaw binding n seed frame origin point path k)).emitted
     (RootGeneratedDebtActivationJointSource.OwnerFree.Completion.state
      (InstalledQuery.Q.base frame).root.toAuthoritativeRoot origin.1
      (fun _=>profileRaw binding n seed frame origin point path k) count.1)))

theorem profile_value (path:List PUnit.{u+1}) (k:Nat):
 (profileResult binding n seed frame origin point path k).2.2.1=
 profileRead binding n frame origin path k point.relation:=
 (Owned.I.source_value _ _ _).trans (Coefficients.expression_eval _ _)

theorem profile_fee (path:List PUnit.{u+1}) (k:Nat):
 (profileResult binding n seed frame origin point path k).2.1.2.length=
 Coefficients.cost (actedWord binding n path point.relation):=
 (Owned.I.source_history _ _ _).trans (Coefficients.expression_remaining _)

def nativeProgramme (path:List PUnit.{u+1}) (k:Nat):=
 InstalledQuery.programme (Future.Replay.Binding.at binding (F.stage binding (state n seed frame) (0+k)))
  (nativeWord binding n seed frame path k point.relation) (F.cfg binding (state n seed frame) (0+k))
def nativeCalculation (path:List PUnit.{u+1}) (k:Nat):=
 ((InstalledQuery.Q.resultFace (F.frame binding (state n seed frame) (0+k))
   (nativeProgramme binding n seed frame origin point path k)).rootRead,
  (InstalledQuery.face (Future.Replay.Binding.at binding (F.stage binding (state n seed frame) (0+k)))
   (nativeWord binding n seed frame path k point.relation) (F.cfg binding (state n seed frame) (0+k))
   (F.frame binding (state n seed frame) (0+k))).rootRead)

theorem native_environment (k:Nat):
 InstalledQuery.environment (Future.Replay.Binding.at binding (F.stage binding (state n seed frame) (0+k)))
  (Act.epoch (F.frame binding (state n seed frame) (0+k)))
  (InstalledQuery.Q.actualOccurrence (F.frame binding (state n seed frame) (0+k)))=
 F.environment binding (state n seed frame) (0+k):=by
 apply (InstalledQuery.environment_source _ _ _).trans
 exact (congrArg (fun raw=>raw.environment)
  (Lower.SourceFamily.Replay.factory_raw binding (F.stage binding (state n seed frame) (0+k))
   (Lower.SourceFamily.Foresight.Tail.tail binding (state n seed frame) (0+k)).2.2
   (F.frame binding (state n seed frame) (0+k)))).symm

theorem native_value (path:List PUnit.{u+1}) (k:Nat):
 (nativeCalculation binding n seed frame origin point path k).1.2.2.1=
 nativeRead binding n seed frame path k point.relation:=by
 apply (InstalledQuery.actual_value _ _ _ _).trans
 exact congrArg (fun env=>evaluation (R:=ℤ) env (nativeWord binding n seed frame path k point.relation))
  (native_environment binding n seed frame k)

def Selected:=
 (Σpath:List PUnit.{u+1},Σk:Nat,
  {packet:type_of% (profileCalculation binding n seed frame origin point path k)//
   packet=profileCalculation binding n seed frame origin point path k ∧ packet.1.2.2.1≠0}) ⊕
 (Σpath:List PUnit.{u+1},Σk:Nat,
  {packet:type_of% (nativeCalculation binding n seed frame origin point path k)//
   packet=nativeCalculation binding n seed frame origin point path k ∧ packet.1.2.2.1≠0})

def selected:Selected binding n seed frame origin point:=by
 classical
 let path:=prefixWitness binding n seed frame origin point
 by_cases profile:∃k,profileRead binding n frame origin path k point.relation≠0
 · let k:=Classical.choose profile
   have seen:=Classical.choose_spec profile
   exact .inl ⟨path,k,profileCalculation binding n seed frame origin point path k,rfl,
    fun zero=>seen ((profile_value binding n seed frame origin point path k).symm.trans zero)⟩
 · have native:∃k,nativeRead binding n seed frame path k point.relation≠0:=
    (prefix_witness binding n seed frame origin point).resolve_left profile
   let k:=Classical.choose native
   have seen:=Classical.choose_spec native
   exact .inr ⟨path,k,nativeCalculation binding n seed frame origin point path k,rfl,
    fun zero=>seen ((native_value binding n seed frame origin point path k).symm.trans zero)⟩

omit point in
def OutputAt (outcome:ResidualDispositionOutcome (face binding n seed frame origin)):=
 match outcome with
 | .unsound _ coordinate=>Selected binding n seed frame origin coordinate
 | .faithful _ _ _ | .kernelResidual _ _ _ | .coverageResidual _ _ _=>PUnit.{u+1}
omit point in
def output:OutputAt binding n seed frame origin (disposition binding n seed frame origin):=by
 generalize actual:disposition binding n seed frame origin=outcome
 cases outcome with
 | unsound _ coordinate=>exact selected binding n seed frame origin coordinate
 | faithful _ _ _ | kernelResidual _ _ _ | coverageResidual _ _ _=>exact PUnit.unit
end Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
