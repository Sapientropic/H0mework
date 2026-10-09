import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.FourFace.Consumer
import H0mework.Realization.Operations.Execution.Relations.History.Monotone
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement CofinalHistorySettlement.RootGeneratedCofinalHistoryAt CategoryTheory
namespace Lower.SourceFamily.Foresight.Contextual.Profile.History
namespace Restriction
variable {S:Type u} {V X:S→Type u} [∀t,AddCommGroup (V t)]
def insert (t:S):V t→+PairValue V t:=(AddMonoidHom.id _).prod 0
def linear {s t:S} (f:PairValue V s→+PairValue V t):V s→+V t:=
 (AddMonoidHom.fst _ _).comp (f.comp (insert s))
def bilinear {s t r:S} (f:PairValue V s→+PairValue V t→+PairValue V r):V s→+V t→+V r where
 toFun x:=(AddMonoidHom.fst _ _).comp ((f (insert s x)).comp (insert t))
 map_zero':=by ext y; simp [insert,map_zero]
 map_add' x y:=by
  ext z
  change ((f (insert s (x+y))) (insert t z)).1=_
  rw [(insert s).map_add]
  exact congrArg Prod.fst (congrArg (fun linear=>linear (insert t z)) (f.map_add _ _))
def expression {s:S} (term:Expr (PairValue V) X s):Expr V X s:=
 Expr.rec (motive:=fun sort _=>Expr V X sort)
  (fun {_} name=>.var name)
  (fun {_} value=>.const value.1)
  (fun {_} _ _ left right=>.add left right)
  (fun {_ _} f _ argument=>.linear (linear f) argument)
  (fun {_ _ _} f _ _ left right=>.bilinear (bilinear f) left right) term
theorem linear_pair {s t:S} (f:V s→+V t):linear (pairLinear f)=f:=by ext x; rfl
theorem bilinear_pair {s t r:S} (f:V s→+V t→+V r):bilinear (pairBilinear f)=f:=by ext x y; rfl
theorem original {s:S} (term:Expr V X s):expression (liftExpr term)=term:=by
 induction term with
 | var name=>rfl
 | const value=>rfl
 | add left right a b=>
  change Expr.add (expression (liftExpr left)) (expression (liftExpr right))=Expr.add left right
  exact congrArg₂ Expr.add a b
 | linear f argument previous=>
  change Expr.linear (linear (pairLinear f)) (expression (liftExpr argument))=Expr.linear f argument
  rw [linear_pair,previous]
 | bilinear f left right a b=>
  change Expr.bilinear (bilinear (pairBilinear f)) (expression (liftExpr left)) (expression (liftExpr right))=Expr.bilinear f left right
  rw [bilinear_pair,a,b]
theorem injective {s:S}:Function.Injective (liftExpr (Value:=V) (Var:=X) (s:=s)):=by
 intro left right same
 exact (original left).symm.trans ((congrArg expression same).trans (original right))
theorem support {s:S} (word:Formal ℤ V X s) (term:Expr V X s) (present:term∈word.support):
 liftExpr term∈(liftMap word).support:=by
 rw [Finsupp.mem_support_iff]
 change Finsupp.mapDomain liftExpr word (liftExpr term)≠0
 rw [Finsupp.mapDomain_apply injective]
 exact Finsupp.mem_support_iff.mp present
theorem event_support {s:S} (event:PresentedRelationEventAt (Expr V X s)) (term:Expr V X s)
 (present:term∈event.support):
 liftExpr term∈(SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.liftEvent event).support:=by
 cases event with
 | generator origin=>
  simp only [PresentedRelationEventAt.support,Finset.mem_singleton] at present
  change liftExpr term∈({liftExpr origin}:Finset (Expr (PairValue V) X _))
  exact Finset.mem_singleton.mpr (congrArg liftExpr present)
 | relation word=>exact support word term present
end Restriction
namespace Generic
variable {S:Type u} {V X:S→Type u} [∀t,AddCommGroup (V t)] {s:S}
variable {Root NextRoot:Type u}
variable (root:RootedAccountedUnfolding Root) (nextRoot:RootedAccountedUnfolding NextRoot)
variable (seed:RootedAccountedUnfolding (PresentedRelationEventAt (Expr V X s)))
variable (nextSeed:RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue V) X s)))
abbrev first:=SourceOperationPaidRelations.prefixHistory root seed
abbrev second:=SourceOperationPaidRelations.prefixHistory nextRoot nextSeed
abbrev eventMap:=SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.liftEvent (PhysicalValue:=V) (PhysicalVar:=X) (sort:=s)
variable (written:∀event∈seed.trace,eventMap event∈nextSeed.trace)
include written in
theorem event_stage (stage:Nat) (event) (present:event∈(first root seed).observedEvents stage):
 eventMap event∈(second nextRoot nextSeed).observedEvents 0:=by
 simp only [observedEvents,List.range_succ,List.range_zero,List.nil_append,List.flatMap_singleton,observation_zero]
 exact written event (SourceOperationPaidRelations.events_seed root seed stage event present)
include written in
theorem relations:(first root seed).relationClosure≤(second nextRoot nextSeed).relationClosure.comap (liftMap (R:=ℤ)):=by
 apply iSup_le
 intro stage
 apply Submodule.span_le.mpr
 intro word present
 exact (second nextRoot nextSeed).relationStage_le_closure 0
  (Submodule.subset_span (event_stage root nextRoot seed nextSeed written stage (.relation word) present))
include written in
theorem generators:(first root seed).generatorClosure≤(second nextRoot nextSeed).generatorClosure.comap (liftMap (R:=ℤ)):=by
 classical
 apply iSup_le
 intro stage
 have supports:((first root seed).generatorSupport stage:Set (Expr V X s))⊆
   (liftExpr (Value:=V) (Var:=X)) ⁻¹' ((second nextRoot nextSeed).generatorSupport 0:Set (Expr (PairValue V) X s)):=by
  intro term present
  change liftExpr term∈(second nextRoot nextSeed).generatorSupport 0
  change term∈(first root seed).generatorSupport stage at present
  rw [generatorSupport,List.mem_toFinset,List.mem_flatMap] at present ⊢
  obtain ⟨event,eventMem,termMem⟩:=present
  exact ⟨eventMap event,event_stage root nextRoot seed nextSeed written stage event eventMem,
   Finset.mem_toList.mpr (Restriction.event_support event term (Finset.mem_toList.mp termMem))⟩
 exact (Finsupp.supported_mono supports).trans
  ((Finsupp.supported_comap_lmapDomain ℤ ℤ liftExpr _).trans
   (Submodule.comap_mono ((second nextRoot nextSeed).generatorStage_le_closure 0)))
end Generic
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly (nextPacket beforeFrame beforeIndex afterFrame afterIndex BeforeTarget AfterTarget beforeSource afterSource beforeJointModule afterJointModule)
end A
namespace K
export Lower.SourceFamily.Foresight.Contextual.Profile.Kernel (beforeFace afterFace before_actual_index)
end K
namespace G
export Lower.SourceFamily.Foresight.Contextual.Profile.Generated (sourceMorphism source_scope_action)
end G
namespace F
export Lower.SourceFamily.Foresight.Contextual.Profile.Affine (BeforeScope AfterScope actor beforeq afterq)
end F
namespace R
export Lower.SourceFamily.Foresight.Contextual.Reader (pairWritten complete_source_inventory)
end R
namespace Wr
export Lower.SourceFamily.Foresight.Contextual.Written (native_written_in_stock stock_in_joint jointHistory jointStock)
end Wr
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint (history)
end J
namespace P
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual (pairInventory)
end P
namespace D
export Lower.SourceFamily.Foresight.Contextual.Forecast.Dispatch (free_evaluation)
end D
namespace C
export CofinalRelationGeneratedComplex (natComplex natComplex_d_zero_one differential relationInclusion differential_sq)
end C
namespace T
export SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (liftEvent)
end T
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (packet:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
local instance beforeModule:Module ℤ (A.BeforeTarget binding n packet):=A.beforeJointModule binding n packet
local instance afterModule:Module ℤ (A.AfterTarget binding n packet):=A.afterJointModule binding n packet
abbrev oldInventory:=P.pairInventory packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet).2
abbrev oldHistory:=J.history packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet).2
abbrev newHistory:=Wr.jointHistory binding n packet
variable (native:packet.1.depth=0)
include native in
theorem actual_event (event) (present:event∈(oldInventory n packet).trace):
 T.liftEvent event∈(Wr.jointStock binding n packet).trace:=by
 have paid:=R.complete_source_inventory binding n packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet) event present
 have inventories:=congrArg (fun index=>R.pairWritten binding n packet.2 (A.beforeFrame n packet) index)
  (K.before_actual_index n packet native)
 have transported:event∈(R.pairWritten binding n packet.2 (A.beforeFrame n packet)
  (Lower.SourceFamily.Foresight.Contextual.actualIndex n packet.1)).trace:=
  Eq.mp (congrArg (fun inventory=>event∈inventory.trace) inventories.symm) paid
 exact Wr.stock_in_joint binding n packet _ (Wr.native_written_in_stock binding n packet event transported)
include native in
theorem actual_relations:(oldHistory n packet).relationClosure≤(newHistory binding n packet).relationClosure.comap (liftMap (R:=ℤ)):=
 Generic.relations (RootedAccountedUnfolding.zero (A.beforeIndex n packet).2)
  (RootedAccountedUnfolding.zero (Lower.SourceFamily.Foresight.Contextual.Written.Q.actualOccurrence (Lower.SourceFamily.Foresight.Contextual.Written.receiver binding n packet)))
  (oldInventory n packet) (Wr.jointStock binding n packet) (actual_event binding n packet native)
include native in
theorem actual_generators:(oldHistory n packet).generatorClosure≤(newHistory binding n packet).generatorClosure.comap (liftMap (R:=ℤ)):=
 Generic.generators (RootedAccountedUnfolding.zero (A.beforeIndex n packet).2)
  (RootedAccountedUnfolding.zero (Lower.SourceFamily.Foresight.Contextual.Written.Q.actualOccurrence (Lower.SourceFamily.Foresight.Contextual.Written.receiver binding n packet)))
  (oldInventory n packet) (Wr.jointStock binding n packet) (actual_event binding n packet native)
include native in
def relationLift:(oldHistory n packet).relationClosure→ₗ[ℤ](newHistory binding n packet).relationClosure:=
 (liftMap (R:=ℤ)).comp (oldHistory n packet).relationClosure.subtype |>.codRestrict
 (newHistory binding n packet).relationClosure (fun relation=>actual_relations binding n packet native relation.property)
include native in
def generatorLift:(oldHistory n packet).generatorClosure→ₗ[ℤ](newHistory binding n packet).generatorClosure:=
 (liftMap (R:=ℤ)).comp (oldHistory n packet).generatorClosure.subtype |>.codRestrict
 (newHistory binding n packet).generatorClosure (fun generator=>actual_generators binding n packet native generator.property)
include native in
theorem inclusion_naturality:
 (generatorLift binding n packet native).comp (C.relationInclusion (oldHistory n packet))=
 (C.relationInclusion (newHistory binding n packet)).comp (relationLift binding n packet native):=by
 apply LinearMap.ext
 intro relation
 apply Subtype.ext
 rfl
include native in
def degreeMap:(i:Nat)→(C.natComplex (oldHistory n packet)).X i⟶(C.natComplex (newHistory binding n packet)).X i
 | 0=>ModuleCat.ofHom (relationLift binding n packet native)
 | 1=>ModuleCat.ofHom (generatorLift binding n packet native)
 | _+2=>0
include native in
def cochainAction:C.natComplex (oldHistory n packet)⟶C.natComplex (newHistory binding n packet):=
 CochainComplex.ofHom (degreeMap binding n packet native) (by
  intro i
  cases i with
  | zero=>
   simp only [degreeMap]
   apply ModuleCat.hom_ext
   exact (inclusion_naturality binding n packet native).symm
  | succ i=>
   cases i with
   | zero=>
    simp only [C.natComplex,CochainComplex.of_d,C.differential,degreeMap]
    rfl
   | succ i=>
    simp only [C.natComplex,CochainComplex.of_d,C.differential,degreeMap]
    rfl)

def oldDifferential:=(K.beforeFace binding n packet).closureEvaluation.comp (C.relationInclusion (oldHistory n packet))
def newDifferential:=(K.afterFace binding n packet).closureEvaluation.comp (C.relationInclusion (newHistory binding n packet))
include native in
def observedMorphism:Morphism (oldDifferential binding n packet) (newDifferential binding n packet) where
 sourceMap:=relationLift binding n packet native
 targetMap:=F.actor binding n packet native
 commutes:=by
  apply LinearMap.ext
  intro relation
  change F.actor binding n packet native ((K.beforeFace binding n packet).freeEvaluation relation.val)=
   (K.afterFace binding n packet).freeEvaluation (liftMap relation.val)
  exact (congrArg (F.actor binding n packet native)
   (D.free_evaluation packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet).2 (A.beforeSource binding n packet) relation.val)).trans
   ((G.source_scope_action binding n packet native relation.val).trans
    (D.free_evaluation (A.nextPacket binding n packet).2 (A.afterFrame binding n packet) (A.afterIndex binding n packet).2
     (A.afterSource binding n packet) (liftMap relation.val)).symm)
include native in
theorem observed_residual_action (relation:(oldHistory n packet).relationClosure):
 inducedResidualMap (observedMorphism binding n packet native)
  (canonicalResidual (oldDifferential binding n packet) relation)=
 canonicalResidual (newDifferential binding n packet) (relationLift binding n packet native relation):=
 LinearMap.congr_fun (inducedResidualMap_comp_canonical (observedMorphism binding n packet native)) relation
include native in
theorem observed_effect (relation:(oldHistory n packet).relationClosure):
 (residualEquivRange (newDifferential binding n packet)
  (inducedResidualMap (observedMorphism binding n packet native)
   (canonicalResidual (oldDifferential binding n packet) relation))).val=
 F.actor binding n packet native (oldDifferential binding n packet relation):=by
 have moved:=congrArg
  (fun value:ResidualCarrier (newDifferential binding n packet)=>
   (residualEquivRange (newDifferential binding n packet) value).val)
  (observed_residual_action binding n packet native relation)
 have realized:
  (residualEquivRange (newDifferential binding n packet)
   (canonicalResidual (newDifferential binding n packet) (relationLift binding n packet native relation))).val=
  newDifferential binding n packet (relationLift binding n packet native relation) :=
  congrArg (fun value:LinearMap.range (newDifferential binding n packet)=>value.val)
   (residualToRange_canonicalResidual (newDifferential binding n packet) (relationLift binding n packet native relation))
 exact moved.trans (realized.trans
  (LinearMap.congr_fun (observedMorphism binding n packet native).commutes relation).symm)


end Lower.SourceFamily.Foresight.Contextual.Profile.History
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
