import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.ExactCurrent

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace NS
export NativeSigma (NativePacket NativeFactory collapseNative collapsedOld collapsedIncrement selected decoded paid increment)
end NS
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionReader afterEnvironment)
end R
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input)
end N
namespace CA
export ActualCofinalSourceAction (nativePacket)
end CA
namespace Coll
export OriginalKFiniteWard (collapse_sub)
end Coll
namespace FR
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullResidualCalculation (completeInput)
end FR
namespace Init
export OriginalKCombFirstFullSourceDynamics (initial_next_active)
export OriginalKCombFirstFullSourceDynamics.Q (split actual_born_pair)
end Init

private theorem receipt_environment {V X : Unit→Type} [∀ target,AddCommGroup (V target)]
 (frame : A.M.Frame (Value:=V) (Var:=X) (sort:=()))
 (cfg : A.Programme (PhysicalValue:=V) (PhysicalVar:=X) (sort:=())) :
 (NativeSigma.AN.paid (S.Complete.atReceipt cfg frame 0)).environment=frame.registered.input.environment := by
 rw [NativeSigma.AN.paid_environment]
 apply NativeSigma.Prefix.receipt_read cfg frame (fun stage=>(S.frames frame cfg stage).registered.input.environment)
 intro stage paid actual
 have next : S.frames frame cfg (stage+1)=(S.frames frame cfg stage).mathNext := by
  change S.next _ _ = _
  unfold S.next
  rw [actual]
 exact (congrArg (fun current : A.M.Frame (Value:=V) (Var:=X) (sort:=())=>current.registered.input.environment) next).trans rfl

local instance deltaGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade

private theorem native_old_environment (factory : NS.NativeFactory) (packet : NS.NativePacket)
 (code : Expr (PairValue (PairValue C.Value)) C.Var ())
 (generated : AI.HasActualInput code packet.1 packet.2.2.1 packet.2.2.2.down) :
 NS.collapsedOld factory packet=fun target name=>CF.collapseValue packet.1
  ((S.next packet.2.1.1 packet.2.2.1).activeEnvironment target name,0) := by
 rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at sameVar
  cases sameVar
  let cfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()) :=
   ⟨C.Var,datum,inventory,pairInventory⟩
  let packet : NS.NativePacket := ⟨grade,data,cfg,⟨rfl⟩⟩
  let native:=CA.nativePacket factory packet
  have afterRaw := (AS.stock_action_reader (S.next data.1 cfg) cfg (S.actualOccurrence (S.next data.1 cfg))).symm.trans
   (generated (S.next data.1 cfg) (S.actualOccurrence (S.next data.1 cfg)))
  have afterEnvironment := (congrArg (fun raw=>raw.environment) afterRaw).trans
   (congrArg (fun environment=>pairEnvironment environment (0 : Env (L.Value (PairValue C.Value) grade) C.Var))
    (OriginalKDirectRCofinalMaterial.AI.actual_environment grade (S.next data.1 cfg)))
  have input : (N.input (R.actualMaterial data.1 cfg)).environment=
   pairEnvironment (S.next data.1 cfg).activeEnvironment 0 :=
   (add_sub_cancel (R.actualMaterial data.1 cfg).environment (R.afterEnvironment data.1 cfg)).trans afterEnvironment
  have receiver : native.2.1.1.registered.input.environment=(N.input (R.actualMaterial data.1 cfg)).environment := rfl
  have old:=receipt_environment native.2.1.1 (AS.stockCfg native.2.2.1)
  change (fun target name=>CF.collapseValue grade
   ((NativeSigma.AN.paid (S.Complete.atReceipt (AS.stockCfg native.2.2.1) native.2.1.1 0)).environment target name))=_
  exact congrArg (fun environment=>fun target name=>CF.collapseValue grade (environment target name))
   (old.trans (receiver.trans input))

private theorem cast_sub (grade nextGrade : Nat) (same : nextGrade=grade+1)
 (left right : L.Value (PairValue C.Value) nextGrade ()) :
 Eq.mp (congrArg (fun next=>L.Value (PairValue C.Value) next ()) same) (left-right)=
 Eq.mp (congrArg (fun next=>L.Value (PairValue C.Value) next ()) same) left-
 Eq.mp (congrArg (fun next=>L.Value (PairValue C.Value) next ()) same) right := by
 subst nextGrade
 rfl

private theorem collapse_native_sub (factory : NS.NativeFactory) (packet : NS.NativePacket)
 (left right : L.Value (PairValue C.Value) (AS.nativeAfterAdmission factory packet).1 ()) :
 NS.collapseNative factory packet (left-right)=NS.collapseNative factory packet left-NS.collapseNative factory packet right :=
 (congrArg (CF.collapseValue packet.1)
  (cast_sub packet.1 _ (AS.nativeAfterAdmission_grade factory packet) left right)).trans
 (Coll.collapse_sub packet.1 _ _)

private theorem collapse_cast_shift (grade nextGrade : Nat) (same : nextGrade=grade+1)
 (value : L.Value (PairValue C.Value) nextGrade ()) :
 CF.collapseValue grade (Eq.mp (congrArg (fun next=>L.Value (PairValue C.Value) next ()) same) value)=
 CF.collapseValue nextGrade (value,0) := by
 subst nextGrade
 change CF.collapseValue grade value=CF.collapseValue grade (value+0)
 exact congrArg (CF.collapseValue grade) (add_zero value).symm

private theorem collapse_native_shift (factory : NS.NativeFactory) (packet : NS.NativePacket)
 (value : L.Value (PairValue C.Value) (AS.nativeAfterAdmission factory packet).1 ()) :
 NS.collapseNative factory packet value=CF.collapseValue (AS.nativeAfterAdmission factory packet).1 (value,0) :=
 collapse_cast_shift packet.1 _ (AS.nativeAfterAdmission_grade factory packet) value

private theorem born_packet_read (native : NS.NativePacket) :
 FR.completeInput (fun target name=>CF.collapseValue native.1
  ((NativeSigma.B.born (S.Complete.atReceipt (AS.stockCfg native.2.2.1) native.2.1.1 0)
    native.2.2.1).activeEnvironment target name,0)) () ()=
 FR.completeInput (fun target name=>CF.collapseValue (AS.bornAfterNative native).1
  ((AS.bornAfterNative native).2.1.1.activeEnvironment target name,0)) () () := rfl

private theorem native_born_input (factory : NS.NativeFactory) (packet : NS.NativePacket) :
 FR.completeInput (fun target name=>NS.collapseNative factory packet
  ((NS.decoded factory packet).activeEnvironment target name)) () ()=
 FR.completeInput (fun target name=>CF.collapseValue (AS.bornAfterNative (AS.nativeAfterAdmission factory packet)).1
  ((AS.bornAfterNative (AS.nativeAfterAdmission factory packet)).2.1.1.activeEnvironment target name,0)) () () := by
 have generated : (fun target name=>NS.collapseNative factory packet
  ((NS.decoded factory packet).activeEnvironment target name))=
  fun target name=>CF.collapseValue (AS.nativeAfterAdmission factory packet).1
   ((NS.decoded factory packet).activeEnvironment target name,0) := by
  funext target name
  cases target
  exact collapse_native_shift factory packet _
 exact (congrArg (fun environment : Env (PairValue (PairValue C.Value)) C.Var=>FR.completeInput environment () ()) generated).trans
  (born_packet_read (AS.nativeAfterAdmission factory packet))

private theorem native_increment_input (factory : NS.NativeFactory) (packet : NS.NativePacket) :
 FR.completeInput (NS.collapsedIncrement factory packet) () ()=
 FR.completeInput (fun target name=>NS.collapseNative factory packet
  ((NS.decoded factory packet).activeEnvironment target name)) () ()-
 FR.completeInput (NS.collapsedOld factory packet) () () := by
 have generated : NS.collapsedIncrement factory packet=
  (fun target name=>NS.collapseNative factory packet ((NS.decoded factory packet).activeEnvironment target name))-
  NS.collapsedOld factory packet := by
  funext target name
  cases target
  exact collapse_native_sub factory packet _ _
 rw [generated]
 simp only [FR.completeInput,Pi.sub_apply,Prod.fst_sub,Prod.snd_sub]
 abel

private theorem native_old_input (factory : NS.NativeFactory) (packet : NS.NativePacket)
 (code : Expr (PairValue (PairValue C.Value)) C.Var ())
 (generated : AI.HasActualInput code packet.1 packet.2.2.1 packet.2.2.2.down) :
 FR.completeInput (NS.collapsedOld factory packet) () ()=
 FR.completeInput (fun target name=>CF.collapseValue packet.1
  ((S.next packet.2.1.1 packet.2.2.1).activeEnvironment target name,0)) () () :=
 congrArg (fun environment : Env (PairValue (PairValue C.Value)) C.Var=>FR.completeInput environment () ()) (native_old_environment factory packet code generated)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

def incrementInput := FR.completeInput (NativeSigma.originalIncrement observation nontrivial half depth ordinal) () ()

theorem actual_born_input :
 FR.completeInput (fun target name=>NS.collapseNative (D.factory observation nontrivial half)
  (originalPredecessor observation nontrivial half depth ordinal)
  ((NativeSigma.originalDecoded observation nontrivial half depth ordinal).activeEnvironment target name)) () ()=
 D.input observation nontrivial half depth ordinal := by
 let read := fun packet : NS.NativePacket=>FR.completeInput
  (fun target name=>CF.collapseValue packet.1 (packet.2.1.1.activeEnvironment target name,0)) () ()
 exact (native_born_input _ _).trans
  (congrArg read (original_next_packet observation nontrivial half depth ordinal)).symm

theorem actual_old_input :
 FR.completeInput (NativeSigma.originalOld observation nontrivial half depth ordinal) () ()=
 originalActionInput observation nontrivial half depth ordinal :=
 native_old_input (D.factory observation nontrivial half)
  (originalPredecessor observation nontrivial half depth ordinal)
  (FR.jointCode (RSource.code observation nontrivial half))
  (original_predecessor_actual_input observation nontrivial half depth ordinal)

/-- Both terms are dependent projections of the same actual native receipt. -/
theorem actual_increment_input :
 incrementInput observation nontrivial half depth ordinal=
 D.input observation nontrivial half depth ordinal-originalActionInput observation nontrivial half depth ordinal :=
 (native_increment_input _ _).trans
  (congrArg₂ (·-·) (actual_born_input observation nontrivial half depth ordinal)
   (actual_old_input observation nontrivial half depth ordinal))

/-- The real decoded native increment is the original R source's exact finite difference. -/
theorem actual_increment_successor :
 incrementInput observation nontrivial half depth (ordinal+1)=
 D.input observation nontrivial half depth (ordinal+1)-D.input observation nontrivial half depth ordinal := by
 rw [actual_increment_input,ExactCurrent.original_action_input_successor]

theorem actual_action_input_zero : originalActionInput observation nontrivial half depth 0=
 Init.split observation nontrivial half depth := by
 change (S.next (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth)).activeEnvironment () ()+0=_
 rw [Init.initial_next_active,add_zero]
 exact congrArg (fun environment=>environment () ()) (Init.actual_born_pair observation nontrivial half depth)

theorem actual_increment_zero : incrementInput observation nontrivial half depth 0=
 D.input observation nontrivial half depth 0-Init.split observation nontrivial half depth := by
 rw [actual_increment_input,actual_action_input_zero]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
