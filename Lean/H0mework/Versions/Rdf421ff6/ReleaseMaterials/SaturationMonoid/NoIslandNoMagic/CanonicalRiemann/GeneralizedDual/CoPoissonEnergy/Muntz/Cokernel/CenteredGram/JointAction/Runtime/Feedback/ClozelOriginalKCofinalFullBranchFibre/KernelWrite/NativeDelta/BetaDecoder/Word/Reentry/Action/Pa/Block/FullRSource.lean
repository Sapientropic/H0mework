import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.BornInventory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.FullRCode

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRSource
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace B
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block
 (parentBorn parentSplit sourceRelationBody programme lowBase nativeBorn)
end B
namespace BI
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.BornInventory
 (inventory np pn born_pair_inventory)
end BI
namespace WR
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence)
end WR
namespace FC
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRCode (code)
end FC
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionResultAt)
end R
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (programme oldPaid old_paid_const)
end WB
namespace CF
export SourceGeneratedInquiryReceiptAction.Configured (lowBareInitial lowPairWritten)
end CF
namespace PT
export SourceGeneratedInquiryReceiptAction.Configured.PairTransport
 (bornPairInventory born_pair_inventory bornSegment)
end PT
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve)
end Stock

namespace Assembly
variable {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
variable (baseProgramme : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()))
variable (law : (receiver : Reentry.A.M.Frame (Value := Value) (Var := Var) (sort := ())) →
 SourceNativeProjectionLaw (S.base receiver).root.source.base.restructuringSource.toLedgerSource)
variable (reader : (receiver : Reentry.A.M.Frame (Value := Value) (Var := Var) (sort := ())) →
 {current : J.Current receiver.registered} → I.Occurrence receiver (current := current) →
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value := PairValue Value) (Var := baseProgramme.LowVar) (sort := ()))
variable (carry : (receiver : Reentry.A.M.Frame (Value := Value) (Var := Var) (sort := ())) →
 {current : J.Current receiver.registered} → I.Occurrence receiver (current := current) →
 Option (Inventory (V := PairValue (PairValue Value)) (X := baseProgramme.LowVar) (s := ())))
variable (receiver : Reentry.A.M.Frame (Value := Value) (Var := Var) (sort := ()))

theorem epoch_pair_inventory : (A.epoch receiver).pairInventory = receiver.pairInventory := rfl

def source := (S.root receiver baseProgramme).source.base.withProjectionCoface (law receiver)

def programme : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()) :=
 { baseProgramme with datum := fun receiver => { baseProgramme.datum receiver with
   component := some (source baseProgramme law receiver).projectionLaw
   calculationReader := some (reader receiver)
   nextPairInventoryAt := some (carry receiver) } }

local notation "cfg" => programme baseProgramme law reader carry

theorem reader_preserved {current : J.Current receiver.registered} (supplied : I.Occurrence receiver (current := current)) :
 ((cfg).datum receiver).reader supplied = (baseProgramme.datum receiver).reader supplied := rfl

theorem decoder_preserved :
 ((cfg).datum receiver).nextEnvironmentRead = (baseProgramme.datum receiver).nextEnvironmentRead := rfl

theorem dependent_decoder_preserved :
 ((cfg).datum receiver).nextEnvironmentReadAt = (baseProgramme.datum receiver).nextEnvironmentReadAt := rfl

theorem inventory_preserved : (cfg).nextInventory = baseProgramme.nextInventory := rfl

theorem pair_inventory_preserved : (cfg).nextPairInventory = baseProgramme.nextPairInventory := rfl

def componentInstallation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
 (S.base receiver).root.source.base (source baseProgramme law (A.epoch receiver)).projectionLaw).trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.baseRoot receiver cfg).source.base
  (S.queryLaw (A.epoch receiver) cfg)) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.queryRoot receiver cfg).source.base
  (S.resultLaw (A.epoch receiver) cfg)) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.resultRoot receiver cfg).source.base
  (S.consumerLaw (A.epoch receiver) cfg)) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.consumerRoot receiver cfg).source.base
  (S.compilationLaw (A.epoch receiver) cfg))

def oldInstallation := (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
 (S.root receiver baseProgramme).source.base (law (A.epoch receiver))).trans
 (componentInstallation baseProgramme law reader carry receiver)

def sourceInstallation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
 (S.root receiver baseProgramme).source.base (law (A.epoch receiver))).trans
 (componentInstallation baseProgramme law reader carry receiver)

def OldInstallationType := type_of% (oldInstallation baseProgramme law reader carry receiver)
def oldInstalled : OldInstallationType baseProgramme law reader carry receiver :=
 oldInstallation baseProgramme law reader carry receiver

def SourceInstallationType := type_of% (sourceInstallation baseProgramme law reader carry receiver)
def sourceInstalled : SourceInstallationType baseProgramme law reader carry receiver :=
 sourceInstallation baseProgramme law reader carry receiver

end Assembly

local instance baseGroups (initial : Nat) : ∀ t, AddCommGroup (BaseValue initial t) :=
 DR.L.groups (PairValue C.Value) initial
local instance originGroups (initial : Nat) : ∀ t, AddCommGroup (DR.L.Value (BaseValue initial) 2 t) :=
 DR.L.groups (BaseValue initial) 2
local instance runtimeGroups (initial : Nat) : ∀ t,
 AddCommGroup (DR.L.Value (DR.L.Value (BaseValue initial) 2) 0 t) := DR.L.groups (DR.L.Value (BaseValue initial) 2) 0

variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
variable (initial : Nat)
variable (frame : Reentry.A.M.Frame (Value := PairValue (BaseValue initial)) (Var := C.Var) (sort := ()))
variable (base : A.Programme (PhysicalValue := PairValue (BaseValue initial)) (PhysicalVar := C.Var) (sort := ()))
variable (before : Inventory (V := BaseValue initial) (X := C.Var) (s := ()))
variable (oldEnvironment : Env (BaseValue initial) C.Var)
variable (admissions : List (AdmissionReceipt.Admission before (Reentry.AS.stockScalar frame base)))
variable (sourceFrame : Reentry.A.M.Frame (Value := PairValue (PairValue (BaseValue initial))) (Var := C.Var) (sort := ()))

local notation "parent" => B.parentBorn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "cfg" => B.programme observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "low" => B.lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "body" => B.sourceRelationBody observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

abbrev born := B.nativeBorn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
abbrev continuation := M.programme parent cfg low

/-- The full next action uses the same source body as the installed NP/PN equations. -/
def code : Expr (PairValue (BlockValue initial)) C.Var () :=
 FC.code observation nontrivial half initial body

def carriedSource :=
 (BI.inventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).map T.liftEvent

variable (receiver : Reentry.A.M.Frame (Value := BlockValue initial) (Var := C.Var) (sort := ()))
variable {current : J.Current receiver.registered}
variable (supplied : I.Occurrence receiver (current := current))

/-- The fixed prefix retains its literal slots while the last field follows the supplied occurrence. -/
structure SourceAt where
 prefixInventory : Inventory (V := PairValue (BlockValue initial)) (X := C.Var) (s := ())
 inventory_eq : (born observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).pairInventory = some prefixInventory
 np : WR.RelationOccurrence prefixInventory
 pn : WR.RelationOccurrence prefixInventory
 sourceBody : Expr (CodeValue initial) C.Var ()
 currentMaterial : type_of% (I.materialAt receiver supplied)

def sourceAt : SourceAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver supplied :=
 ⟨BI.inventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame,
  BI.born_pair_inventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame,
  BI.np observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame,
  BI.pn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame,
  body, I.materialAt receiver supplied⟩

def sourceLaw : SourceNativeProjectionLaw
 (S.base receiver).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit
 ActiveAt := fun _ {_current} _ => PUnit
 InactiveAt := fun _ {_current} _ => PEmpty
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} occurrence _ =>
  SourceAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver occurrence
 project := fun _ {_current} occurrence _ =>
  sourceAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver occurrence

def fullSource := Assembly.source (continuation observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (fun receiver => sourceLaw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver) receiver

def codeReader (_supplied : I.Occurrence receiver (current := current)) : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value := PairValue (BlockValue initial)) (Var := C.Var) (sort := ()) :=
 let source := sourceAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver _supplied
 ⟨pairEnvironment (receiver.environment (receiver.old.root.emitted current.1)) 0,
  FC.code observation nontrivial half initial source.sourceBody⟩

/-- Preserve any installed callback before adding this receiver's complete pair inventory. -/
def carryAt : Option (Inventory (V := PairValue (PairValue (BlockValue initial))) (X := C.Var) (s := ())) :=
 let inherited := ((continuation observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).datum receiver).nextPairInventoryAt.bind
  (fun read => read supplied)
 match receiver.pairInventory with
 | none => inherited
 | some source => some (Stock.preserve inherited (source.map T.liftEvent))

local notation "Law" => (fun receiver => sourceLaw observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver)
local notation "Reader" => (fun receiver {_current} supplied => codeReader observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver supplied)
local notation "Carry" => (fun receiver {_current} supplied => carryAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver supplied)

def programme : A.Programme (PhysicalValue := BlockValue initial) (PhysicalVar := C.Var) (sort := ()) :=
 Assembly.programme (continuation observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) Law Reader Carry

local notation "newCfg" => programme observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "oldCfg" => continuation observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "f" => born observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

theorem reader_preserved : ((newCfg).datum receiver).reader supplied = ((oldCfg).datum receiver).reader supplied :=
 Assembly.reader_preserved oldCfg Law Reader Carry receiver supplied
theorem decoder_preserved : ((newCfg).datum receiver).nextEnvironmentRead = ((oldCfg).datum receiver).nextEnvironmentRead :=
 Assembly.decoder_preserved oldCfg Law Reader Carry receiver
theorem dependent_decoder_preserved : ((newCfg).datum receiver).nextEnvironmentReadAt = ((oldCfg).datum receiver).nextEnvironmentReadAt :=
 Assembly.dependent_decoder_preserved oldCfg Law Reader Carry receiver
theorem inventory_preserved : (newCfg).nextInventory = (oldCfg).nextInventory :=
 Assembly.inventory_preserved oldCfg Law Reader Carry
theorem pair_inventory_preserved : (newCfg).nextPairInventory = (oldCfg).nextPairInventory :=
 Assembly.pair_inventory_preserved oldCfg Law Reader Carry
theorem inherited_callback_none : ((oldCfg).datum receiver).nextPairInventoryAt = none := rfl

def componentInstallation := Assembly.componentInstallation oldCfg Law Reader Carry receiver

def oldInstallation : Assembly.OldInstallationType oldCfg Law Reader Carry receiver :=
 Assembly.oldInstalled oldCfg Law Reader Carry receiver

def sourceInstallation : Assembly.SourceInstallationType oldCfg Law Reader Carry receiver :=
 Assembly.sourceInstalled oldCfg Law Reader Carry receiver

def sourceFace : SourceNativeRootSemanticFaceAt (S.root receiver newCfg) (S.visit receiver newCfg) where
 projection := (sourceInstallation observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl

abbrev sourceMaterial := (sourceFace observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver).rootRead

theorem actual_carry :
 carryAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame (A.epoch f) (S.actualOccurrence f) =
 some (carriedSource observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) := by
 unfold carryAt
 rw [inherited_callback_none observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame (A.epoch f)]
 rw [Assembly.epoch_pair_inventory f]
 rw [BI.born_pair_inventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame]
 rfl

theorem initial_pair_inventory : (CF.lowBareInitial f newCfg).pairInventory =
 some (carriedSource observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) :=
 actual_carry observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

abbrev material := R.actualMaterial f newCfg
abbrev oldPaid := WB.oldPaid f newCfg
abbrev result := R.actionResultAt f newCfg (S.actualOccurrence f)

local notation "m" => material observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "paid" => oldPaid observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame
local notation "raw" => code observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

theorem material_raw : (m).raw = raw := rfl
theorem material_environment : (m).environment = pairEnvironment (f).activeEnvironment 0 := rfl
theorem material_state : (m).state =
 (result observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).2.1 :=
 SourceGeneratedInquiryReceiptAction.actual_calculation_state f newCfg

def actualTrace : Trace (m).environment raw (.const paid) :=
 Eq.mp (congrArg (fun terminal => Trace (m).environment raw terminal) (WB.old_paid_const f newCfg)) (m).state.2

theorem actual_trace_cost :
 (actualTrace observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).length = 5 :=
 (actualTrace observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).length_to_const.trans rfl

def fullWrite (value : PairValue (BlockValue initial) ()) : Env (PairValue (BlockValue initial)) C.Var :=
 fun target _ => by cases target; exact value

local notation "write" => fullWrite initial
abbrev lowBase := WB.programme f newCfg write
local notation "nextBase" => lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

abbrev generatedAction := M.generatedAction f newCfg nextBase
abbrev runtime := M.runtime f newCfg nextBase
abbrev nextMaterialFace := M.nextMaterialFace f newCfg nextBase
abbrev selected := M.selected f newCfg nextBase
abbrev nativeBorn := M.born f newCfg nextBase
abbrev nativeValue := M.nativeValue f newCfg nextBase
abbrev inventory := PT.bornPairInventory f newCfg write

def initialSegment : SourceInventoryTraceSegment
 (carriedSource observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (CF.lowPairWritten f newCfg) := by
 unfold CF.lowPairWritten
 rw [initial_pair_inventory]
 exact .left _ _

def bornSegment : SourceInventoryTraceSegment
 (carriedSource observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 (inventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) :=
 (initialSegment observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).trans
  (PT.bornSegment f newCfg write)

theorem born_pair_inventory :
 (nativeBorn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).pairInventory =
 some (inventory observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame) :=
 PT.born_pair_inventory f newCfg write

theorem actual_writeback : type_of% (@M.actual_writeback _ _ _ _ _ f newCfg write) :=
 @M.actual_writeback _ _ _ _ _ f newCfg write

theorem whole_first : type_of% (M.whole_first f newCfg nextBase) := M.whole_first f newCfg nextBase
theorem target_next : type_of% (M.target_next f newCfg nextBase) := M.target_next f newCfg nextBase
theorem compiles : type_of% (M.compiles f newCfg nextBase) := M.compiles f newCfg nextBase
theorem actual_receipt_next : type_of% (M.actual_receipt_next f newCfg nextBase) := M.actual_receipt_next f newCfg nextBase
theorem actual_receipt_compiles : type_of% (M.actual_receipt_compiles f newCfg nextBase) := M.actual_receipt_compiles f newCfg nextBase
theorem native_effect : type_of% (M.native_effect f newCfg nextBase) := M.native_effect f newCfg nextBase
theorem native_inverse : type_of% (M.native_inverse f newCfg nextBase) := M.native_inverse f newCfg nextBase

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
