import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.PaidMethod.CurrentAffine.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.PaidMethod.CurrentRaw.Admissions

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFamilyCurrentAffineWrite
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace K
export SourceFamilyCurrentPaidRawInstallation (enrich component combined nativeFrameRestriction native_frame_source noetherianPayment)
end K
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Factory Seed Packet cfg runtime actual_whole actual_next)
end SF
namespace H
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod
 (factory methodBase selected actual_complete_query_written actual_native_faces after_native_whole_action)
end H
namespace Original
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod.Admissions
 (originalFrame originalProgramme originalLanguage baseFactory Operator)
end Original
namespace Act
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod.Admissions.Act (LowValue LowVar sort)
end Act
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (baseRoot root visit queryRoot resultRoot consumerRoot queryLaw resultLaw consumerLaw compilationLaw nextBorn)
end S
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (stockLaw component)
end I
namespace Faces
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower (component combined)
end Faces
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket stockCfg stockScalar stockDecodedEnvironment nextCfg nextBase nextSeed nativeAfterAdmission bornAfterNative)
end AS
namespace AN
export ActualNativeRelationTransport (bornStock born_stock bornHistory)
end AN
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
 (packetAt packetAt_successor actual_index index history_end_index historyAt)
end D
namespace F
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace (whole_recovery wholeFaces)
end F
namespace Canonical
export ActualCofinalInstalledRaw (currentAtStop actual_current)
end Canonical
namespace SO
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation (current)
end SO
namespace Cx
export CofinalRelationGeneratedComplex (natComplex natComplex_d_zero_one completion_kills_generated_differential)
end Cx

private theorem keep_right {T : Type u} (prior : Option (RootedAccountedUnfolding T))
 (tree : RootedAccountedUnfolding T) : ∀ event ∈ tree.trace, event ∈ (Stock.preserve prior tree).trace := by
 cases prior with
 | none => exact fun _ present => present
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1

section Native
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance groups (n : Nat) (t : Sorts) : AddCommGroup (L.Value W n t) := L.groups W n t
variable (original : SF.Factory W X s) (f : W s →+ W s)
def factory := H.factory (K.enrich (enrich original)) f

-- The original affine component is carried through K's strict raw coordinate and the actual H compiler.
def templateFace (n : Nat) (data : SF.Packet (W := W) (X := X) (s := s) n)
 (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s))
 (language : sourceCfg.LowVar = X)
 (frame : M.Frame (Value := L.Value W (n+1)) (Var := sourceCfg.LowVar) (sort := s)) :
 SourceNativeRootSemanticFaceAt (S.root frame (AS.nextCfg (factory original f) n data sourceCfg language))
  (S.visit frame (AS.nextCfg (factory original f) n data sourceCfg language)) := by
 cases sourceCfg with
 | mk Y datum inventory pairInventory =>
  change Y = X at language
  cases language
  let cfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s) := ⟨X,datum,inventory,pairInventory⟩
  let seed := AS.nextSeed (factory original f) n data cfg rfl
  let oldBase := SF.cfg original (n+1) seed
  let affineBase := SF.cfg (enrich original) (n+1) seed
  let method := H.methodBase (K.enrich (enrich original)) f (n+1) seed
  let base := AS.nextBase (factory original f) n data cfg rfl
  let actual := AS.stockCfg base
  let installed := ((SourceNativeProjectionLaw.InstallationAt.componentCoface
   (A.optionalSourceRoot (S.base (A.epoch frame)).root (oldBase.datum (A.epoch frame)).component).source.base
   (component (A.epoch frame))).trans
   (SourceNativeProjectionLaw.InstallationAt.componentCoface (S.base (A.epoch frame)).root.source.base
    (combined (A.epoch frame) oldBase))) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (A.optionalSourceRoot (S.base (A.epoch frame)).root (affineBase.datum (A.epoch frame)).component).source.base
    (K.component (A.epoch frame))) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.componentCoface (S.base (A.epoch frame)).root.source.base
    (K.combined (A.epoch frame) affineBase)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (A.optionalSourceRoot (S.base (A.epoch frame)).root (method.datum (A.epoch frame)).component).source.base
    (Faces.component (A.epoch frame) method)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    { (S.base (A.epoch frame)).root.source.base with projectionLaw := Faces.combined (A.epoch frame) method }
    (I.stockLaw (A.epoch frame) base)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.componentCoface (S.base frame).root.source.base
    (I.component (A.epoch frame) base)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.baseRoot frame actual).source.base (S.queryLaw (A.epoch frame) actual)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.queryRoot frame actual).source.base (S.resultLaw (A.epoch frame) actual)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.resultRoot frame actual).source.base (S.consumerLaw (A.epoch frame) actual)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.consumerRoot frame actual).source.base (S.compilationLaw (A.epoch frame) actual))
  exact {
   projection := installed.embed PUnit.unit
   active := PUnit.unit
   classifier_eq := rfl }

theorem template_source (n : Nat) (data : SF.Packet (W := W) (X := X) (s := s) n)
 (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s))
 (language : sourceCfg.LowVar = X)
 (frame : M.Frame (Value := L.Value W (n+1)) (Var := sourceCfg.LowVar) (sort := s)) :
 HEq (templateFace original f n data sourceCfg language frame).rootRead
  (material (A.epoch frame) (S.actualOccurrence frame)) := by
 cases sourceCfg with
 | mk Y datum inventory pairInventory =>
  change Y = X at language
  cases language
  rfl

def nativeFace (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (frame : M.Frame (Value := L.Value W (AS.nativeAfterAdmission (factory original f) packet).1) (Var := X) (sort := s)) :
 SourceNativeRootSemanticFaceAt (S.root frame (AS.stockCfg (AS.nativeAfterAdmission (factory original f) packet).2.2.1))
 (S.visit frame (AS.stockCfg (AS.nativeAfterAdmission (factory original f) packet).2.2.1)) := by
 rcases packet with ⟨n,⟨old,seed⟩,⟨Y,datum,inventory,pairInventory⟩,⟨language⟩⟩
 change Y = X at language
 cases language
 exact templateFace original f n (old,seed) ⟨X,datum,inventory,pairInventory⟩ rfl frame

theorem native_face_source (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (frame : M.Frame (Value := L.Value W (AS.nativeAfterAdmission (factory original f) packet).1) (Var := X) (sort := s)) :
 HEq (nativeFace original f packet frame).rootRead (material (A.epoch frame) (S.actualOccurrence frame)) := by
 rcases packet with ⟨n,⟨old,seed⟩,⟨Y,datum,inventory,pairInventory⟩,⟨language⟩⟩
 change Y = X at language
 cases language
 exact template_source original f n (old,seed) ⟨X,datum,inventory,pairInventory⟩ rfl frame

theorem template_written_in_born (n : Nat) (data : SF.Packet (W := W) (X := X) (s := s) n)
 (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s))
 (language : sourceCfg.LowVar = X)
 (frame : M.Frame (Value := L.Value W (n+1)) (Var := sourceCfg.LowVar) (sort := s)) :
 ∀ event ∈ (written (A.epoch frame) (S.actualOccurrence frame)).trace,
 event ∈ (AN.bornStock frame (AS.nextBase (factory original f) n data sourceCfg language)).trace := by
 cases sourceCfg with
 | mk Y datum inventory pairInventory =>
  change Y = X at language
  cases language
  let cfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s) := ⟨X,datum,inventory,pairInventory⟩
  let seed := AS.nextSeed (factory original f) n data cfg rfl
  let base := AS.nextBase (factory original f) n data cfg rfl
  have callbackLaw : base.nextInventory frame = some (callback original (n+1) seed frame) := rfl
  intro event present
  apply Feed.original_preserved (AS.stockDecodedEnvironment frame base) (AS.stockScalar frame base) event
  unfold AS.stockScalar
  apply keep_right frame.inventory _ event
  rw [callbackLaw]
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event
   (callback_keeps_trace original (n+1) seed frame event present)

theorem native_written_in_born (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (frame : M.Frame (Value := L.Value W (AS.nativeAfterAdmission (factory original f) packet).1) (Var := X) (sort := s)) :
 ∀ event ∈ (written (A.epoch frame) (S.actualOccurrence frame)).trace,
 event ∈ (AN.bornStock frame (AS.nativeAfterAdmission (factory original f) packet).2.2.1).trace := by
 rcases packet with ⟨n,⟨old,seed⟩,⟨Y,datum,inventory,pairInventory⟩,⟨language⟩⟩
 change Y = X at language
 cases language
 exact template_written_in_born original f n (old,seed) ⟨X,datum,inventory,pairInventory⟩ rfl frame

private theorem gamma_born_of_written {U Y : Sorts → Type u} [∀ t, AddCommGroup (U t)]
 (frame : M.Frame (Value := U) (Var := Y) (sort := s))
 (base : A.Programme (PhysicalValue := U) (PhysicalVar := Y) (sort := s))
 (kept : ∀ event ∈ (written (A.epoch frame) (S.actualOccurrence frame)).trace, event ∈ (AN.bornStock frame base).trace) :
 gamma (A.epoch frame) (S.actualOccurrence frame) ∈ (AN.bornHistory frame base).relationClosure := by
 have inside : gamma (A.epoch frame) (S.actualOccurrence frame) ∈
  (P.prefixHistory (F.sourceOccurrence (paid (A.epoch frame) (S.actualOccurrence frame)))
   (written (A.epoch frame) (S.actualOccurrence frame))).relationClosure := by
  rw [Feed.history_relation_space]
  exact gamma_written (A.epoch frame) (S.actualOccurrence frame)
 exact SourceOperationPaidRelations.relations_next _ _ _ _ kept inside

def nativeGamma (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :=
 let native := AS.nativeAfterAdmission (factory original f) packet
 let frame := H.selected native
 (⟨gamma (A.epoch frame) (S.actualOccurrence frame), gamma_born_of_written frame native.2.2.1
   (native_written_in_born original f packet frame)⟩ : (AN.bornHistory frame native.2.2.1).relationClosure)

structure PacketReceipt (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) where
 environment : Env (L.Value W packet.1) X
 beta : Formal ℤ (L.Value W packet.1) X s
 nu : L.Value W packet.1 s →₀ ℤ
 gamma : Formal ℤ (L.Value W packet.1) X s
 certificate : RelationIndex ℤ environment s →₀ ℤ
 certificate_source : relationMap (R := ℤ) environment certificate = gamma
 split : beta = gamma + constantMap (R := ℤ) nu
 oldTrace : SourceInventoryExecutionFeed.Inventory (V := L.Value W packet.1) (X := X) (s := s)
 written : SourceInventoryExecutionFeed.Inventory (V := L.Value W packet.1) (X := X) (s := s)
 inventory : SourceInventoryExecutionFeed.Inventory (V := L.Value W packet.1) (X := X) (s := s)
 actual_inventory : packet.2.1.1.inventory = some inventory
 every_written : ∀ event ∈ written.trace, event ∈ inventory.trace
 gamma_in_inventory : gamma ∈ Feed.relationSpace inventory

def nextReceipt (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 PacketReceipt (AS.bornAfterNative (AS.nativeAfterAdmission (factory original f) packet)) := by
 let native := AS.nativeAfterAdmission (factory original f) packet
 let frame := H.selected native
 let occurrence := S.actualOccurrence frame
 have belongs := (nativeGamma original f packet).property
 change gamma (A.epoch frame) occurrence ∈ (AN.bornHistory frame native.2.2.1).relationClosure at belongs
 rw [Feed.history_relation_space] at belongs
 exact {
  environment := updatedEnvironment (A.epoch frame) occurrence
  beta := beta (A.epoch frame) occurrence
  nu := nu (A.epoch frame) occurrence
  gamma := gamma (A.epoch frame) occurrence
  certificate := certificate (A.epoch frame) occurrence
  certificate_source := affine_certificate (A.epoch frame) occurrence
  split := (sub_add_cancel _ _).symm
  oldTrace := sourceInventory (A.epoch frame) occurrence
  written := written (A.epoch frame) occurrence
  inventory := AN.bornStock frame native.2.2.1
  actual_inventory := AN.born_stock frame native.2.2.1
  every_written := native_written_in_born original f packet frame
  gamma_in_inventory := belongs }

private theorem differential_value {Root Generator : Type u} {root : RootedAccountedUnfolding Root}
 {seed : RootedAccountedUnfolding (PresentedRelationEventAt Generator)}
 {continuation : RootedAccountedUnfolding (PresentedRelationEventAt Generator → RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
 (history : RootGeneratedCofinalHistoryAt root seed continuation) (relation : history.relationClosure) :
 (((Cx.natComplex history).d 0 1).hom relation).val = relation.val :=
 congrArg (fun delta : (Cx.natComplex history).X 0 ⟶ (Cx.natComplex history).X 1 => (delta.hom relation).val)
  (Cx.natComplex_d_zero_one history)
def native_affine_consumer (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :=
 let native := AS.nativeAfterAdmission (factory original f) packet
 let frame := H.selected native
 let occurrence := S.actualOccurrence frame
 let m := paid (A.epoch frame) occurrence
 let relation := nativeGamma original f packet
 PProd.mk (nativeFace original f packet frame) <|
 PProd.mk (native_face_source original f packet frame) <|
 PProd.mk (material (A.epoch frame) occurrence) <|
 PProd.mk (affine_certificate (A.epoch frame) occurrence) <|
 PProd.mk (free_value_read (A.epoch frame) occurrence) <|
 PProd.mk (differential_read (A.epoch frame) occurrence) <|
 PProd.mk (F.actual_inverse m) <|
 PProd.mk (F.native_zero_iff m) <|
 PProd.mk (F.whole_recovery m (beta (A.epoch frame) occurrence)) <|
 PProd.mk (F.whole_recovery m (constantMap (R := ℤ) (nu (A.epoch frame) occurrence))) <|
 PProd.mk (F.whole_recovery m (gamma (A.epoch frame) occurrence)) <|
 PProd.mk (show beta (A.epoch frame) occurrence = gamma (A.epoch frame) occurrence + constantMap (R := ℤ) (nu (A.epoch frame) occurrence)
  from (sub_add_cancel _ _).symm) <|
 PProd.mk (native_written_in_born original f packet frame) <|
 PProd.mk relation <|
 PProd.mk (differential_value (AN.bornHistory frame native.2.2.1) relation) <|
 PProd.mk (Cx.completion_kills_generated_differential (AN.bornHistory frame native.2.2.1) relation) <|
 PProd.mk (Feed.complete_source_cost (updatedEnvironment (A.epoch frame) occurrence) (sourceInventory (A.epoch frame) occurrence)) <|
 PProd.mk (H.actual_complete_query_written (K.enrich (enrich original)) f packet) <|
 PProd.mk (H.actual_native_faces (K.enrich (enrich original)) f packet)
 (K.noetherianPayment frame native.2.2.1)
end Native

section Root
open CategoryTheory
variable {Nw : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {Space : Type u} [NormedAddCommGroup Space] [InnerProductSpace ℂ Space] [CompleteSpace Space]
variable (root : SourceNativeLivingRootClosure Nw V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt Space root)
local instance rootGroups (t) : AddCommGroup (Act.LowValue root visit rec t) := inferInstance
local instance rootFamilyGroups (n : Nat) (t) : AddCommGroup (L.Value (Act.LowValue root visit rec) n t) :=
 L.groups (Act.LowValue root visit rec) n t
variable (U7 : U7ProducerCalculus Nw) (calculus : U7ObstructionEvolutionCalculus Nw U7)
variable (anchor sourceStage stage count : Nat) (f : Original.Operator root visit rec)
abbrev initial := Original.originalFrame root visit rec U7 calculus anchor sourceStage stage count
abbrev firstCfg := Original.originalProgramme root visit rec U7 calculus anchor sourceStage stage
abbrev language := Original.originalLanguage root visit rec U7 calculus anchor sourceStage stage
abbrev baseFactory := Original.baseFactory root visit rec
def queryFactory := factory (baseFactory root visit rec) f
def sourceRuntime := SF.runtime (queryFactory root visit rec f)
 (initial root visit rec U7 calculus anchor sourceStage stage count) (firstCfg root visit rec U7 calculus anchor sourceStage stage)
 (language root visit rec U7 calculus anchor sourceStage stage)
abbrev actualPacket (k : Nat) := D.packetAt (queryFactory root visit rec f)
 (initial root visit rec U7 calculus anchor sourceStage stage count) (firstCfg root visit rec U7 calculus anchor sourceStage stage)
 (language root visit rec U7 calculus anchor sourceStage stage) k
local notation "method" => queryFactory root visit rec f
local notation "old" => initial root visit rec U7 calculus anchor sourceStage stage count
local notation "cfg" => firstCfg root visit rec U7 calculus anchor sourceStage stage
local notation "lang" => language root visit rec U7 calculus anchor sourceStage stage
local notation "packet" => actualPacket root visit rec U7 calculus anchor sourceStage stage count f

-- Transport the whole receipt through the actual packet equation, preserving its grade and full free word.
def receiptAtNext (k : Nat) : PacketReceipt (packet (k+1)) :=
 (congrArg PacketReceipt (D.packetAt_successor method old cfg lang k)).mpr
  (nextReceipt (baseFactory root visit rec) f (packet k))

def nextHistory (k : Nat) := P.prefixHistory
 (RootedAccountedUnfolding.zero (S.actualOccurrence (packet (k+1)).2.1.1))
 (receiptAtNext root visit rec U7 calculus anchor sourceStage stage count f k).inventory

def actualNextGamma (k : Nat) : (nextHistory root visit rec U7 calculus anchor sourceStage stage count f k).relationClosure := by
 let data := receiptAtNext root visit rec U7 calculus anchor sourceStage stage count f k
 refine ⟨data.gamma, ?_⟩
 change data.gamma ∈ (P.prefixHistory
  (RootedAccountedUnfolding.zero (S.actualOccurrence (packet (k+1)).2.1.1)) data.inventory).relationClosure
 rw [Feed.history_relation_space]
 exact data.gamma_in_inventory

theorem actual_next_root (k : Nat) : Canonical.currentAtStop method old cfg lang (k+1) =
 SO.current (AS.bornAfterNative (AS.nativeAfterAdmission method (packet k))).2.1.1
  (AS.bornAfterNative (AS.nativeAfterAdmission method (packet k))).2.2.1 :=
 (Canonical.actual_current method old cfg lang (k+1)).trans
  (congrArg (fun value => SO.current value.2.1.1 value.2.2.1) (D.packetAt_successor method old cfg lang k))

def cofinal_current_affine_write (k : Nat) :=
 PProd.mk (native_affine_consumer (baseFactory root visit rec) f (packet k)) <|
 PProd.mk (receiptAtNext root visit rec U7 calculus anchor sourceStage stage count f k) <|
 PProd.mk (actual_next_root root visit rec U7 calculus anchor sourceStage stage count f k) <|
 PProd.mk (actualNextGamma root visit rec U7 calculus anchor sourceStage stage count f k) <|
 PProd.mk (differential_value (nextHistory root visit rec U7 calculus anchor sourceStage stage count f k)
  (actualNextGamma root visit rec U7 calculus anchor sourceStage stage count f k)) <|
 PProd.mk (Cx.completion_kills_generated_differential (nextHistory root visit rec U7 calculus anchor sourceStage stage count f k)
  (actualNextGamma root visit rec U7 calculus anchor sourceStage stage count f k)) <|
 PProd.mk (D.packetAt_successor method old cfg lang k) <|
 PProd.mk (D.actual_index method old cfg lang k) <|
 PProd.mk (D.actual_index method old cfg lang (k+1)) <|
 PProd.mk (SF.actual_whole method old cfg lang (D.index method old cfg lang (k+1)-1)) <|
 PProd.mk (SF.actual_next method old cfg lang (D.index method old cfg lang (k+1)-1)) <|
 PProd.mk (D.history_end_index method old cfg lang k)
 (D.historyAt method old cfg lang k)
end Root
end SourceFamilyCurrentAffineWrite
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
