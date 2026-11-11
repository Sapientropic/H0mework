import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.PaidMethod.CurrentRaw.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.PaidMethod.Admissions
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.EnvironmentUpdate.CurrentMaterial.RootedEffect.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFamilyCurrentPaidRawInstallation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket nativeAfterAdmission bornAfterNative localNativeReceipt)
end AS
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
 (packetAt packetAt_successor packetAt_successor_grade actual_index index historyAt history_end_index complete_word actual_source_action)
end D
namespace H
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod
 (selected actual_born_stock)
end H
namespace Original
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod.Admissions
 (originalFrame originalProgramme originalLanguage baseFactory Operator)
end Original
namespace Act
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod.Admissions.Act (LowValue LowVar sort)
end Act
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation (readRaw)
end O
namespace SO
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation (current root)
end SO
namespace Canonical
export ActualCofinalInstalledRaw (currentAtStop actual_current rawAtStop rawAtStop_read materialAtStop whole_word whole_trace)
end Canonical
namespace AN
export ActualNativeRelationTransport (paid)
end AN
namespace RE
export SourceFamilyActualCurrentMaterialRootedEffect
 (paid_updated_environment born_request_input born_actual_paid born_actual_payment born_payment_entry born_payment_ledger born_payment_visit born_whole_receipt born_payment_whole_destination)
end RE
namespace Pay
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment
 (debtCurrent paidContinuation no_refill continuation_wellFounded)
end Pay
namespace B
export ActualNativeBornSourceEffect (born)
end B

section Native
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance nativeGroups (n : Nat) (t : Sorts) : AddCommGroup (L.Value W n t) := L.groups W n t
variable (original : SF.Factory W X s) (f : W s →+ W s)

def templateRawRestriction (n : Nat) (data : SF.Packet (W := W) (X := X) (s := s) n)
 (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s))
 (language : sourceCfg.LowVar = X)
 (frame : M.Frame (Value := L.Value W (n+1)) (Var := sourceCfg.LowVar) (sort := s)) :
 SourceOperationInquiry.Context.RawRestrictionAt
  (PhysicalValue := L.Value W (n+1)) (PhysicalVar := sourceCfg.LowVar) (sort := s)
  (SO.current frame (AS.nextCfg (H.factory (enrich original) f) n data sourceCfg language)) := by
 cases sourceCfg with
 | mk Y datum inventory pairInventory =>
  change Y = X at language
  cases language
  let cfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s) :=
   ⟨X,datum,inventory,pairInventory⟩
  let seed := AS.nextSeed (H.factory (enrich original) f) n data cfg rfl
  let originalCfg := SF.cfg original (n+1) seed
  let method := H.methodBase (enrich original) f (n+1) seed
  let base := AS.nextBase (H.factory (enrich original) f) n data cfg rfl
  let actual := AS.stockCfg base
  let installed := ((SourceNativeProjectionLaw.InstallationAt.componentCoface
   (A.optionalSourceRoot (S.base (A.epoch frame)).root (originalCfg.datum (A.epoch frame)).component).source.base
   (component (A.epoch frame))).trans
   (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (S.base (A.epoch frame)).root.source.base (combined (A.epoch frame) originalCfg))) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (A.optionalSourceRoot (S.base (A.epoch frame)).root (method.datum (A.epoch frame)).component).source.base
    (Faces.component (A.epoch frame) method)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    { (S.base (A.epoch frame)).root.source.base with projectionLaw := Faces.combined (A.epoch frame) method }
    (I.stockLaw (A.epoch frame) base)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.componentCoface (S.base frame).root.source.base
    (I.component (A.epoch frame) base)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.baseRoot frame actual).source.base
    (S.queryLaw (A.epoch frame) actual)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.queryRoot frame actual).source.base
    (S.resultLaw (A.epoch frame) actual)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.resultRoot frame actual).source.base
    (S.consumerLaw (A.epoch frame) actual)) |>.trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.consumerRoot frame actual).source.base
    (S.compilationLaw (A.epoch frame) actual))
  exact {
   projection := installed.embed PUnit.unit
   active := PUnit.unit
   classifier_eq := rfl
   payload_eq := rfl }

theorem template_raw_source (n : Nat) (data : SF.Packet (W := W) (X := X) (s := s) n)
 (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := s))
 (language : sourceCfg.LowVar = X)
 (frame : M.Frame (Value := L.Value W (n+1)) (Var := sourceCfg.LowVar) (sort := s)) :
 O.readRaw _ (templateRawRestriction original f n data sourceCfg language frame) =
 currentRaw (A.epoch frame) (S.actualOccurrence frame) := by
 cases sourceCfg with
 | mk Y datum inventory pairInventory =>
  change Y = X at language
  cases language
  rfl

def nativeFrameRestriction (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (frame : M.Frame (Value := L.Value W (AS.nativeAfterAdmission (H.factory (enrich original) f) packet).1)
  (Var := X) (sort := s)) :
 SourceOperationInquiry.Context.RawRestrictionAt
  (PhysicalValue := L.Value W (AS.nativeAfterAdmission (H.factory (enrich original) f) packet).1)
  (PhysicalVar := X) (sort := s)
  (SO.current frame (AS.stockCfg (AS.nativeAfterAdmission (H.factory (enrich original) f) packet).2.2.1)) := by
 rcases packet with ⟨n,⟨old,seed⟩,⟨Y,datum,inventory,pairInventory⟩,⟨language⟩⟩
 change Y = X at language
 cases language
 exact templateRawRestriction original f n (old,seed) ⟨X,datum,inventory,pairInventory⟩ rfl frame

theorem native_frame_source (packet : AS.AdmissionPacket (W := W) (X := X) (s := s))
 (frame : M.Frame (Value := L.Value W (AS.nativeAfterAdmission (H.factory (enrich original) f) packet).1)
  (Var := X) (sort := s)) :
 O.readRaw _ (nativeFrameRestriction original f packet frame) = currentRaw (A.epoch frame) (S.actualOccurrence frame) := by
 rcases packet with ⟨n,⟨old,seed⟩,⟨Y,datum,inventory,pairInventory⟩,⟨language⟩⟩
 change Y = X at language
 cases language
 exact template_raw_source original f n (old,seed) ⟨X,datum,inventory,pairInventory⟩ rfl frame

structure PacketReceipt (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) where
 restriction : SourceOperationInquiry.Context.RawRestrictionAt
  (PhysicalValue := L.Value W packet.1) (PhysicalVar := X) (sort := s)
  (SO.current packet.2.1.1 packet.2.2.1)
 source : O.readRaw _ restriction = currentRaw (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)

def nextReceipt (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 PacketReceipt (AS.bornAfterNative (AS.nativeAfterAdmission (H.factory (enrich original) f) packet)) :=
 { restriction := nativeFrameRestriction original f packet
    (AS.bornAfterNative (AS.nativeAfterAdmission (H.factory (enrich original) f) packet)).2.1.1
   source := native_frame_source original f packet
    (AS.bornAfterNative (AS.nativeAfterAdmission (H.factory (enrich original) f) packet)).2.1.1 }
private theorem born_current_raw {U Y : Sorts → Type u} [∀ t, AddCommGroup (U t)]
 (frame : M.Frame (Value := U) (Var := Y) (sort := s))
 (cfg : A.Programme (PhysicalValue := U) (PhysicalVar := Y) (sort := s)) :
 (B.born frame cfg).rawRead = currentRaw (A.epoch frame) (S.actualOccurrence frame) := by
 have source := RE.born_request_input frame cfg
 exact congrArg₂ (fun env code =>
  (⟨env,code⟩ : SourceOperationInquiry.Context.Raw (PhysicalValue := U) (PhysicalVar := Y) (sort := s)))
  source.1 source.2

def RegisteredFrom (current next : AS.AdmissionPacket (W := W) (X := X) (s := s)) : Prop :=
 let native := AS.nativeAfterAdmission (H.factory (enrich original) f) current
 HEq next.2.1.1.rawRead (currentRaw (A.epoch (H.selected native)) (S.actualOccurrence (H.selected native)))

theorem registered_from_next (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 RegisteredFrom original f packet (AS.bornAfterNative (AS.nativeAfterAdmission (H.factory (enrich original) f) packet)) :=
 heq_of_eq (born_current_raw (H.selected (AS.nativeAfterAdmission (H.factory (enrich original) f) packet))
  (AS.nativeAfterAdmission (H.factory (enrich original) f) packet).2.2.1)

-- This is the existing exact payment in its own registered math-entry epoch.
def noetherianPayment {U Y : Sorts → Type u} [∀ t, AddCommGroup (U t)]
 (frame : M.Frame (Value := U) (Var := Y) (sort := s))
 (cfg : A.Programme (PhysicalValue := U) (PhysicalVar := Y) (sort := s)) :=
 let born := B.born frame cfg
 let paid := RE.born_actual_paid frame cfg
 let continuation := Pay.paidContinuation born paid.1 paid.2.down
 let edge : SourceNativePaidRootDebtContinuationRel continuation.target (Pay.debtCurrent born) := ⟨continuation,rfl⟩
 let targetAcc := ((Pay.continuation_wellFounded born).apply (Pay.debtCurrent born)).inv edge
 PProd.mk continuation <|
 PProd.mk (show continuation.payment = RE.born_actual_payment frame cfg from rfl) <|
 PProd.mk continuation.payment.strictDebit <|
 PProd.mk continuation.strictDebit <|
 PProd.mk (Pay.no_refill born) <|
 PProd.mk (RE.born_payment_entry frame cfg) <|
 PProd.mk (RE.born_payment_whole_destination frame cfg) targetAcc

end Native

section Root
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
def queryFactory := H.factory (enrich (baseFactory root visit rec)) f
def sourceRuntime := SF.runtime (queryFactory root visit rec f)
 (initial root visit rec U7 calculus anchor sourceStage stage count)
 (firstCfg root visit rec U7 calculus anchor sourceStage stage)
 (language root visit rec U7 calculus anchor sourceStage stage)
abbrev actualPacket (k : Nat) := D.packetAt (queryFactory root visit rec f)
 (initial root visit rec U7 calculus anchor sourceStage stage count)
 (firstCfg root visit rec U7 calculus anchor sourceStage stage)
 (language root visit rec U7 calculus anchor sourceStage stage) k

local notation "method" => queryFactory root visit rec f
local notation "old" => initial root visit rec U7 calculus anchor sourceStage stage count
local notation "cfg" => firstCfg root visit rec U7 calculus anchor sourceStage stage
local notation "lang" => language root visit rec U7 calculus anchor sourceStage stage
local notation "packet" => actualPacket root visit rec U7 calculus anchor sourceStage stage count f
local notation "runtime" => sourceRuntime root visit rec U7 calculus anchor sourceStage stage count f

-- The whole generated packet is transported; neither its State nor its grade is rewritten independently.
def receiptAtNext (k : Nat) : PacketReceipt (packet (k+1)) :=
 (congrArg PacketReceipt (D.packetAt_successor method old cfg lang k)).mpr
  (nextReceipt (baseFactory root visit rec) f (packet k))

def rawAtNext (k : Nat) : SourceOperationInquiry.Context.RawRestrictionAt
 (PhysicalValue := L.Value (Act.LowValue root visit rec) (packet (k+1)).1)
 (PhysicalVar := Act.LowVar root visit rec) (sort := Act.sort root rec)
 (Canonical.currentAtStop method old cfg lang (k+1)) :=
 Eq.mp (congrArg (SourceOperationInquiry.Context.RawRestrictionAt
  (PhysicalValue := L.Value (Act.LowValue root visit rec) (packet (k+1)).1)
  (PhysicalVar := Act.LowVar root visit rec) (sort := Act.sort root rec))
  (Canonical.actual_current method old cfg lang (k+1)).symm)
  (receiptAtNext root visit rec U7 calculus anchor sourceStage stage count f k).restriction

open private restriction_transport_read from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Source

theorem raw_at_next_source (k : Nat) : O.readRaw _ (rawAtNext root visit rec U7 calculus anchor sourceStage stage count f k) =
 currentRaw (A.epoch (packet (k+1)).2.1.1) (S.actualOccurrence (packet (k+1)).2.1.1) :=
 (restriction_transport_read _ _ (Canonical.actual_current method old cfg lang (k+1)).symm
  (receiptAtNext root visit rec U7 calculus anchor sourceStage stage count f k).restriction).trans
  (receiptAtNext root visit rec U7 calculus anchor sourceStage stage count f k).source

theorem actual_current_effect (k : Nat) :
 (O.readRaw _ (rawAtNext root visit rec U7 calculus anchor sourceStage stage count f k)).expression.eval
  (O.readRaw _ (rawAtNext root visit rec U7 calculus anchor sourceStage stage count f k)).environment =
 effectEvaluator (R := ℤ) (AN.paid (packet (k+1)).2.1.1).environment (AN.paid (packet (k+1)).2.1.1).increment
  (relationMap (R := ℤ) (AN.paid (packet (k+1)).2.1.1).environment (N.relations (R := ℤ) (AN.paid (packet (k+1)).2.1.1))) :=
 (congrArg (fun raw => raw.expression.eval raw.environment)
  (raw_at_next_source root visit rec U7 calculus anchor sourceStage stage count f k)).trans
  (N.updated_value (R := ℤ) (AN.paid (packet (k+1)).2.1.1))

theorem actual_registered_handoff (k : Nat) :
 RegisteredFrom (baseFactory root visit rec) f (packet k) (packet (k+1)) :=
 (congrArg (RegisteredFrom (baseFactory root visit rec) f (packet k))
  (D.packetAt_successor method old cfg lang k)).mpr
  (registered_from_next (baseFactory root visit rec) f (packet k))

theorem actual_current_residual (k : Nat) :
 (SourceGeneratedScalarDifferentialResidual.residualEquivRange
  (evaluation (R := ℤ) (N.input (AN.paid (packet (k+1)).2.1.1)).environment)
  (SourceGeneratedScalarDifferentialResidual.canonicalResidual
   (evaluation (R := ℤ) (N.input (AN.paid (packet (k+1)).2.1.1)).environment)
   (relationMap (R := ℤ) (AN.paid (packet (k+1)).2.1.1).environment
    (N.relations (R := ℤ) (AN.paid (packet (k+1)).2.1.1))))).val =
 (O.readRaw _ (rawAtNext root visit rec U7 calculus anchor sourceStage stage count f k)).expression.eval
  (O.readRaw _ (rawAtNext root visit rec U7 calculus anchor sourceStage stage count f k)).environment :=
 (N.residual_value (R := ℤ) (AN.paid (packet (k+1)).2.1.1)).trans
  (congrArg (fun raw => raw.expression.eval raw.environment)
   (raw_at_next_source root visit rec U7 calculus anchor sourceStage stage count f k)).symm

theorem actual_same_next_root (k : Nat) :
 Canonical.currentAtStop method old cfg lang (k+1) =
 SO.current (AS.bornAfterNative (AS.nativeAfterAdmission method (packet k))).2.1.1
  (AS.bornAfterNative (AS.nativeAfterAdmission method (packet k))).2.2.1 :=
 (Canonical.actual_current method old cfg lang (k+1)).trans
  (congrArg (fun value => SO.current value.2.1.1 value.2.2.1)
   (D.packetAt_successor method old cfg lang k))

-- The old selected residual becomes the born registered input; the born current paid raw is the next residual.
def cofinal_current_paid_raw_method (k : Nat) :=
 let current := packet k
 let native := AS.nativeAfterAdmission method current
 let selected := H.selected native
 let installed := rawAtNext root visit rec U7 calculus anchor sourceStage stage count f k
 PProd.mk installed <|
 PProd.mk (raw_at_next_source root visit rec U7 calculus anchor sourceStage stage count f k) <|
 PProd.mk (actual_current_effect root visit rec U7 calculus anchor sourceStage stage count f k) <|
 PProd.mk (Canonical.whole_word method old cfg lang (k+1)
  (Finsupp.single (O.readRaw _ installed).expression (1 : ℤ))) <|
 PProd.mk (Canonical.whole_trace method old cfg lang (k+1)) <|
 PProd.mk (actual_current_residual root visit rec U7 calculus anchor sourceStage stage count f k) <|
 PProd.mk (actual_registered_handoff root visit rec U7 calculus anchor sourceStage stage count f k) <|
 PProd.mk (nativeFrameRestriction (baseFactory root visit rec) f current selected) <|
 PProd.mk (native_frame_source (baseFactory root visit rec) f current selected) <|
 PProd.mk (RE.paid_updated_environment selected) <|
 PProd.mk (RE.born_request_input selected native.2.2.1) <|
 PProd.mk (RE.born_actual_payment selected native.2.2.1) <|
 PProd.mk (RE.born_payment_entry selected native.2.2.1) <|
 PProd.mk (RE.born_payment_ledger selected native.2.2.1) <|
 PProd.mk (RE.born_payment_visit selected native.2.2.1) <|
 PProd.mk (RE.born_whole_receipt selected native.2.2.1) <|
 PProd.mk (RE.born_payment_whole_destination selected native.2.2.1) <|
 PProd.mk (noetherianPayment selected native.2.2.1) <|
 PProd.mk (actual_same_next_root root visit rec U7 calculus anchor sourceStage stage count f k) <|
 PProd.mk (H.after_native_value method current) <|
 PProd.mk (H.after_native_whole_action (enrich (baseFactory root visit rec)) f current) <|
 PProd.mk (H.actual_complete_query_written (enrich (baseFactory root visit rec)) f current) <|
 PProd.mk (H.actual_native_faces (enrich (baseFactory root visit rec)) f current) <|
 PProd.mk (Canonical.rawAtStop_read method old cfg lang (k+1)) <|
 PProd.mk (D.packetAt_successor method old cfg lang k) <|
 PProd.mk (D.actual_index method old cfg lang k) <|
 PProd.mk (D.actual_index method old cfg lang (k+1)) <|
 PProd.mk (SF.actual_whole method old cfg lang (D.index method old cfg lang k)) <|
 PProd.mk (SF.actual_next method old cfg lang (D.index method old cfg lang k)) <|
 PProd.mk (D.history_end_index method old cfg lang k)
 (D.historyAt method old cfg lang k)
end Root
end SourceFamilyCurrentPaidRawInstallation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
