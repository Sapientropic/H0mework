import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Runtime
import Mathlib.Order.Filter.AtTopBot.Tendsto

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects
namespace Lower.SourceFamily.Admissions
namespace AS
export ActivationSource (AdmissionPacket nextAdmissionAt admissionDistance admissionPoint admissionPresentation
 nextAdmission_full admissionSegment localNativeReceipt localPaidAt nativePresentation
 bornAfterNative nativeAfterAdmission nativeAfterAdmission_grade admissionPoint_successor)
end AS
variable {S : Type u} {W X : S → Type u} [∀ target,AddCommGroup (W target)] {s : S}
local instance familyGroups (n : Nat) (target : S) : AddCommGroup (Lower.Value W n target) :=
 Lower.groups W n target
variable (factory : Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

abbrev sourceRuntime := runtime factory initial cfg language
abbrev receipt (start : Nat) := AS.nextAdmissionAt factory initial cfg language start
abbrev distance (start : Nat) := AS.admissionDistance factory initial cfg language start
abbrev packet (start : Nat) := AS.admissionPoint factory initial cfg language start

def history (start : Nat) := SourceNativeInquiryRuntime.runFrom
 (runtime := sourceRuntime factory initial cfg language) (distance factory initial cfg language start)
 ((sourceRuntime factory initial cfg language).stateAt start)

def tickReceipts (start : Nat) (offset : Fin (distance factory initial cfg language start)) :=
 actual_branch_receipt factory initial cfg language (start+offset.val)

theorem actual_admission (start : Nat) :
 ((sourceRuntime factory initial cfg language).stateAt (start+distance factory initial cfg language start)).engine.node =
 .active (AS.admissionPresentation factory (packet factory initial cfg language start)) :=
 (actual_node factory initial cfg language _).trans
  (congrArg RootInquiryProcessNode.active (AS.nextAdmission_full factory initial cfg language start))

attribute [local irreducible] ActivationSource.nextAdmissionAt ActivationSource.admissionSegment

def actual_segment (start : Nat) :
 PLift (distance factory initial cfg language start = 0) ⊕
 Σ native : AS.AdmissionPacket (W := W) (X := X) (s := s),
  PLift (distance factory initial cfg language start = (AS.localNativeReceipt native).1+1) ×
  ((offset : Fin (AS.localNativeReceipt native).1) → type_of% (AS.localPaidAt native offset)) ×
  PLift (∀ offset,offset ≤ (AS.localNativeReceipt native).1 →
   ((sourceRuntime factory initial cfg language).stateAt (start+offset)).engine.node =
    .active (AS.nativePresentation native offset)) := by
 refine Sum.map id (fun native => ?_) (AS.admissionSegment factory initial cfg language start)
 exact ⟨native.1,native.2.1,native.2.2.1,⟨fun offset within =>
  (actual_node factory initial cfg language (start+offset)).trans
   (congrArg RootInquiryProcessNode.active (native.2.2.2.down offset within))⟩⟩

theorem history_whole (start offset : Nat) : type_of%
 (actual_whole factory initial cfg language (start+offset)) :=
 actual_whole factory initial cfg language (start+offset)

/-- Every subsequent stop starts strictly after the previous source admission. -/
def index : Nat → Nat
 | 0 => distance factory initial cfg language 0
 | ordinal+1 => index ordinal+1+distance factory initial cfg language (index ordinal+1)

def startAt : Nat → Nat
 | 0 => 0
 | ordinal+1 => index factory initial cfg language ordinal+1

theorem index_eq_stop (ordinal : Nat) : index factory initial cfg language ordinal =
 startAt factory initial cfg language ordinal+
  distance factory initial cfg language (startAt factory initial cfg language ordinal) := by
 cases ordinal with
 | zero => exact (Nat.zero_add _).symm
 | succ ordinal => rfl

theorem strictMono : StrictMono (index factory initial cfg language) := by
 apply strictMono_nat_of_lt_succ
 intro ordinal
 change index factory initial cfg language ordinal <
  index factory initial cfg language ordinal+1+distance factory initial cfg language _
 omega

theorem ordinal_le_index (ordinal : Nat) : ordinal ≤ index factory initial cfg language ordinal := by
 induction ordinal with
 | zero => exact Nat.zero_le _
 | succ ordinal previous =>
  exact Nat.le_trans (Nat.succ_le_succ previous)
   (Nat.succ_le_of_lt (strictMono factory initial cfg language (Nat.lt_succ_self ordinal)))

def cover (bound : Nat) : Σ ordinal : Nat,PLift (bound ≤ index factory initial cfg language ordinal) :=
 ⟨bound,⟨ordinal_le_index factory initial cfg language bound⟩⟩

theorem cofinal : Filter.Tendsto (index factory initial cfg language) Filter.atTop Filter.atTop :=
 (strictMono factory initial cfg language).tendsto_atTop

abbrev packetAt (ordinal : Nat) := packet factory initial cfg language (startAt factory initial cfg language ordinal)

theorem actual_index (ordinal : Nat) :
 ((sourceRuntime factory initial cfg language).stateAt (index factory initial cfg language ordinal)).engine.node =
 .active (AS.admissionPresentation factory (packetAt factory initial cfg language ordinal)) := by
 rw [index_eq_stop]
 exact actual_admission factory initial cfg language _

/-- This history includes the admission tick and every following paid/settled tick. -/
def historyAt (ordinal : Nat) := SourceNativeInquiryRuntime.runFrom
 (runtime := sourceRuntime factory initial cfg language)
 (1+distance factory initial cfg language (index factory initial cfg language ordinal+1))
 ((sourceRuntime factory initial cfg language).stateAt (index factory initial cfg language ordinal))

theorem history_end_index (ordinal : Nat) : index factory initial cfg language ordinal+
 (1+distance factory initial cfg language (index factory initial cfg language ordinal+1)) =
 index factory initial cfg language (ordinal+1) := by
 change _ = index factory initial cfg language ordinal+1+distance factory initial cfg language _
 exact (Nat.add_assoc _ _ _).symm

theorem complete_word (ordinal : Nat) : type_of% (SourceOperationInquiry.word_point
 (sourceRuntime factory initial cfg language)
 ((sourceRuntime factory initial cfg language).stateAt (index factory initial cfg language ordinal))) :=
 SourceOperationInquiry.word_point _ _

theorem word_action (tick : Nat) : type_of% (SourceOperationInquiry.word_action
 (sourceRuntime factory initial cfg language) (SourceOperationInquiry.fieldPoint
  (sourceRuntime factory initial cfg language) ((sourceRuntime factory initial cfg language).stateAt tick))) :=
 SourceOperationInquiry.word_action _ _

theorem actual_source_action (tick : Nat) : type_of% (SourceOperationInquiry.actual_point_action
 (sourceRuntime factory initial cfg language) tick) := SourceOperationInquiry.actual_point_action _ _


/-- Original consecutive cofinal stops are the full source receiver--receipt--birth packet. -/
theorem packetAt_successor (ordinal : Nat) :
 packetAt factory initial cfg language (ordinal+1) =
 AS.bornAfterNative (AS.nativeAfterAdmission factory (packetAt factory initial cfg language ordinal)) := by
 change AS.admissionPoint factory initial cfg language (index factory initial cfg language ordinal+1) = _
 exact (congrArg (fun stop => AS.admissionPoint factory initial cfg language (stop+1))
  (index_eq_stop factory initial cfg language ordinal)).trans
   (AS.admissionPoint_successor factory initial cfg language (startAt factory initial cfg language ordinal))

theorem packetAt_successor_grade (ordinal : Nat) :
 (packetAt factory initial cfg language (ordinal+1)).1 =
 (packetAt factory initial cfg language ordinal).1+1 :=
 (congrArg Sigma.fst (packetAt_successor factory initial cfg language ordinal)).trans
  (AS.nativeAfterAdmission_grade factory _)


end Lower.SourceFamily.Admissions
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
