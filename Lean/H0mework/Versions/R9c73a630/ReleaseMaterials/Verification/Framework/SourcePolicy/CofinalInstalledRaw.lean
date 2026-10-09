import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Consumer
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CofinalRawGate"
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalRawGate
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations
namespace C
export ActualCofinalInstalledRaw (packet currentAtStop actual_current rawAtStop rawAtStop_read materialAtStop materialAtStop_source requestAtStop installed_request installed_boundary installed_differential whole_trace whole_word installed_relation_inverse)
end C
variable {S : Type u} {W X : S → Type u} [∀ target, AddCommGroup (W target)] {s : S}
local instance gateGroups (grade : Nat) (target : S) : AddCommGroup (ActualCofinalInstalledRaw.L.Value W grade target) :=
 ActualCofinalInstalledRaw.L.groups W grade target
variable (factory : ActualCofinalInstalledRaw.SF.Factory W X s)
variable (frame : ActualCofinalInstalledRaw.M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : ActualCofinalInstalledRaw.A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)
example (ordinal : Nat) : type_of% (C.packet factory frame cfg language ordinal) := C.packet factory frame cfg language ordinal
example (ordinal : Nat) : type_of% (C.currentAtStop factory frame cfg language ordinal) := C.currentAtStop factory frame cfg language ordinal
example (ordinal : Nat) : type_of% (C.actual_current factory frame cfg language ordinal) := C.actual_current factory frame cfg language ordinal
example (ordinal : Nat) : type_of% (C.rawAtStop factory frame cfg language ordinal) := C.rawAtStop factory frame cfg language ordinal
example (ordinal : Nat) : type_of% (C.rawAtStop_read factory frame cfg language ordinal) := C.rawAtStop_read factory frame cfg language ordinal
example (ordinal : Nat) : type_of% (C.materialAtStop factory frame cfg language ordinal) := C.materialAtStop factory frame cfg language ordinal
example (ordinal : Nat) : type_of% (C.materialAtStop_source factory frame cfg language ordinal) := C.materialAtStop_source factory frame cfg language ordinal
example (ordinal : Nat) : type_of% (C.requestAtStop factory frame cfg language ordinal) := C.requestAtStop factory frame cfg language ordinal
example (ordinal : Nat) : type_of% (C.installed_request factory frame cfg language ordinal) := C.installed_request factory frame cfg language ordinal
example (ordinal : Nat) : type_of% (C.installed_boundary factory frame cfg language ordinal) := C.installed_boundary factory frame cfg language ordinal
example (ordinal : Nat) : type_of% (C.installed_differential factory frame cfg language ordinal) := C.installed_differential factory frame cfg language ordinal
example (ordinal : Nat) : type_of% (C.whole_trace factory frame cfg language ordinal) := C.whole_trace factory frame cfg language ordinal
example (ordinal : Nat) : type_of% (C.installed_relation_inverse factory frame cfg language ordinal) := C.installed_relation_inverse factory frame cfg language ordinal
example (ordinal : Nat) (word : Formal ℤ
 (ActualCofinalInstalledRaw.L.Value W (C.packet factory frame cfg language ordinal).1) X s) :
 type_of% (C.whole_word factory frame cfg language ordinal word) := C.whole_word factory frame cfg language ordinal word
example {Result : Sort v} (ordinal : Nat)
 (consume : (restriction : SourceOperationInquiry.Context.RawRestrictionAt
  (PhysicalValue := ActualCofinalInstalledRaw.L.Value W (C.packet factory frame cfg language ordinal).1)
  (PhysicalVar := X) (sort := s) (C.currentAtStop factory frame cfg language ordinal)) →
  (material : ActualCanonicalBornSource.MaterialAtCurrent
   (Value := ActualCofinalInstalledRaw.L.Value W (C.packet factory frame cfg language ordinal).1)
   (Var := X) (s := s) (C.currentAtStop factory frame cfg language ordinal)) →
  type_of% (C.materialAtStop_source factory frame cfg language ordinal) →
  type_of% (C.installed_request factory frame cfg language ordinal) →
  type_of% (C.installed_differential factory frame cfg language ordinal) →
  type_of% (C.installed_relation_inverse factory frame cfg language ordinal) → Result) : Result :=
 consume (C.rawAtStop factory frame cfg language ordinal) (C.materialAtStop factory frame cfg language ordinal)
  (C.materialAtStop_source factory frame cfg language ordinal)
  (C.installed_request factory frame cfg language ordinal)
  (C.installed_differential factory frame cfg language ordinal)
  (C.installed_relation_inverse factory frame cfg language ordinal)
#print axioms C.packet
#print axioms C.currentAtStop
#print axioms C.actual_current
#print axioms C.rawAtStop
#print axioms C.rawAtStop_read
#print axioms C.materialAtStop
#print axioms C.materialAtStop_source
#print axioms C.requestAtStop
#print axioms C.installed_request
#print axioms C.installed_boundary
#print axioms C.installed_differential
#print axioms C.whole_trace
#print axioms C.installed_relation_inverse
#print axioms C.whole_word
end CofinalRawGate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
