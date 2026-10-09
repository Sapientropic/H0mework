import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Source
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "ActualCofinalInstalledRaw"

/-! The original relation/cochain and full literal-word consumers use the
installed raw at each actual admission, with that admission's complete native
material. The complete runtime word and all between-stop receipts remain
owned by the original source-generated admission history. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalInstalledRaw
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarPresentation
namespace F
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace
 (boundary source_boundary actualRelation complex generated_differential wholeFaces whole_paid_trace
  relation_recovery whole_recovery)
end F
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance consumerGroups (grade : Nat) (target : Sorts) :
 AddCommGroup (L.Value W grade target) := L.groups W grade target
variable (factory : SF.Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)
attribute [local irreducible] currentAtStop

/-- Installed coordinates agree with the same-occurrence request, including its retained owner. -/
theorem installed_request (ordinal : Nat) :
 (O.readRaw _ (rawAtStop factory initial cfg language ordinal)).environment =
  (requestAtStop factory initial cfg language ordinal).environment ∧
 (O.readRaw _ (rawAtStop factory initial cfg language ordinal)).expression =
  (requestAtStop factory initial cfg language ordinal).expression := by
 have raw := (rawAtStop_read factory initial cfg language ordinal).trans
  (ActualInstalledNativeRaw.raw_registered (packet factory initial cfg language ordinal).2.1.1)
 have source := materialAtStop_source factory initial cfg language ordinal
 exact ⟨(congrArg (fun input => input.environment) raw).trans source.1.symm,
  (congrArg (fun input => input.expression) raw).trans source.2.1.symm⟩

/-- The actual source relation uses the installed AST and the complete paid endpoint. -/
theorem installed_boundary (ordinal : Nat) :
 F.boundary (materialAtStop factory initial cfg language ordinal) =
 Finsupp.single (O.readRaw _ (rawAtStop factory initial cfg language ordinal)).expression 1 -
  Finsupp.single (materialAtStop factory initial cfg language ordinal).state.1 1 :=
 (F.source_boundary (materialAtStop factory initial cfg language ordinal)).trans
  (congrArg (fun expression => Finsupp.single expression (1 : ℤ) -
   Finsupp.single (materialAtStop factory initial cfg language ordinal).state.1 1)
   (installed_request factory initial cfg language ordinal).2).symm

/-- The original cochain differential consumes the actual installed relation. -/
theorem installed_differential (ordinal : Nat) :
 (((F.complex (materialAtStop factory initial cfg language ordinal)).d 0 1).hom
  (F.actualRelation (materialAtStop factory initial cfg language ordinal))).val =
 Finsupp.single (O.readRaw _ (rawAtStop factory initial cfg language ordinal)).expression 1 -
  Finsupp.single (materialAtStop factory initial cfg language ordinal).state.1 1 :=
 (F.generated_differential (materialAtStop factory initial cfg language ordinal)).trans
  (installed_boundary factory initial cfg language ordinal)

/-- The full material Trace is the combinatorial face; no scalar quotient discards its positions. -/
theorem whole_trace (ordinal : Nat) :
 (F.wholeFaces (materialAtStop factory initial cfg language ordinal)).combinatorialFace.root.2.1 =
 (materialAtStop factory initial cfg language ordinal).state.2 :=
 F.whole_paid_trace (materialAtStop factory initial cfg language ordinal)

/-- Every complete coefficient word is recovered by the original literal-word duality. -/
theorem whole_word (ordinal : Nat)
 (word : Formal ℤ (L.Value W (packet factory initial cfg language ordinal).1) X s) :
 SourceGeneratedCompleteWordDual.coimageRecovery
  ((F.wholeFaces (materialAtStop factory initial cfg language ordinal)).canonical word) = word :=
 F.whole_recovery (materialAtStop factory initial cfg language ordinal) word

/-- In particular, the full inverse recovers the installed source relation word. -/
theorem installed_relation_inverse (ordinal : Nat) :
 SourceGeneratedCompleteWordDual.coimageRecovery
  ((F.wholeFaces (materialAtStop factory initial cfg language ordinal)).canonical
   (F.boundary (materialAtStop factory initial cfg language ordinal))) =
 Finsupp.single (O.readRaw _ (rawAtStop factory initial cfg language ordinal)).expression 1 -
  Finsupp.single (materialAtStop factory initial cfg language ordinal).state.1 1 :=
 (F.relation_recovery (materialAtStop factory initial cfg language ordinal)).trans
  (installed_boundary factory initial cfg language ordinal)

end ActualCofinalInstalledRaw
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
