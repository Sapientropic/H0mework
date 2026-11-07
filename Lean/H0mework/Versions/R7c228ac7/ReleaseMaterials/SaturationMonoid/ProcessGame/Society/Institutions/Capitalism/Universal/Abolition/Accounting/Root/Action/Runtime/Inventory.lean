import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action.Installation
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Runtime
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

private def cofaceEquiv (A B : Type) : SourceNativeProjectionCoface A B ≃ A ⊕ B where
  toFun := fun value => match value with | .inherited a => .inl a | .component b => .inr b
  invFun := fun value => match value with | .inl a => .inherited a | .inr b => .component b
  left_inv := fun value => by cases value <;> rfl
  right_inv := fun value => by cases value <;> rfl

private def compilerProjectionEquiv : Compiler.Projection ≃ Fin 2 where
  toFun := fun value => match value with | .ledger => 0 | .current => 1
  invFun := Fin.cases .ledger (fun _ => .current)
  left_inv := fun value => by cases value <;> rfl
  right_inv := fun value => by fin_cases value <;> rfl

private def inputProjectionEquiv : Installation.Projection ≃ Fin 2 where
  toFun := fun value => match value with | .compilation => 0 | .input => 1
  invFun := Fin.cases .compilation (fun _ => .input)
  left_inv := fun value => by cases value <;> rfl
  right_inv := fun value => by fin_cases value <;> rfl

private def inquiryProjectionEquiv : Source.Inquiry.Projection ≃ Fin 7 where
  toFun := fun value => match value with
    | .answer => 0 | .input => 1 | .assessment => 2 | .verdict => 3
    | .needs => 4 | .consumer => 5 | .compilation => 6
  invFun := Fin.cases .answer (Fin.cases .input (Fin.cases .assessment
    (Fin.cases .verdict (Fin.cases .needs (Fin.cases .consumer (fun _ => .compilation))))))
  left_inv := fun value => by cases value <;> rfl
  right_inv := fun value => by fin_cases value <;> rfl

local instance : Finite Installation.Projection := Finite.of_equiv (Fin 2) inputProjectionEquiv.symm
local instance : Finite Compiler.Projection := Finite.of_equiv (Fin 2) compilerProjectionEquiv.symm
local instance : Finite Source.Inquiry.Projection := Finite.of_equiv (Fin 7) inquiryProjectionEquiv.symm
local instance {A B : Type} [Finite A] [Finite B] : Finite (SourceNativeProjectionCoface A B) := by
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  exact Finite.of_equiv (A ⊕ B) (cofaceEquiv A B).symm

private theorem coface_card (A B : Type) [Finite A] [Finite B] :
    Nat.card (SourceNativeProjectionCoface A B) = Nat.card A + Nat.card B :=
  (Nat.card_congr (cofaceEquiv A B)).trans Nat.card_sum

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.NativeFrame input)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (origin : Source.OriginAt input frame visit claim)
  (word : RawEvent Party Good Port Technology Instrument)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (Source.sourceEntry input frame visit))
  [Finite frame.root.toAuthoritativeRoot.source.projectionLaw.Projection]

def source := Installation.presentation input frame visit claim origin word authority

def target (n : Nat) := Source.Inquiry.presentationAt input (Installation.native input frame visit claim word) visit claim word n

def projectionCard (current : AnyAuthoritativeRootCurrent) : Nat :=
  Nat.card current.current.root.source.projectionLaw.Projection

theorem source_projection_card : projectionCard (source input frame visit claim origin word authority).erase =
    Nat.card frame.root.toAuthoritativeRoot.source.projectionLaw.Projection + 2 := by
  change Nat.card (SourceNativeProjectionCoface frame.root.toAuthoritativeRoot.source.projectionLaw.Projection Installation.Projection) = _
  rw [coface_card,(Nat.card_congr inputProjectionEquiv).trans (Nat.card_fin 2)]

theorem target_projection_card (n : Nat) : projectionCard (target input frame visit claim word n).erase =
    Nat.card frame.root.toAuthoritativeRoot.source.projectionLaw.Projection + 11 := by
  change Nat.card (SourceNativeProjectionCoface
    (SourceNativeProjectionCoface Compiler.Projection
      (SourceNativeProjectionCoface frame.root.toAuthoritativeRoot.source.projectionLaw.Projection Installation.Projection))
    Source.Inquiry.Projection) = _
  rw [coface_card,coface_card,coface_card,(Nat.card_congr inputProjectionEquiv).trans (Nat.card_fin 2),
    (Nat.card_congr compilerProjectionEquiv).trans (Nat.card_fin 2),
    (Nat.card_congr inquiryProjectionEquiv).trans (Nat.card_fin 7)]
  omega

theorem source_ne_target (n : Nat) : (source input frame visit claim origin word authority).erase ≠
    (target input frame visit claim word n).erase := by
  intro same
  have cards := congrArg projectionCard same
  rw [source_projection_card,target_projection_card] at cards
  omega

#print axioms source_ne_target

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action.Runtime
