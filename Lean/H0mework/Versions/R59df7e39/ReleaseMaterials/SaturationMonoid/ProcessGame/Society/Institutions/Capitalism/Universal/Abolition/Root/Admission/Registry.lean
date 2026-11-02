import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission.Successor
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat) (datum : Datum input (frame input depth count))

private def sourceProjectionEquiv : Projection ≃ Fin 4 where
  toFun := fun projection => match projection with
    | .input => 0 | .attempt => 1 | .compilation => 2 | .consumer => 3
  invFun := fun index => Fin.cases .input (Fin.cases .attempt (Fin.cases .compilation (fun _ => .consumer))) index
  left_inv := fun projection => by cases projection <;> rfl
  right_inv := fun index => by fin_cases index <;> rfl

private def targetProjectionEquiv : Continuation.Projection ≃ Fin 5 where
  toFun := fun projection => match projection with
    | .ledger => 0 | .execution => 1 | .account => 2 | .pending => 3 | .originalHistory => 4
  invFun := fun index => Fin.cases .ledger (Fin.cases .execution (Fin.cases .account
    (Fin.cases .pending (fun _ => .originalHistory)))) index
  left_inv := fun projection => by cases projection <;> rfl
  right_inv := fun index => by fin_cases index <;> rfl

private def cofaceEquiv (A B : Type) : (A ⊕ B) ≃ SourceNativeProjectionCoface A B where
  toFun := fun value => match value with
    | .inl inherited => .inherited inherited
    | .inr component => .component component
  invFun := fun value => match value with
    | .inherited inherited => .inl inherited
    | .component component => .inr component
  left_inv := fun value => by cases value <;> rfl
  right_inv := fun value => by cases value <;> rfl

theorem source_projection_lower :
    6 ≤ Financial.Installation.Runtime.erasedProjectionCard (presentation input depth count datum).erase := by
  have oldFinite : Finite (frame input depth count).native.root.toAuthoritativeRoot.source.projectionLaw.Projection :=
    (frame input depth count).projectionFinite
  have componentFinite : Finite Projection := Finite.of_equiv (Fin 4) sourceProjectionEquiv.symm
  let : Fintype (frame input depth count).native.root.toAuthoritativeRoot.source.projectionLaw.Projection := Fintype.ofFinite _
  let : Fintype Projection := Fintype.ofFinite _
  have cofaceFinite : Finite (SourceNativeProjectionCoface
      (frame input depth count).native.root.toAuthoritativeRoot.source.projectionLaw.Projection Projection) :=
    Finite.of_equiv _ (cofaceEquiv _ _)
  change 6 ≤ Nat.card (SourceNativeProjectionCoface
    (frame input depth count).native.root.toAuthoritativeRoot.source.projectionLaw.Projection Projection)
  exact (frame input depth count).projectionLarge.trans
    (Nat.card_le_card_of_injective SourceNativeProjectionCoface.inherited
      (by intro left right same; cases same; rfl))

theorem target_projection_card :
    Financial.Installation.Runtime.erasedProjectionCard (targetPresentation input depth count datum).erase = 5 :=
  (Nat.card_congr targetProjectionEquiv).trans (Nat.card_fin 5)

theorem source_and_target_are_distinct :
    (presentation input depth count datum).erase ≠ (targetPresentation input depth count datum).erase := by
  intro same
  have cards := congrArg Financial.Installation.Runtime.erasedProjectionCard same
  have lower := source_projection_lower input depth count datum
  have target := target_projection_card input depth count datum
  omega

def node : Bool → RootInquiryProcessNode
  | false => .active (presentation input depth count datum)
  | true => .active (targetPresentation input depth count datum)

/-- A finite admission epoch.  The target is active and literal; the
enclosing decision source must supply its next review query. -/
def process : SourceNativeInquiryEngineProcess where
  State := Bool
  stateAt := node input depth count datum
  erase_injective := by
    intro left right leftState rightState leftActive rightActive same
    cases left <;> cases right
    · rfl
    · cases leftActive
      cases rightActive
      exact False.elim (source_and_target_are_distinct input depth count datum same)
    · cases leftActive
      cases rightActive
      exact False.elim (source_and_target_are_distinct input depth count datum same.symm)
    · rfl
  initial := false
  successorAt := by
    intro index query
    cases index with
    | false => exact ⟨true, actual_successor_valid input depth count datum query⟩
    | true => exact query.elim

def seededEngine := Engine.initial (process input depth count datum)

def sourceInput : Engine.SourceNativeInquiryRegisteredInputAt (seededEngine input depth count datum) :=
  registeredInput input (frame input depth count) datum

def activation := (seededEngine input depth count datum).registeredInquiryActivation
  (sourceInput input depth count datum)

def ask := (seededEngine input depth count datum).ask (activation input depth count datum)

theorem activation_keeps_registered_source :
    (activation input depth count datum).registeredInput? = some (sourceInput input depth count datum) := rfl

theorem actual_registered_action_is_consumed :
    (ask input depth count datum).resolution = .actualAction (generated input depth count datum) := rfl

theorem actual_answer_is_source_attempt :
    (ask input depth count datum).answer = result input depth count datum := rfl

theorem actual_next_is_literal_active_target :
    (ask input depth count datum).next.node = .active (targetPresentation input depth count datum) := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission
