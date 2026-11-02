import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.State
import Mathlib.Data.List.Forall2

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Coupling.State

open Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)
  (input other : ProgrammeSource.Input Party Good Port Technology Instrument)

structure OriginPair (old : Financial.InstructionOrigin input) (new : Financial.InstructionOrigin other) : Prop where
  origin : Identity.originImage code other new = Identity.originImage code input old
  decoded : new.instruction? other = old.instruction? input
  issues : Causality.issuedImage code other new = Causality.issuedImage code input old

omit [DecidableEq Technology] in
theorem consume_origins_natural (law : other.law = input.law) (initial : other.initial = input.initial)
    (oldOrigins : List (Financial.InstructionOrigin input)) (newOrigins : List (Financial.InstructionOrigin other))
    (paired : List.Forall₂ (OriginPair code input other) oldOrigins newOrigins)
    (old : (Financial.process input).GeneratedState) (new : (Financial.process other).GeneratedState)
    (matched : Match code input other old new) :
    Match code input other (Financial.consumeOrigins input oldOrigins old) (Financial.consumeOrigins other newOrigins new) := by
  induction paired generalizing old new with
  | nil => exact matched
  | @cons oldOrigin newOrigin oldOrigins newOrigins pair paired ih =>
    exact ih _ _ (consume_natural code input other law initial oldOrigin newOrigin pair.origin pair.decoded pair.issues old new matched)

omit [DecidableEq Technology] in
theorem administrative_consumption_idle
    (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot)
    (emit : RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument)
    (generated : input.emission? = some emit) (before : (Financial.process input).GeneratedState) :
    Financial.consumeOrigins input (Financial.administrativeInventoryAt input visit) before = before := by
  have each : ∀ origin ∈ Financial.administrativeInventoryAt input visit, origin.instruction? input = none := by
    intro origin member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact Institutions.Capitalism.Universal.Source.ProgrammeFace.Registered.originalInstruction_generated_none input
      ((Financial.originAt input visit index).event input) (Financial.originAt input visit index).item emit generated
  generalize Financial.administrativeInventoryAt input visit = origins at each ⊢
  induction origins generalizing before with
  | nil => rfl
  | cons origin tail ih =>
    rw [Financial.consumeOrigins, Financial.BalanceConservation.consume_without_instruction input origin before (each origin (by simp))]
    exact ih before (fun entry member => each entry (by simp [member]))

omit [DecidableEq Technology] in
theorem account_at_natural (law : other.law = input.law) (initial : other.initial = input.initial)
    (oldEmit newEmit : RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument)
    (oldGenerated : input.emission? = some oldEmit) (newGenerated : other.emission? = some newEmit)
    (limit : Nat)
    (pairs : ∀ ordinal, ordinal < limit → List.Forall₂ (OriginPair code input other)
      (Financial.traceInventoryAt input (ProgrammeHistory.visitAt input ordinal))
      (Financial.traceInventoryAt other (ProgrammeHistory.visitAt other ordinal))) :
    ∀ ordinal, ordinal ≤ limit → Match code input other (Financial.accountAt input ordinal) (Financial.accountAt other ordinal) := by
  intro ordinal bounded
  induction ordinal with
  | zero => exact ⟨rfl, rfl⟩
  | succ ordinal ih =>
    have prior := ih (by omega)
    have step := consume_origins_natural code input other law initial _ _ (pairs ordinal (by omega)) _ _ prior
    rw [Financial.accountAt_successor, Financial.accountAt_successor]
    simp only [Financial.inventoryAt, oldGenerated, newGenerated, Financial.consumeOrigins_append,
      administrative_consumption_idle input _ oldEmit oldGenerated,
      administrative_consumption_idle other _ newEmit newGenerated]
    exact step

variable (source : Machine Party Good Port Technology Instrument) (cut : Nat) (policy : source.code.Policy)

theorem prior_trace_pairs (ordinal : Nat) (bounded : ordinal < source.history.length + 2 + cut) :
    List.Forall₂ (OriginPair source.code source.input (source.atFeedbackCut cut policy).input)
      (Financial.traceInventoryAt source.input (ProgrammeHistory.visitAt source.input ordinal))
      (Financial.traceInventoryAt (source.atFeedbackCut cut policy).input
        (ProgrammeHistory.visitAt (source.atFeedbackCut cut policy).input ordinal)) := by
  apply List.forall₂_of_length_eq_of_get
  · simp only [Financial.traceInventoryAt, List.length_ofFn]
    exact (congrArg List.length (source.scheduled_policy_keeps_every_prior_instruction_trace cut policy ordinal bounded)).symm
  · intro index oldBound newBound
    simp only [Financial.traceInventoryAt, List.get_eq_getElem, List.getElem_ofFn]
    let originalIndex : Fin (Institutions.Capitalism.Universal.Source.ProgrammeFace.Registered.traceItems source.input
        (ProgrammeHistory.visitAt source.input ordinal).current).length := ⟨index, by simpa only [Financial.traceInventoryAt, List.length_ofFn] using oldBound⟩
    exact ⟨Causality.prior_trace_origin_image source cut policy ordinal bounded originalIndex,
      Causality.prior_trace_origin_decodes_the_same_instruction source cut policy ordinal bounded originalIndex,
      Causality.prior_trace_issue_image source cut policy ordinal bounded originalIndex⟩

theorem every_prior_account_is_financially_coupled (ordinal : Nat) (bounded : ordinal ≤ source.history.length + 2 + cut) :
    Match source.code source.input (source.atFeedbackCut cut policy).input
      (Financial.accountAt source.input ordinal) (Financial.accountAt (source.atFeedbackCut cut policy).input ordinal) := by
  exact account_at_natural source.code source.input (source.atFeedbackCut cut policy).input rfl rfl
    source.body (source.atFeedbackCut cut policy).body rfl rfl (source.history.length + 2 + cut)
    (prior_trace_pairs source cut policy) ordinal bounded

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Coupling.State
