import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly.Functions
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Finite.Resolution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Registered Source.Program Source.ProgrammeControl

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

local notation "F" => Macro.Runtime.ActivatedFrame (review := review)
  input depth count prefixLimit renewalLimit sourceDepth sourceCount

/-- Only the existing material guard's law parameter is changed. This view
does not construct an Input root, occurrence, actor, account or history. -/
def controlView (state : F) := { input with law := state.interpreter }

def FreshControlAt (state : F) : Prop :=
  ¬ Material.NoFreshControl (controlView state) (sourceBody state).1 (sourceBody state).2

theorem open_guard (raw : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    Material.NoFreshControl (Macro.Public.Scope.checkInput input) raw word := by
  constructor
  · have empty : controlInventory (Macro.Public.Scope.checkInput input).law raw word
        (Material.localFamily (Macro.Public.Scope.checkInput input) raw word) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro use _present
      have families := Functions.open_interpretation_generated_families_empty input.law raw word input.localAttempts use.item
      have present := use.controlled
      change use.port ∈ Kernel.AssetAuthority.generatedFamily (PublicFunction.physicalLaw input.law)
        raw word input.localAttempts use.item ++
        Kernel.ActualSurplus.familyAt (PublicFunction.physicalLaw input.law) raw word use.item at present
      rw [families.1, families.2] at present
      exact List.not_mem_nil present
    rw [empty]
    rfl
  · intro item _listed port _required fresh
    obtain ⟨_accepted, _port, subject, _affected, phase⟩ := fresh
    exact Functions.open_interpretation_has_no_private_phase input.law item.before port subject phase

theorem an_actual_public_body_has_no_fresh_title_surplus_or_historical_control
    (state : F) (opened : state.isPublic = true) : ¬ FreshControlAt state := by
  cases state with
  | original current => cases opened
  | enacted origin admission current =>
      exact fun controlled => controlled (open_guard _ _)

theorem each_actual_title_or_surplus_control_is_covered
    (state : F)
    (item : OriginalItem (controlView state).law (sourceBody state).1 (sourceBody state).2)
    (accepted : (controlView state).law.Valid item.val.before item.val.request)
    (port : Port) (required : port ∈ (controlView state).law.requiredPorts item.val.before item.val.request)
    (controlled : port ∈ Material.localFamily (controlView state) (sourceBody state).1 (sourceBody state).2 item) :
    FreshControlAt state := by
  intro clear
  exact (empty_controlInventory_excludes_every_control _ _ _ _ (List.length_eq_zero_iff.mp clear.1)
    item accepted port required) controlled

theorem each_actual_historical_control_is_covered
    (state : F)
    (item : OriginalItem (controlView state).law (sourceBody state).1 (sourceBody state).2)
    (port : Port) (required : port ∈ (controlView state).law.requiredPorts item.val.before item.val.request)
    (controlled : History.FreshControl (controlView state) port item.val) : FreshControlAt state := by
  exact fun clear => clear.2 item.val item.property port required controlled

variable (input depth sourceDepth)
  (datum : Macro.Ingress.Datum input depth sourceDepth) (prefixLimit renewalLimit : Nat)
  (reader : Macro.Raw.Reader input depth (Macro.Ingress.cut input depth sourceDepth))
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "A" => Macro.Runtime.ActivatedFrame (review := review) input depth
  (Macro.Ingress.cut input depth sourceDepth) prefixLimit renewalLimit depth
  (Macro.Ingress.cut input depth sourceDepth)
local notation "current" => Macro.Runtime.actualFrame (review := review)
  input depth sourceDepth datum prefixLimit renewalLimit reader

def LegallyAbsorbingActualCapitalControl (tick : Nat) : Prop :=
  ∃ path : Nat → A, path 0 = current tick ∧
    (∀ step, path (step + 1) = (path step).next) ∧
    (∀ cutoff, ∃ step ≥ cutoff, FreshControlAt (path step)) ∧
    ∀ step, Finite.NoUnresolvedReview (path step)

theorem no_actual_source_form_can_obtain_a_legally_absorbing_capital_finality (tick : Nat) :
    ¬ LegallyAbsorbingActualCapitalControl input depth sourceDepth datum prefixLimit renewalLimit reader review tick := by
  rintro ⟨path, starts, legal, recurs, closed⟩
  obtain ⟨steps, _within, outcome⟩ := Finite.the_actual_source_forces_a_finite_public_tail_or_its_exact_obstruction
    input depth sourceDepth datum prefixLimit renewalLimit reader review tick
  rcases outcome with ⟨_opened, tail⟩ | blocked
  · obtain ⟨index, after, capital⟩ := recurs steps
    have actual := Finite.every_legal_continuation_is_the_original_actual_fold input depth sourceDepth datum
      prefixLimit renewalLimit reader review tick path starts legal index
    have opened := tail (index - steps)
    have same : tick + steps + (index - steps) = tick + index := by omega
    rw [same, ← actual] at opened
    exact an_actual_public_body_has_no_fresh_title_surplus_or_historical_control _ opened capital
  · have actual := Finite.every_legal_continuation_is_the_original_actual_fold input depth sourceDepth datum
      prefixLimit renewalLimit reader review tick path starts legal steps
    exact Finite.an_actual_obstruction_cannot_be_a_closed_review _ blocked (actual ▸ closed steps)

#print axioms an_actual_public_body_has_no_fresh_title_surplus_or_historical_control
#print axioms each_actual_title_or_surplus_control_is_covered
#print axioms each_actual_historical_control_is_covered
#print axioms no_actual_source_form_can_obtain_a_legally_absorbing_capital_finality

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly
