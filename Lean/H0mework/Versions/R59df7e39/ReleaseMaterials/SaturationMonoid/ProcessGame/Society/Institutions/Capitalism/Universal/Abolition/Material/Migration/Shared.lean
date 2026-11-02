import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Shared

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration

open Source.Program Source.ProgrammeControl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

/-- All necessary recipients and affected subjects are extracted from this
finite occurrence. The ambient Party type is never assumed finite. -/
def subjects (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : List Party :=
  (input.law.rawItems current word).flatMap (History.affectedSubjects input)

def FiniteShared (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ item ∈ input.law.rawItems current word,
    ∀ port ∈ input.law.requiredPorts item.before item.request,
      ∀ person ∈ subjects input current word, input.law.allowed item.before.technology port person = true

instance (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : Decidable (FiniteShared input current word) := by
  unfold FiniteShared
  infer_instance

omit [DecidableEq Port] in
theorem kernel_recipient_is_an_original_subject
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (capital : Kernel.CapitalRelationKernel input.law current word) :
    capital.proposal.access.recipient ∈ subjects input current word := by
  let access := capital.proposal.access
  have need := capital.checked.1.2.2.2.1
  change access.RequiredUsePaid input.law current word at need
  unfold Kernel.AccessProposal.RequiredUsePaid at need
  cases operation : access.necessity.val.request.operation with
  | use bearer goods purpose =>
      simp only [operation] at need
      obtain ⟨same, required, _valid, _positive⟩ := need
      apply List.mem_flatMap.mpr
      refine ⟨access.necessity.val, access.necessity.property, ?_⟩
      simp only [History.affectedSubjects, List.mem_dedup, List.mem_append]
      right
      simp only [operation, if_pos required]
      exact List.mem_singleton.mpr same.symm
  | _ => simp only [operation] at need

theorem finiteShared_noFreshControl
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (shared : FiniteShared input current word) : NoFreshControl input current word := by
  refine ⟨?_, ?_⟩
  · apply List.length_eq_zero_iff.mpr
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro use _present
    have classified := use.controlled
    simp only [localFamily, List.mem_append] at classified
    rcases classified with title | surplus
    · obtain ⟨capital, _, _, phase⟩ := Kernel.AssetAuthority.generatedFamily_original_provenance
        input.law current word input.localAttempts use.item use.port title
      have allowed := shared use.item.val use.item.property use.port use.required
        capital.dependency.proposal.access.recipient
        (kernel_recipient_is_an_original_subject input current word capital.dependency)
      exact Bool.noConfusion (allowed.symm.trans phase.2)
    · obtain ⟨capital, _, _, phase⟩ := Kernel.ActualSurplus.familyAt_has_original_witness
        input.law current word use.item use.port surplus
      have allowed := shared use.item.val use.item.property use.port use.required
        capital.dependency.proposal.access.recipient
        (kernel_recipient_is_an_original_subject input current word capital.dependency)
      exact Bool.noConfusion (allowed.symm.trans phase.2)
  · intro item present port required fresh
    obtain ⟨_, _, person, affected, phase⟩ := fresh
    have member : person ∈ subjects input current word := List.mem_flatMap.mpr ⟨item, present, affected⟩
    exact Bool.noConfusion ((shared item present port required person member).symm.trans phase.2)

omit [DecidableEq Port] in
theorem sharedPeriod_is_finitely_detected
    (current : RawCurrent Party Good Technology Instrument) (members : List Party)
    (word : RawEvent Party Good Port Technology Instrument)
    (shared : Continuation.SharedPeriod input current members word) : FiniteShared input current word :=
  fun item present port required person _member => shared.2.2.1 item present port required person

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration
