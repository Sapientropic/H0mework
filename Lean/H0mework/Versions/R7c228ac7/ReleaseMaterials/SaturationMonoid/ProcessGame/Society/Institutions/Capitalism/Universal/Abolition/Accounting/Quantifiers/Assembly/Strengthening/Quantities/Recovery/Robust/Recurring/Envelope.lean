import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Recurring.Domain

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Recurring

open Abolition.Root Abolition.Root.Registered

noncomputable section

universe u v

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Event : Type u} {Signal : Type v}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Policy" => Nat → Signal → Script
local notation "Exposure" => Nat → C → Event → Script
local notation "Observation" => Nat → C → Signal

inductive Minimum (source : C) (expose : Exposure) (observe : Observation)
  | noEvents (empty : IsEmpty Event)
  | attained (policy : Policy) (paid : PolicyPaid source expose observe policy)
      (exactValue : worst source expose observe policy = sInf (values source expose observe))
      (finite : worst source expose observe policy < ⊤)
  | approached (nonempty : (values source expose observe).Nonempty)
      (finite : sInf (values source expose observe) < ⊤)
      (strict : sInf (values source expose observe) ∉ values source expose observe)
      (near : ∀ limit, sInf (values source expose observe) < limit →
        ∃ policy, PolicyPaid source expose observe policy ∧ worst source expose observe policy < limit)
  | unbounded (nonempty : (values source expose observe).Nonempty)
      (each : ∀ policy, PolicyPaid source expose observe policy → ∀ limit < (⊤ : EReal),
        ∃ events stage, PaidAt source expose observe policy events stage ∧
          limit < ratioAt source expose observe policy events stage)
  | blocked (each : ∀ policy, Failure source expose observe policy)

/-- The original root settles every branch of one observation policy
selected before the first exposure, with no bound on the number of stages. -/
def resolve (source : C) (expose : Exposure) (observe : Observation) : Minimum source expose observe := by
  classical
  by_cases occurs : Nonempty Event
  · let domain := values source expose observe
    by_cases feasible : domain.Nonempty
    · by_cases infinite : sInf domain = ⊤
      · refine .unbounded feasible ?_
        intro policy paid limit finite
        have above := sInf_le (show worst source expose observe policy ∈ domain from ⟨policy, paid, rfl⟩)
        rw [infinite] at above
        have outside : limit < worst source expose observe policy := finite.trans_le above
        obtain ⟨events, later⟩ := lt_iSup_iff.mp outside
        obtain ⟨stage, exceeded⟩ := lt_iSup_iff.mp later
        exact ⟨events, stage, paid.restoration events stage, exceeded⟩
      · by_cases reached : sInf domain ∈ domain
        · have existsPolicy : ∃ policy, PolicyPaid source expose observe policy ∧
              worst source expose observe policy = sInf domain := reached
          let policy := Classical.choose existsPolicy
          have actual := Classical.choose_spec existsPolicy
          exact .attained policy actual.1 actual.2 (actual.2.symm ▸ lt_top_iff_ne_top.mpr infinite)
        · refine .approached feasible (lt_top_iff_ne_top.mpr infinite) reached ?_
          intro limit strict
          obtain ⟨value, ⟨policy, paid, same⟩, below⟩ := sInf_lt_iff.mp strict
          exact ⟨policy, paid, same ▸ below⟩
    · refine .blocked fun policy => (policy_fails_iff_an_actual_history_has_an_original_obstruction
        source expose observe policy).mp (fun paid => feasible ⟨_, policy, paid, rfl⟩)
  · exact .noEvents ⟨fun event => occurs ⟨event⟩⟩

theorem the_repeated_work_conversion_has_its_exact_lower_envelope
    (source : C) (expose : Exposure) (observe : Observation) :
    IsGLB (values source expose observe) (sInf (values source expose observe)) :=
  isGLB_sInf _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Recurring
