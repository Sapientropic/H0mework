import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

structure Unresolved (support : Support (genesisRaw input) (genesisCarried input)) where
  private mk ::
  first : Address Instrument Party
  rest : List (Address Instrument Party)
  report : discrepancies support = first :: rest

theorem Unresolved.original_key
    {support : Support (genesisRaw input) (genesisCarried input)}
    (refusal : Unresolved input support) (key : Address Instrument Party) :
    key ∈ refusal.first :: refusal.rest ↔ input.initial.claims key.instrument key.debtor key.holder ≠ 0 := by
  rw [← refusal.report, discrepancies_exact]
  rfl

variable (depth start : Nat)

structure Accepted where
  private mk ::
  originalGenesis : input.initial.claims = fun _ _ _ => 0
  exactOpening : rawAtCut input depth start = carriedAtCut input depth start

inductive Outcome (support : Support (genesisRaw input) (genesisCarried input))
  | accepted (opening : Accepted input depth start)
  | unresolved (refusal : Unresolved input support)

/-- The original genesis check is prior to opening an actual cut. A later
balance equality cannot authorize an unsupported old genesis claim. -/
def openAt (support : Support (genesisRaw input) (genesisCarried input)) :
    Outcome input depth start support :=
  match inspect support with
  | .accepted matching =>
    let original := (genesis_matches_iff input).1 matching
    .accepted ⟨original, nativeCut_recovers_all_original_claims input depth start original⟩
  | .refused first rest report => .unresolved ⟨first, rest, report⟩

theorem openAt_accepts_iff (support : Support (genesisRaw input) (genesisCarried input)) :
    (∃ accepted, openAt input depth start support = .accepted accepted) ↔
      input.initial.claims = fun _ _ _ => 0 := by
  constructor
  · rintro ⟨accepted, _⟩
    exact accepted.originalGenesis
  · intro original
    obtain ⟨proof, selected⟩ := (accepted_iff support).2 ((genesis_matches_iff input).2 original)
    refine ⟨⟨original, nativeCut_recovers_all_original_claims input depth start original⟩, ?_⟩
    unfold openAt
    rw [selected]

def Accepted.inherited (_accepted : Accepted input depth start) :
    (Epoch.Finance.process input depth (cut input depth start)).GeneratedState :=
  Opening.inherited input depth start

theorem Accepted.inherited_eq (_accepted : Accepted input depth start) :
    _accepted.inherited input depth start =
      Epoch.Finance.Legacy.generated input depth (cut input depth start) (originalAccount input depth start) :=
  inherited_is_the_original_run input depth start

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening
