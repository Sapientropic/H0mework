import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Root
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Unbounded
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Menu.Unbounded

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal

open Capitalism.Universal.Source.Program
open Reparation.Actual (ReceiptAnswers Script)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

variable (loss : Reparation.Actual.Occurrence seed community)

def registeredMenus : Runtime.Menus Party Good Port Technology Instrument :=
  fun _ current => Supply.generatedMenu seed.native.input (originalRaw loss) current (originalBearers loss)

variable (answers : ReceiptAnswers seed) (payments : List (Script Party Good Port Technology Instrument))

/-- The original alphabet is searched anew at the actual current. No
fixed length cap, payment witness, or future supply policy is supplied. -/
def compileRegistered :=
  compile loss answers payments (registeredMenus loss)

theorem a_failed_registered_visit_refutes_all_finite_original_service_words
    (visit : Nat)
    (failure : Runtime.FaultAt (Occurrence.choose answers loss payments).state
      seed.native.input (originalRaw loss) (originalBearers loss) (registeredMenus loss) visit) :
    let selected := Occurrence.choose answers loss payments
    let actual := Runtime.eventAt selected.state seed.native.input
      (originalRaw loss) (originalBearers loss) (registeredMenus loss) visit
    (¬ ∃ word, Supply.Registered seed.native.input actual.before.raw word ∧
      Supply.Period seed.native.input (originalRaw loss) actual.before.raw (originalBearers loss) word) ∨
      ∃ person ∈ originalBearers loss,
        ¬ ∃ word, Supply.Registered seed.native.input actual.before.raw word ∧
          Supply.Period seed.native.input (originalRaw loss) actual.before.raw [person] word := by
  let selected := Occurrence.choose answers loss payments
  let actual := Runtime.eventAt selected.state seed.native.input
    (originalRaw loss) (originalBearers loss) (registeredMenus loss) visit
  have offered : actual.offers = Supply.generatedMenu seed.native.input (originalRaw loss)
      actual.before.raw (originalBearers loss) :=
    Runtime.the_original_root_records_each_new_menu _ _ _ _ _ _
  have refused := Runtime.the_missing_personal_exit_names_the_original_bearer selected.state
    seed.native.input (originalRaw loss) (originalBearers loss) (registeredMenus loss) visit failure
  change (∀ word ∈ actual.offers, ¬ Supply.Period seed.native.input
    (originalRaw loss) actual.before.raw (originalBearers loss) word) ∨
    (∃ person ∈ originalBearers loss, ∀ word ∈ actual.offers,
      ¬ Supply.Period seed.native.input (originalRaw loss) actual.before.raw [person] word) at refused
  rcases refused with together | ⟨person, onRoster, alone⟩
  · refine Or.inl fun witness => ?_
    obtain ⟨word, listed, paid⟩ :=
      (Supply.generated_menu_contains_an_actual_period_iff seed.native.input (originalRaw loss) actual.before.raw
        (originalBearers loss) (originalBearers loss) (Or.inl rfl)).mpr witness
    exact together word (offered.symm ▸ listed) paid
  · refine Or.inr ⟨person, onRoster, fun witness => ?_⟩
    obtain ⟨word, listed, paid⟩ :=
      (Supply.generated_menu_contains_an_actual_period_iff seed.native.input (originalRaw loss) actual.before.raw
        (originalBearers loss) [person] (Or.inr ⟨person, onRoster, rfl⟩)).mpr witness
    exact alone word (offered.symm ▸ listed) paid

variable (registered : Script Party Good Port Technology Instrument → Prop)

/-- After an actual attainment or a requested precision payment, the
living compiler starts at the reached ledger, including any remainder. -/
private def continueAfter (word : Script Party Good Port Technology Instrument) :=
  Runtime.classify (Occurrence.reached answers loss word)
    seed.native.input (originalRaw loss) (originalBearers loss) (registeredMenus loss)

inductive ReparationFrontier where
  | attained (word : Script Party Good Port Technology Instrument)
      (permitted : Occurrence.Unbounded.Allowed answers loss registered word)
      (minimum : Occurrence.Unbounded.value answers loss word = Occurrence.Unbounded.infimum answers loss registered)
      (continuation : Runtime.Outcome (Occurrence.reached answers loss word) seed.native.input
        (originalRaw loss) (originalBearers loss) (registeredMenus loss))
  | approached (unattained : Occurrence.Unbounded.infimum answers loss registered ∉
      Occurrence.Unbounded.values answers loss registered)
      (continuation : ∀ epsilon : ℝ, 0 < epsilon →
        (word : {word : Script Party Good Port Technology Instrument //
          Occurrence.Unbounded.Allowed answers loss registered word ∧
          Occurrence.Unbounded.infimum answers loss registered < Occurrence.Unbounded.value answers loss word ∧
          Occurrence.Unbounded.value answers loss word < Occurrence.Unbounded.infimum answers loss registered + epsilon}) ×
        Runtime.Outcome (Occurrence.reached answers loss word.val) seed.native.input
          (originalRaw loss) (originalBearers loss) (registeredMenus loss))

/-- An unattained minimum opens an explicit precision request. Only the
finite word selected in response is written, with its own exact balance. -/
def compileAtInfimum : ReparationFrontier loss answers registered := by
  classical
  by_cases attained : Occurrence.Unbounded.infimum answers loss registered ∈
      Occurrence.Unbounded.values answers loss registered
  · let word := Classical.choose attained
    have actual := Classical.choose_spec attained
    exact .attained word actual.1 actual.2 (continueAfter loss answers word)
  · refine .approached attained fun epsilon positive => ?_
    have available := Occurrence.Unbounded.every_positive_precision_has_an_actual_eligible_word
      answers loss registered epsilon positive
    let word := Classical.choose available
    have actual := Classical.choose_spec available
    refine ⟨⟨word, actual.1, ?_, actual.2.2.1⟩, continueAfter loss answers word⟩
    exact Occurrence.Unbounded.an_unattained_infimum_is_strict_at_each_actual_word
      answers loss registered attained word actual.1

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal
