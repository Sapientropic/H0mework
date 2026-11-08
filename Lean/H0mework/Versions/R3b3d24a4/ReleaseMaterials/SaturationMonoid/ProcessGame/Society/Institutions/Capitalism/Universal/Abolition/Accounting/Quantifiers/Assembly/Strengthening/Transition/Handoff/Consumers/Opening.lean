import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Ingress
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Joint

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.OpeningCheck

open Actual
open Abolition.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Joint

noncomputable section

abbrev Key := Opening.Address Unit Bool
abbrev legacyKey : Key := ⟨(), false, true⟩

def recorded (amount : ℚ) : Opening.Matrix Unit Bool :=
  fun key => if key = legacyKey then amount else 0

private def keys : List Key :=
  [⟨(), false, false⟩, legacyKey, ⟨(), true, false⟩, ⟨(), true, true⟩]

private def all (raw carried : Opening.Matrix Unit Bool) : Opening.Support raw carried :=
  .ofAll raw carried keys (by decide +kernel) (by
    rintro ⟨⟨⟩, debtor, holder⟩
    cases debtor <;> cases holder <;> decide +kernel)

private theorem sameCut : seed.count = Opening.cut seed.input seed.depth 19 ∨
    seed.count + 1 = Opening.cut seed.input seed.depth 19 := by
  apply Or.inr
  let drain := Epoch.Finance.Installation.PendingDrain.drain input 0 19
  change 20 = drain.last
  have fresh : Financial.Installation.Cursor.FreshBody input
      (Financial.Installation.Runtime.cursorAt input 0 20) := by decide +kernel
  have stillOld : ¬ Financial.Installation.Cursor.FreshBody input
      (Financial.Installation.Runtime.cursorAt input 0 19) := by decide +kernel
  apply le_antisymm
  · by_contra! earlier
    have exactOld : drain.last = 19 := by have := drain.after; omega
    have stopped := drain.stoppedBeforeFresh
    rw [exactOld] at stopped
    exact stillOld stopped
  · by_contra! later
    exact drain.bookkeeping 20 (by decide) later fresh

private theorem zeroGenesis : input.initial.claims = fun _ _ _ => 0 := by
  funext instrument debtor holder
  cases instrument
  cases debtor <;> cases holder <;> decide +kernel

theorem the_original_cut_has_one_unpaid_old_unit :
    Opening.rawAtCut input 0 19 = recorded 1 := by
  funext key
  obtain ⟨⟨⟩, debtor, holder⟩ := key
  cases debtor <;> cases holder <;> decide +kernel

def submit (amount : ℚ) :=
  selectAtOpening seed grossClaim enough (fun _ _ => .advance) 19 sameCut (recorded amount)
    (all _ _) (all _ _) [proposal] ordered task reserved held budget ((6 : ℚ) : WithTop ℚ)

set_option backward.isDefEq.respectTransparency false in
theorem the_verified_old_balance_enters_the_same_paid_handoff :
    ∃ opening run listed paid least,
      submit 1 = .checked opening run (.selected proposal listed paid least) := by
  obtain ⟨reading, checked⟩ := (Opening.reopenAt_certifies_iff input 0 19 (recorded 1)
    (all _ _) (all _ _)).mpr ⟨zeroGenesis, the_original_cut_has_one_unpaid_old_unit.symm⟩
  change Opening.reopenAt seed.input seed.depth 19 (recorded 1) (all _ _) (all _ _) = .certified reading at checked
  have noRefusal : refusal source ordered task reserved held budget ((6 : ℚ) : WithTop ℚ) proposal = none :=
    (has_no_refusal_iff _ _ _ _ _ _ _ _).mpr the_same_original_handoff_is_admitted_at_clock_six
  have only : admittedFrom source ordered task reserved held budget ((6 : ℚ) : WithTop ℚ) [proposal] = [proposal] := by
    simpa [admittedFrom] using noRefusal
  have chosen : (admittedFrom source ordered task reserved held budget ((6 : ℚ) : WithTop ℚ) [proposal]).argmin
      (handoffTime source) = some proposal := by rw [only]; rfl
  have result : ∃ listed paid least,
      select source ordered task reserved held budget ((6 : ℚ) : WithTop ℚ) [proposal] (handoffTime source) =
        .selected proposal listed paid least := by
    unfold select
    dsimp only
    split
    · rename_i found observed
      have same : found = proposal := Option.some.inj (observed.symm.trans chosen)
      subst found
      refine ⟨List.mem_cons_self, the_same_original_handoff_is_admitted_at_clock_six, ?_, rfl⟩
      intro other member _
      rw [List.mem_singleton.mp member]
    · rename_i observed
      rw [chosen] at observed
      cases observed
  obtain ⟨listed, paid, least, selected⟩ := result
  unfold submit selectAtOpening
  rw [checked]
  exact ⟨reading, _, listed, paid, least, congrArg (Ingress.checked reading _) selected⟩

set_option backward.isDefEq.respectTransparency false in
theorem reporting_two_old_units_names_the_original_debtor_and_holder :
    ∃ report, submit 2 = .conflicting legacyKey [] report := by
  obtain ⟨opening, verified⟩ := (Opening.openAt_accepts_iff input 0 19 (all _ _)).mpr zeroGenesis
  change Opening.openAt seed.input seed.depth 19 (all _ _) = .accepted opening at verified
  unfold submit selectAtOpening Opening.reopenAt
  rw [verified]
  have diff : Opening.discrepancies (all (recorded 2) (Opening.carriedAtCut seed.input seed.depth 19)) = [legacyKey] := by
    decide +kernel
  have rejected : ∃ report, Opening.inspect (all (recorded 2)
      (Opening.carriedAtCut seed.input seed.depth 19)) = .refused legacyKey [] report := by
    unfold Opening.inspect
    split
    · rename_i observed
      rw [observed] at diff
      cases diff
    · rename_i first rest observed
      have same : first :: rest = [legacyKey] := observed.symm.trans diff
      injection same with address tail
      subst first
      subst rest
      exact ⟨diff, rfl⟩
  obtain ⟨report, refused⟩ := rejected
  rw [refused]
  exact ⟨report, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.OpeningCheck
