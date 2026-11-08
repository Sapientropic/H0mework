import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening.Scan
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.ClaimsReceipt.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.PendingDrain.Account
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.LawfulPrefix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Financial.Installation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation

noncomputable section

variable {Party Good Port Technology Instrument : Type}

def atAddress (matrix : Instrument → Party → Party → ℚ) : Matrix Instrument Party :=
  fun address => matrix address.instrument address.debtor address.holder

theorem atAddress_injective : Function.Injective (atAddress (Instrument := Instrument) (Party := Party)) := by
  intro left right same
  funext instrument debtor holder
  exact congrFun same ⟨instrument, debtor, holder⟩

variable [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def genesisRaw : Matrix Instrument Party := atAddress input.initial.claims

def genesisCarried : Matrix Instrument Party :=
  atAddress (Completion.Actual.External.Admission.nativeInitialClaims input)

theorem genesis_matches_iff :
    genesisRaw input = genesisCarried input ↔ input.initial.claims = fun _ _ _ => 0 := by
  rw [genesisRaw, genesisCarried,
    Completion.Actual.External.Admission.the_canonical_native_genesis_has_zero_claims]
  exact ⟨fun matching => atAddress_injective matching, congrArg atAddress⟩

variable (depth start : Nat)

/-- The original cursor pays down the existing bookkeeping queue at the
same physical cut, before any fresh word. -/
abbrev cut : Nat := (PendingDrain.drain input depth start).last

def originalAccount : (Financial.process input).GeneratedState :=
  (Runtime.cursorAt input depth (cut input depth start)).account

def rawAtCut : Matrix Instrument Party :=
  atAddress (ProgrammeSource.rawCurrent input
    (Cursor.physicalVisit input (Runtime.cursorAt input depth start)).current).claims

def carriedAtCut : Matrix Instrument Party :=
  atAddress (Financial.BalanceConservation.ledgerClaims input (originalAccount input depth start).current)

theorem originalAccount_is_on_the_actual_frame :
    originalAccount input depth start = ((PendingDrain.frame input depth start).cursor input).account :=
  congrArg Cursor.State.account (Runtime.frames_cursor input depth (cut input depth start)).symm

theorem rawAtCut_is_the_actual_frame :
    rawAtCut input depth start = atAddress (Runtime.physical input (Runtime.frames input depth start)).claims := by
  unfold rawAtCut Runtime.physical
  rw [Runtime.frames_cursor]

theorem rawAtCut_is_unchanged_by_drain :
    rawAtCut input depth start = atAddress (Runtime.physical input (PendingDrain.frame input depth start)).claims := by
  rw [rawAtCut_is_the_actual_frame]
  unfold Runtime.physical
  rw [PendingDrain.no_physical_body_is_replayed input depth start]

theorem nativeCut_recovers_all_original_claims
    (initialZero : input.initial.claims = fun _ _ _ => 0) :
    rawAtCut input depth start = carriedAtCut input depth start := by
  let cursor := Runtime.cursorAt input depth (cut input depth start)
  have fresh := (PendingDrain.drain input depth start).stoppedBeforeFresh
  change Cursor.FreshBody input cursor at fresh
  have aligned := Runtime.cursorAt_prefix_aligned input depth (cut input depth start)
  change Cursor.PrefixAligned input cursor at aligned
  have ready : cursor.position = 0 ∧ cursor.ahead = 0 := by
    rcases fresh with entering | ready
    · have accounting := Runtime.cursorAt_accounting input depth (cut input depth start)
      change cursor.phase = .accounting at accounting
      rw [accounting] at entering
      cases entering
    · exact ready
  have wholeAccount : cursor.account = Financial.accountAt input cursor.cycle := by
    simpa only [ready.1, List.take_zero, Financial.consumeOrigins] using aligned.2
  have physical : Cursor.physicalVisitIndex input cursor = cursor.cycle := by
    simp [Cursor.physicalVisitIndex, ready.1, ready.2]
  rw [rawAtCut_is_unchanged_by_drain, Runtime.physical, PendingDrain.frame, Runtime.frames_cursor]
  change atAddress (ProgrammeSource.rawCurrent input (Cursor.physicalVisit input cursor).current).claims =
    atAddress (Financial.BalanceConservation.ledgerClaims input cursor.account.current)
  rw [wholeAccount, Cursor.physicalVisit, physical]
  exact congrArg atAddress (Financial.BalanceConservation.generated_prefix_claims input initialZero cursor.cycle).symm

def inherited : (Epoch.Finance.process input depth (cut input depth start)).GeneratedState :=
  (Epoch.Finance.settleCommitted input depth (cut input depth start)).after

/-- Exactly the existing settlement continuation receives the original GS
and its complete dependent Run, including terminal archive receipts. -/
theorem inherited_is_the_original_run :
    inherited input depth start =
      Epoch.Finance.Legacy.generated input depth (cut input depth start) (originalAccount input depth start) := by
  rw [originalAccount_is_on_the_actual_frame]
  exact PendingDrain.macro_initial_account_is_the_literal_drained_account input depth start

theorem inherited_retains_original_slots_and_history :
    (inherited input depth start).current.slots =
      (originalAccount input depth start).current.slots.map
        (Epoch.Finance.Legacy.slot input depth (cut input depth start)) ∧
    (inherited input depth start).current.history =
      (originalAccount input depth start).current.history.map
        (Epoch.Finance.Legacy.lifecycle input depth (cut input depth start)) := by
  rw [inherited_is_the_original_run]
  exact Epoch.Finance.Legacy.every_slot_and_history_entry_is_retained input depth
    (cut input depth start) (originalAccount input depth start)

theorem inherited_does_not_replay_the_source_word :
    Cursor.physicalVisit input ((PendingDrain.frame input depth start).cursor input) =
      Cursor.physicalVisit input ((Runtime.frames input depth start).cursor input) :=
  PendingDrain.no_physical_body_is_replayed input depth start

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening
