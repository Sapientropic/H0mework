import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Slices
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System.Envelope
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Joint

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System.Slices

open Abolition.Root Abolition.Root.Registered Execution

noncomputable section

universe u v w

abbrev Selection (Input Key : Type*) := ∀ word : List Input, Key → Option (Slice word.length)

abbrev LocalInquiry (Current Input : Type*) {Key : Type*} (Issue : Key → Current → List Input → Type*) :=
  ∀ key current word, Option (Issue key current word)

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Key : Type u} {Address : Type v}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Request" => Option (Compile.RawInput Party Good Port Technology Instrument)
local notation "Script" => List Request

local notation "Lookup" => Selection Request Key

variable {Issue : Key → Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument) →
    List (Option (Compile.RawInput Party Good Port Technology Instrument)) → Type w}

local notation "Inquiry" => LocalInquiry C Request Issue

inductive Failure (source : C) (locate : Lookup) (key : Key) (word : Script) : Type w
  | absent (missing : locate word key = none)
  | found (slice : Slice word.length) (original : locate word key = some slice)
      (issue : Issue key (slice.current source word) (slice.body word))

def inspect (source : C) (locate : Lookup) (inquiry : Inquiry)
    (key : Key) (word : Script) : Option (Failure (Issue := Issue) source locate key word) :=
  match found : locate word key with
  | none => some (.absent found)
  | some slice => (inquiry key (slice.current source word) (slice.body word)).map (.found slice found)

theorem a_required_slice_is_paid_exactly_at_its_original_cut
    (source : C) (locate : Lookup) (inquiry : Inquiry) (key : Key) (word : Script) :
    inspect source locate inquiry key word = none ↔
      ∃ slice, locate word key = some slice ∧ inquiry key (slice.current source word) (slice.body word) = none := by
  unfold inspect
  split
  · rename_i missing
    simp [missing]
  · rename_i slice found
    simp [found]

def readAt (source : C) (locate : Lookup) (owner : Address → Key)
    (read : Address → C → Script → EReal) (word : Script) (address : Address) : EReal :=
  match locate word (owner address) with
  | none => ⊤
  | some slice => read address (slice.current source word) (slice.body word)

/-- Every source word is eligible for inspection. The constraints refer to
actual cuts of that one word and use its whole original settlement. -/
theorem the_simultaneous_domain_uses_only_slices_of_one_actual_whole_ledger
    (source : C) (locate : Lookup) (inquiry : Inquiry) (owner : Address → Key)
    (read : Address → C → Script → EReal) (profile : Address → EReal) :
    profile ∈ System.values source id (inspect source locate inquiry) (readAt source locate owner read) ↔
      ∃ word : Script, Settled source word ∧
        (∀ key, ∃ slice, locate word key = some slice ∧
          inquiry key (slice.current source word) (slice.body word) = none ∧
          Recorded (slice.current source word) (slice.body word) ∧
          (type_of% (slice.read_at_the_end_of_a_slice_uses_the_literal_original_successor source word))) ∧
        readAt source locate owner read word = profile := by
  rw [an_assignment_is_in_the_joint_domain_exactly_when_the_original_root_pays_it]
  constructor
  · rintro ⟨word, paid, all, rfl⟩
    refine ⟨word, paid, fun key => ?_, rfl⟩
    obtain ⟨slice, original, clear⟩ := (a_required_slice_is_paid_exactly_at_its_original_cut _ _ _ _ _).mp (all key)
    exact ⟨slice, original, clear, record _ _, slice.read_at_the_end_of_a_slice_uses_the_literal_original_successor source word⟩
  · rintro ⟨word, paid, all, rfl⟩
    refine ⟨word, paid, fun key => ?_, rfl⟩
    obtain ⟨slice, original, clear, _, _⟩ := all key
    exact (a_required_slice_is_paid_exactly_at_its_original_cut _ _ _ _ _).mpr ⟨slice, original, clear⟩

/-- Tight amounts and simultaneous allowances use the same original words.
When a slice is absent its named original requirement remains visible. -/
theorem the_actual_slice_family_has_tight_bounds_and_native_budget_resolution
    (source : C) (locate : Lookup) (inquiry : Inquiry) (owner : Address → Key)
    (read : Address → C → Script → EReal) :
    let check := inspect source locate inquiry
    let reading := readAt source locate owner read
    let domain := System.values source id check reading
    IsGLB domain (sInf domain) ∧ IsLUB domain (sSup domain) ∧
      (∀ address, Bounds.Compiled.Minimum source id (System.inspect check) (fun word => reading word address) ∧
        Bounds.Compiled.Minimum source id (System.inspect check) (fun word => OrderDual.toDual (reading word address))) ∧
      ∀ limit, Nonempty (System.BoxDecision source id check reading limit) := by
  exact ⟨isGLB_sInf _, isLUB_sSup _, every_coordinate_resolves_on_the_same_joint_feasible_domain _ _ _ _,
    fun limit => ⟨System.decideBox _ _ _ _ limit⟩⟩

/-- A crossing in the joint order names both actual excesses. Their
responsible slices and the two original whole accounts remain available. -/
theorem incomparable_actual_amounts_retain_both_responsible_cuts
    (source : C) (locate : Lookup) (inquiry : Inquiry) (owner : Address → Key)
    (read : Address → C → Script → EReal) {first second : Script}
    (firstPaid : Settled source first) (secondPaid : Settled source second)
    (firstPasses : Passes (inspect source locate inquiry) first)
    (secondPasses : Passes (inspect source locate inquiry) second)
    (crossed : ¬ readAt source locate owner read first ≤ readAt source locate owner read second ∧
      ¬ readAt source locate owner read second ≤ readAt source locate owner read first) :
    ∃ crossing : Bounds.Tradeoff source (readAt source locate owner read) first second,
      (∃ slice, locate first (owner crossing.leftBurden) = some slice ∧
        Recorded (slice.current source first) (slice.body first)) ∧
      (∃ slice, locate second (owner crossing.rightBurden) = some slice ∧
        Recorded (slice.current source second) (slice.body second)) := by
  have compare := Bounds.compare_paid source (readAt source locate owner read) first second firstPaid secondPaid
  rcases compare with firstLe | secondLe | crossing
  · exact (crossed.1 firstLe).elim
  · exact (crossed.2 secondLe).elim
  · obtain ⟨crossing⟩ := crossing
    obtain ⟨left, foundLeft, _⟩ :=
      (a_required_slice_is_paid_exactly_at_its_original_cut _ _ _ _ _).mp (firstPasses (owner crossing.leftBurden))
    obtain ⟨right, foundRight, _⟩ :=
      (a_required_slice_is_paid_exactly_at_its_original_cut _ _ _ _ _).mp (secondPasses (owner crossing.rightBurden))
    exact ⟨crossing, ⟨left, foundLeft, record _ _⟩, ⟨right, foundRight, record _ _⟩⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System.Slices
