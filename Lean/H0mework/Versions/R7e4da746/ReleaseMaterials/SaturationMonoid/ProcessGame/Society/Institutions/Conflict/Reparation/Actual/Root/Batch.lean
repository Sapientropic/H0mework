import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Root.Open
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Stack

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Quantities.Execution (endAt query next)
open Transport (NativeWork)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "History" => Script Party Good Port Technology Instrument
local notation "Proposal" => Input Party Good Port Technology Instrument

theorem cast_open_back {N : WorldRelationNetwork} {s t : N.Support} (same : s = t)
    (row : OpenResponsibilityAt N t) :
    (same ▸ (same.symm ▸ row : OpenResponsibilityAt N s) : OpenResponsibilityAt N t) = row := by
  cases same
  rfl

/-- A first write being assembled on one original target support.
All responsibility additions are coordinates of this same write. -/
structure Prepared (seed : C) (community : Party → Community)
    (base : WorldRelationNetwork) (atBase : base.Support) where
  world : WorldRelationNetwork
  stack : Stack seed community base world
  draft : Draft world
  target_eq : draft.afterSupport = stack.support atBase

namespace Prepared

variable {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {base : WorldRelationNetwork} {atBase : base.Support}
  (prepared : Prepared seed community base atBase)

def fileOne (origin : Occurrence seed community) : Prepared seed community base atBase where
  world := _
  stack := prepared.stack.append origin
  draft := prepared.draft.extended (file origin)
  target_eq := (prepared.draft.the_joint_first_support_is_the_original_successor_with_the_new_row
    (file origin)).trans (congrArg (fun s => (s, some (Phase.live (opening origin)))) prepared.target_eq)

def fileMany (prepared : Prepared seed community base atBase) :
    List (Occurrence seed community) → Prepared seed community base atBase
  | [] => prepared
  | origin :: tail => (prepared.fileOne origin).fileMany tail

theorem fileMany_balances (origins : List (Occurrence seed community)) :
    (prepared.fileMany origins).stack.balances = prepared.stack.balances ++
      origins.map (fun origin => (origin, opening origin)) := by
  induction origins generalizing prepared with
  | nil => simp only [fileMany, List.map_nil, List.append_nil]
  | cons origin tail ih =>
    rw [fileMany, ih]
    change (prepared.stack.balances ++ [(origin, opening origin)]) ++ _ = _
    rw [List.append_assoc]
    rfl

abbrev entered := prepared.draft.enter

theorem entered_support : prepared.entered.support = prepared.stack.support atBase :=
  prepared.draft.enter_support.trans prepared.target_eq

def read (row : OpenResponsibilityAt prepared.world prepared.entered.support) :
    OpenResponsibilityAt base atBase ⊕ (Occurrence seed community × Balance) :=
  prepared.stack.read atBase (prepared.entered_support ▸ row)

theorem each_open_balance_is_on_the_actual_next (balance : Occurrence seed community × Balance)
    (filed : balance ∈ prepared.stack.balances) :
    ∃ row : OpenResponsibilityAt prepared.world prepared.entered.support, prepared.read row = .inr balance := by
  obtain ⟨row, exactRow⟩ := prepared.stack.every_balance_has_an_actual_open_row atBase balance filed
  refine ⟨prepared.entered_support.symm ▸ row, ?_⟩
  unfold read
  rwa [cast_open_back]

end Prepared

variable (seed : Root.Cut Party Good Port Technology Instrument) (community : Party → Community)
  (past : Script Party Good Port Technology Instrument) (input : Input Party Good Port Technology Instrument)

abbrev tick : C := query (endAt seed past) input

def openings : List (Occurrence seed community) :=
  (Boundary.Actual.damages (endAt seed past) input community).map
    (fun damage => ⟨past, input, damage⟩)

def materialBatch (ready : ¬ NativeWork (tick seed past input)) :
    Prepared seed community (endAt seed past).native.frame.N
      (materialDraft (endAt seed past) input ready).afterSupport :=
  let draft := materialDraft (endAt seed past) input ready
  let initial : Prepared seed community _ draft.afterSupport := ⟨_, .base _, draft, rfl⟩
  initial.fileMany (openings seed community past input)

theorem every_affected_address_is_filed_on_the_same_generated_next
    (ready : ¬ NativeWork (tick seed past input))
    (damage : Boundary.Actual.DamageAt (endAt seed past) input community) :
    let result := materialBatch seed community past input ready
    let origin : Occurrence seed community := ⟨past, input, damage⟩
    ∃ row : OpenResponsibilityAt result.world result.entered.support,
      result.read row = .inr (origin, opening origin) := by
  intro result origin
  apply result.each_open_balance_is_on_the_actual_next
  unfold result materialBatch
  rw [Prepared.fileMany_balances]
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨origin, List.mem_map.mpr ⟨damage, Boundary.Actual.every_actual_debit_is_assessed damage, rfl⟩, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
