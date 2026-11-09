import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Joint.Exits

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Joint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  [DecidableEq (Request Party Good Port Technology Instrument)]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin raw : RawCurrent Party Good Technology Instrument) (people : List Party)
  (registered : RecipeMenu input raw) (incumbent : RawEvent Party Good Port Technology Instrument)
  (basis : RepeatCode input raw)

local notation "Fresh" => Repair.Fresh input raw registered incumbent

def codes (width : Nat) (personal : Exits input origin raw width people) : RecipeMenu input raw :=
  ((words input raw people width).filter fun word => decide (Fresh word)).map fun word =>
    { basis with production := word, personal := personal.word }

def Within (width : Nat) (code : RepeatCode input raw) : Prop :=
  code.production.length ≤ width ∧ ∀ person ∈ people, (code.personal person).length ≤ width

def widthOf (code : RepeatCode input raw) : Nat :=
  max code.production.length (people.toFinset.sup fun person => (code.personal person).length)

omit [DecidableEq Good] [DecidableEq Instrument] [DecidableEq (Request Party Good Port Technology Instrument)] in
theorem within_widthOf (code : RepeatCode input raw) :
    Within input raw people (widthOf input raw people code) code := by
  refine ⟨le_max_left _ _, fun person listed => ?_⟩
  exact (Finset.le_sup (f := fun p => (code.personal p).length) (List.mem_toFinset.mpr listed)).trans
    (le_max_right _ _)

variable (width : Nat)

structure Plan where
  personal : Exits input origin raw width people
  selected : SelectedRecipe input origin raw people (codes input origin raw people registered incumbent basis width personal)

theorem Plan.source_conditions (plan : Plan input origin raw people registered incumbent basis width) :
    ∃ code : RepeatCode input raw,
      code.production = plan.selected.recipe.move.word ∧ Fresh code.production ∧
      Within input raw people width code ∧ RecipeConditions input origin raw people code := by
  let code := (codes input origin raw people registered incumbent basis width plan.personal)[plan.selected.position]
  have member : code ∈ codes input origin raw people registered incumbent basis width plan.personal :=
    List.getElem_mem plan.selected.position.isLt
  obtain ⟨word, inside, exactCode⟩ := List.mem_map.mp member
  have wordListed := List.mem_filter.mp inside
  have exactWord : plan.selected.recipe.move.word = word := plan.selected.word.trans (congrArg RepeatCode.production exactCode).symm
  refine ⟨{ basis with production := word, personal := plan.personal.word }, exactWord.symm,
    of_decide_eq_true wordListed.2, ⟨words_have_bounded_length _ _ _ wordListed.1,
    plan.personal.bounded⟩, ?_, ?_, ?_, ?_⟩
  · exact exactWord ▸ ⟨plan.selected.recipe.move.registered, plan.selected.recipe.move.paid⟩
  · exact fun person listed => ⟨plan.personal.registered person listed, plan.personal.paid person listed⟩
  · exact exactWord ▸ plan.selected.recipe.law.accumulating
  · exact exactWord ▸ plan.selected.recipe.positiveGain

inductive Obstruction
  | exit (issue : ExitIssue input origin raw width people)
  | production (personal : Exits input origin raw width people)
      (refused : RejectedRecipes input origin raw people
        (codes input origin raw people registered incumbent basis width personal))

theorem Obstruction.excludes (blocked : Obstruction input origin raw people registered incumbent basis width)
    (code : RepeatCode input raw) (fresh : Fresh code.production)
    (within : Within input raw people width code) :
    ¬ RecipeConditions input origin raw people code := by
  intro fits
  cases blocked with
  | exit issue =>
    have paid := fits.2.1 issue.person issue.listed
    exact issue.refutes _ _ _ _ (within.2 _ issue.listed) paid.1 paid.2
  | production personal refused =>
    let assembled := { basis with production := code.production, personal := personal.word }
    have listed : assembled ∈ codes input origin raw people registered incumbent basis width personal := by
      apply List.mem_map.mpr
      refine ⟨code.production, List.mem_filter.mpr ⟨?_, decide_eq_true fresh⟩, rfl⟩
      exact every_paid_registered_word_is_listed _ _ _ _ within.1 fits.1.1 fits.1.2
    obtain ⟨i, inside, same⟩ := List.getElem_of_mem listed
    apply (refused ⟨i, inside⟩).refutes _ _ _ _ _
    change RecipeConditions input origin raw people
      (codes input origin raw people registered incumbent basis width personal)[i]
    rw [same]
    exact ⟨fits.1, fun person member => ⟨personal.registered person member, personal.paid person member⟩, fits.2.2⟩

def inspect : Obstruction input origin raw people registered incumbent basis width ⊕
    Plan input origin raw people registered incumbent basis width :=
  match exits input origin raw width people with
  | .inl issue => .inl (.exit issue)
  | .inr personal =>
    match chooseRecipe input origin raw people (codes input origin raw people registered incumbent basis width personal) with
    | .inl failed => .inl (.production personal failed)
    | .inr chosen => .inr ⟨personal, chosen⟩

inductive Search (limit : Nat)
  | pending (tested : ∀ width ≤ limit, Obstruction input origin raw people registered incumbent basis width)
  | found (width : Nat) (within : width ≤ limit)
      (earlier : ∀ n < width, Obstruction input origin raw people registered incumbent basis n)
      (plan : Plan input origin raw people registered incumbent basis width)

/-- Widen the checked domain in order of the longest independently
required word. Exhaustion certifies the checked widths and stays pending. -/
def search : (limit : Nat) → Search input origin raw people registered incumbent basis limit
  | 0 =>
    match inspect input origin raw people registered incumbent basis 0 with
    | .inl failed => .pending (fun n bound => (Nat.eq_zero_of_le_zero bound).symm ▸ failed)
    | .inr plan => .found 0 le_rfl (fun n early => (Nat.not_lt_zero n early).elim) plan
  | limit + 1 =>
    match search limit with
    | .found width within earlier plan => .found width (within.trans (Nat.le_succ _)) earlier plan
    | .pending tested =>
      match inspect input origin raw people registered incumbent basis (limit + 1) with
      | .inr plan => .found (limit + 1) le_rfl (fun n early => tested n (Nat.lt_succ_iff.mp early)) plan
      | .inl failed => .pending (fun n bound => by
          by_cases same : n = limit + 1
          · exact same.symm ▸ failed
          · exact tested n (Nat.lt_succ_iff.mp (lt_of_le_of_ne bound same)))

variable {input origin raw people registered incumbent basis} in
def Search.word {limit : Nat} : Search input origin raw people registered incumbent basis limit →
    Option (RawEvent Party Good Port Technology Instrument)
  | .pending _ => none
  | .found _ _ _ plan => some plan.selected.recipe.move.word

theorem search_is_complete_at_every_width (code : RepeatCode input raw)
    (fresh : Fresh code.production) (within : Within input raw people width code)
    (fits : RecipeConditions input origin raw people code) :
    (search input origin raw people registered incumbent basis width).word.isSome = true := by
  cases search input origin raw people registered incumbent basis width with
  | pending tested => exact ((tested width le_rfl).excludes _ _ _ _ _ _ _ _ code fresh within fits).elim
  | found _ _ _ _ => rfl

theorem checked_prefixes_cover_every_finite_joint_recipe :
    (∃ width, (search input origin raw people registered incumbent basis width).word.isSome = true) ↔
      ∃ code : RepeatCode input raw, Fresh code.production ∧ RecipeConditions input origin raw people code := by
  constructor
  · rintro ⟨limit, found⟩
    cases tested : search input origin raw people registered incumbent basis limit with
    | pending _ => rw [tested] at found; cases found
    | found width _ _ plan =>
      obtain ⟨code, _, fresh, _, paid⟩ := plan.source_conditions _ _ _ _ _ _ _ _
      exact ⟨code, fresh, paid⟩
  · rintro ⟨code, fresh, paid⟩
    exact ⟨widthOf input raw people code, search_is_complete_at_every_width _ _ _ _ _ _ _ _ code fresh
      (within_widthOf _ _ _ _) paid⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Joint
