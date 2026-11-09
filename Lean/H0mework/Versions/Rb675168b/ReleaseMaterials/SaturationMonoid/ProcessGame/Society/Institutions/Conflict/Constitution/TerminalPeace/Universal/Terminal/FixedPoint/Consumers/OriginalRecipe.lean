import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Revision
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Consumers.Alternation

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OriginalRecipe

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material.Continuation
open Capitalism.Universal.Abolition.Root.Registered
open Conflict.Consumers.Evolving (W compact)
open Runtime.Viability (Move)
open TerminalPeace.Supply (localTechnique personalWord)
open Supply.Consumers (refillWord)

noncomputable section

def offer : ProductionOffer Bool Bool Bool Unit Unit :=
  ⟨localTechnique, refillWord, []⟩

def programme := reviseProgramme compact offer

abbrev opening := Settlement.settledCut.raw

private theorem opening_eq : opening = Original.snapshot 117 107 :=
  Settlement.settled_raw

def periodPasses (roster : List Bool) (word : W) (raw : Original.Raw) : Bool :=
  match Supply.inspect programme raw raw roster word with
  | .inr _ => true
  | .inl _ => false

theorem paidAt (origin raw : Original.Raw) (roster : List Bool) (word : W)
    (passed : periodPasses roster word raw = true) :
    Supply.Period programme origin raw roster word := by
  cases checked : Supply.inspect programme raw raw roster word with
  | inl issue =>
    unfold periodPasses at passed
    rw [checked] at passed
    cases passed
  | inr paid =>
    exact ⟨paid.down.own, paid.down.originalFloor, paid.down.currentFloor, paid.down.positiveClock⟩

private theorem personal_registered (raw : Original.Raw) (person : Bool) :
    Supply.Registered programme raw (personalWord person) := by
  intro request listed
  apply revision_registers_its_pilot compact offer raw request
  cases person <;> simp [offer, refillWord, personalWord] at listed ⊢ <;> grind

private theorem timing : programme.law.TimeIndependent :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

private theorem reserveInsensitive : programme.law.ReserveInsensitive :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

private theorem original_registration (raw : Original.Raw) : Move.RegistrationOnReserves programme raw := by
  intro extra available clock round word original
  exact original

/-- Finite checks at a newly reached original cut instantiate the same
physical production law and its independent living words. -/
def recipeOfChecks (origin raw : Original.Raw) (roster : List Bool)
    (paid : Supply.Period programme origin raw roster refillWord)
    (personal : ∀ person ∈ roster, Supply.Period programme origin raw [person] (personalWord person))
    (balance : Balance.FiniteChecks .accumulating programme.law raw refillWord)
    (growth : ∃ person good, 0 < Balance.gain programme.law raw refillWord person good) :
    Recipe programme origin roster raw 1 where
  move := {
    word := refillWord
    registered := revision_registers_its_pilot compact offer raw
    paid := paid
    personal := fun person listed => ⟨personalWord person, personal_registered raw person, personal person listed⟩ }
  law := {
    timing := timing
    reserve := reserveInsensitive
    accumulating := balance
    positive := by norm_num
    duration := fun _ _ _ _ => le_rfl
    registered := fun _ _ _ _ original => original }
  registration := original_registration raw
  positiveGain := growth

/-- On the already settled original cut, the old refill sequence leaves
one new meal per person after paying both original living needs. -/
def originalRecipe (origin : Original.Raw) : Recipe programme origin [false, true] opening 1 :=
  recipeOfChecks origin opening [false, true]
    (paidAt origin opening _ _ (by rw [opening_eq]; decide +kernel))
    (fun person _ => paidAt origin opening _ _ (by rw [opening_eq]; cases person <;> decide +kernel))
    (by rw [opening_eq]; decide +kernel)
    ⟨false, true, by rw [opening_eq]; decide +kernel⟩

theorem exact_gain (origin : Original.Raw) (person good : Bool) :
    (originalRecipe origin).gain person good = if good then 1 else 0 := by
  change Balance.gain programme.law opening refillWord person good = _
  rw [opening_eq]
  cases person <;> cases good <;> decide +kernel

theorem original_pilot_writes_and_renews (origin : Original.Raw) :
    let written := Physical.Public.compile programme Settlement.settledCut.state (.execute refillWord)
    written.isAccepted = true ∧
      (∀ person good, written.next.raw.stock person good = opening.stock person good + (if good then 1 else 0)) ∧
      written.next.raw.claims = opening.claims ∧ written.next.raw.clock = opening.clock + 1 := by
  have pilot : Supply.Period programme origin opening [false, true] refillWord := (originalRecipe origin).move.paid
  have actual := pilot.native_write Settlement.settledCut.state
  dsimp only at actual ⊢
  refine ⟨actual.1, ?_, ?_, ?_⟩
  · intro person good
    rw [actual.2.2]
    change (programme.law.next opening refillWord).stock person good = _
    rw [opening_eq]
    cases person <;> cases good <;> decide +kernel
  · rw [actual.2.2]
    change (programme.law.execute opening 0 refillWord).final.claims = opening.claims
    have endpoint := (Balance.checked_productive_period _ _ _ (originalRecipe origin).law.accumulating).1
    have same := congrArg (fun result : Original.Raw => result.claims) endpoint
    exact same
  · rw [actual.2.2]
    change opening.clock + max 0 (1 : ℚ) = _
    norm_num

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OriginalRecipe
