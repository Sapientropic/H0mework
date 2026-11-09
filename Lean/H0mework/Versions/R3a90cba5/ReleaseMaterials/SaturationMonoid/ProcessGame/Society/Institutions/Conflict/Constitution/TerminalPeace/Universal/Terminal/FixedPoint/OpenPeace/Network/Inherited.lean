import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.History
import H0mework.Foundation.Responsibility.DebtU7

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Root.Registered.Macro
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld RootGeneratedDebtActivationU7
open Reparation.Actual Reparation.Actual.Allocation
open Quantities.Execution (endAt next query endAt_append)

open private consumeItems from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Receipts

noncomputable section

abbrev InheritedCalculus (N : WorldRelationNetwork) :=
  Σ producer : U7ProducerCalculus N, U7ObstructionEvolutionCalculus N producer

private def extend {N : WorldRelationNetwork} (law : DebtActivationLaw)
    (old : InheritedCalculus N) : InheritedCalculus (ExtendedNetwork N law) :=
  ⟨extendU7 (law := law) old.1, extendU7Calculus (law := law) old.1 old.2⟩

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "Cut" => Conflict.Root.Cut Party Good Port Technology Instrument

def inheritedAtCut (cut : Cut) : InheritedCalculus cut.native.frame.N :=
  ⟨cut.native.frame.basis.U7, cut.native.frame.basis.calculus⟩

variable {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {past : Reparation.Actual.Script Party Good Port Technology Instrument}

private theorem rebased_world {cut other : Cut} (state : StateAt seed community cut) (same : cut = other) :
    (state.rebase same).world = state.world := by
  cases same
  rfl

private theorem queried_world {cut : Cut} (state : StateAt seed community cut)
    (input : Reparation.Actual.Input Party Good Port Technology Instrument) :
    (state.atQuery input).world = state.world := by
  cases input <;> rfl

private def inheritedFiles {N : WorldRelationNetwork} {support : N.Support}
    (prepared : Prepared seed community N support) (prior : InheritedCalculus prepared.world) :
    (origins : List (Occurrence seed community)) → InheritedCalculus (prepared.fileMany origins).world
  | [] => prior
  | origin :: later =>
    inheritedFiles (prepared.fileOne origin) (extend (Reparation.Actual.law origin) prior) later

variable (state : Reparation.Actual.State seed community past)
  (input : Reparation.Actual.Input Party Good Port Technology Instrument)

private def inheritedSame (prior : InheritedCalculus state.world) (safe : Reparation.History.NoFinancialBirth (query (endAt seed past) input)) :
    InheritedCalculus (sameNext state input safe).world := by
  unfold sameNext StateAt.fromPrepared samePrepared
  exact inheritedFiles _ prior (openings seed community past input)

/-- Keep the original U7 compiler and extend it at the source-selected
material or financial admission, using its exact registered law. -/
def inheritedPosted (prior : InheritedCalculus state.world) : InheritedCalculus (posted state input).world := by
  cases disposition : Reparation.Transport.inspect (query (endAt seed past) input) with
  | material ready =>
    rw [posted, disposition]
    exact inheritedSame state input prior (.inl ready)
  | accounting _ absent =>
    rw [posted, disposition]
    exact inheritedSame state input prior (.inr absent)
  | registration work registered selected =>
    rw [posted, disposition]
    let born := financeBorn (state.atQuery input) registered
    have same : (financeNext state input work registered selected).world = born.world :=
      rebased_world born (selected_birth_is_the_original_cut input work selected).symm
    have inherited : InheritedCalculus born.world :=
      extend _ ((queried_world state input).symm ▸ prior)
    exact same.symm ▸ inherited

private theorem consumeItems_world
    {positions : List (Position seed past input)} {rows : List (Occurrence seed community × Balance)}
    (trace : ItemWrites (community := community) past input positions rows)
    (state : StateAt seed community (next (endAt seed past) input)) (same : state.stack.balances = rows) :
    (consumeItems past input trace state same).val.world = state.world := by
  induction trace generalizing state with
  | nil => rfl
  | next tail earlier =>
    unfold consumeItems
    exact earlier _ _

private theorem writtenReceipts_world (state : StateAt seed community (next (endAt seed past) input)) :
    (writtenReceipts past input state).val.world = state.world :=
  consumeItems_world input _ state rfl

def inheritedAdvance (prior : InheritedCalculus state.world) :
    InheritedCalculus (Reparation.Actual.advance state input).world := by
  let material := posted state input
  let written := (writtenReceipts past input material).val
  have same : (Reparation.Actual.advance state input).world = written.world :=
    rebased_world written (endAt_append seed past [input]).symm
  have unchanged : written.world = material.world := writtenReceipts_world input material
  exact (same.trans unchanged).symm ▸ inheritedPosted state input prior

/-- Start from the native frame's own total compiler and follow every
original material and financial birth in the actual replay. -/
def inheritedRun (seed : Cut) (community : Party → Community)
    (history : Reparation.Actual.Script Party Good Port Technology Instrument) :
    InheritedCalculus (Reparation.Actual.run seed community history).world := by
  induction history using List.reverseRecOn with
  | nil =>
    rw [Reparation.Actual.run_nil]
    exact inheritedAtCut seed
  | append_singleton previous request inherited =>
    rw [Reparation.Actual.run_snoc]
    exact inheritedAdvance _ request inherited

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network
