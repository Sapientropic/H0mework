import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Network

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Network
open Lean

/-- Public input to one independent run, with its own policy, horizon and exogenous law. -/
structure IndependentDraw (State Noise Observation : Type) where
  initial : State
  strategy : List Observation → Nat → Json
  law : List ((Nat → Noise) × ℚ)
  count : Nat

/-- Ordered independent products of complete observations. Each coordinate uses
its own tape and retains its state, visible observations, and rational weight. -/
def independentProductLaw {State Noise Observation : Type}
    (channel : Channel State Noise Observation) :
    List (Bool × IndependentDraw State Noise Observation) →
      List (List (State × List Observation) × ℚ)
  | [] => [([], 1)]
  | (larger, draw) :: rest =>
    (observationLaw channel larger draw.initial draw.strategy draw.law draw.count).flatMap
      fun (head, headWeight) =>
        (independentProductLaw channel rest).map fun (tail, tailWeight) =>
          (head :: tail, headWeight * tailWeight)

/-- Any finite sequence of private selectors gives the same joint law when the
public experiments and independent exogenous input laws agree coordinatewise. -/
theorem independent_productLaw_eq_of_same_public_draws {State Noise Observation : Type}
    (channel : Channel State Noise Observation)
    {left right : List (Bool × IndependentDraw State Noise Observation)}
    (sameDraws : left.map Prod.snd = right.map Prod.snd) :
    independentProductLaw channel left = independentProductLaw channel right := by
  induction left generalizing right with
  | nil =>
    cases right <;> simp_all [independentProductLaw]
  | cons head tail ih =>
    cases right with
    | nil => cases sameDraws
    | cons other rest =>
      rcases head with ⟨a, first⟩
      rcases other with ⟨b, second⟩
      obtain ⟨sameHead, sameTail⟩ := List.cons.inj (by simpa only [List.map_cons] using sameDraws)
      change first = second at sameHead
      subst second
      have tailEq := ih sameTail
      cases a <;> cases b <;>
        simp only [independentProductLaw, tailEq, all_exogenous_laws_preserve_complete_observation_distribution]

/-- At two equal public draws the product is exactly the original two-run
law with its pair of observations represented as a list. -/
theorem independentProductLaw_pair {State Noise Observation : Type}
    (channel : Channel State Noise Observation)
    (a b : Bool) (draw : IndependentDraw State Noise Observation) :
    independentProductLaw channel [(a, draw), (b, draw)] =
      (independentLaw channel a b draw.initial draw.strategy draw.law draw.count).map
        (fun ((left, right), weight) => ([left, right], weight)) := by
  simp [independentProductLaw, observationLaw, independentLaw, List.flatMap_map,
    List.map_flatMap, Function.comp_def]
  simp only [List.map_eq_flatMap]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Network
