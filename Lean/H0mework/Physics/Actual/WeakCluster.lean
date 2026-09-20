import H0mework.Physics.Actual.WeakOccurrence
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.WeakCluster

open Filter
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFriedrichsAllOrderWeakLimitOccurrence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {sequence : ℕ → ℕ → H} {target : ℕ → H}

/-- The unthinned source history itself gives a weak occurrence once each
coordinate has reached its source-generated value. -/
def occurrenceOfEventuallyConstant
    (settled : ∀ coordinate, ∀ᶠ index in atTop,
      sequence index coordinate = target coordinate) :
    CountableHilbertWeakLimitOccurrence sequence where
  limit := target
  subsequence := id
  subsequenceStrict := strictMono_id
  weakConvergence coordinate test := by
    apply tendsto_const_nhds.congr'
    filter_upwards [settled coordinate] with index atIndex
    exact congrArg (fun value ↦ inner ℝ value test) atIndex.symm

/-- Every legal subsequence retains the settled source value; weak Hilbert
separation fixes its complete coordinate limit. -/
theorem limit_eq_of_eventuallyConstant
    (settled : ∀ coordinate, ∀ᶠ index in atTop,
      sequence index coordinate = target coordinate)
    (occurrence : CountableHilbertWeakLimitOccurrence sequence) :
    occurrence.limit = target := by
  funext coordinate
  apply ext_inner_right ℝ
  intro test
  have sourceConvergence :=
    (occurrenceOfEventuallyConstant settled).weakConvergence coordinate test
  have subsequenceConvergence :=
    sourceConvergence.comp occurrence.subsequenceStrict.tendsto_atTop
  exact tendsto_nhds_unique
    (occurrence.weakConvergence coordinate test) subsequenceConvergence

theorem pairwise_limit_eq_of_eventuallyConstant
    (settled : ∀ coordinate, ∀ᶠ index in atTop,
      sequence index coordinate = target coordinate)
    (left right : CountableHilbertWeakLimitOccurrence sequence) :
    left.limit = right.limit :=
  (limit_eq_of_eventuallyConstant settled left).trans
    (limit_eq_of_eventuallyConstant settled right).symm

/-- Uniqueness concerns the full weak-limit value, while allowing every
strict subsequence presentation of the same source history. -/
theorem existsUnique_limit_of_eventuallyConstant
    (settled : ∀ coordinate, ∀ᶠ index in atTop,
      sequence index coordinate = target coordinate) :
    ∃! value : ℕ → H, ∃ occurrence : CountableHilbertWeakLimitOccurrence sequence,
      occurrence.limit = value := by
  refine ⟨target, ⟨occurrenceOfEventuallyConstant settled, rfl⟩, ?_⟩
  rintro value ⟨occurrence, rfl⟩
  exact limit_eq_of_eventuallyConstant settled occurrence

end SaturationMonoid.PhysicsCore.Stage9CU.WeakCluster
