import H0mework.Physics.MotherProgrammesFormationRational.Trace
import Mathlib.Data.Nat.Pairing

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.RationalSourceFormation

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Stage9C.Revision MotherFamilyOccurrence StageEightDiscreteFormation

noncomputable section

def unpack : (count : ℕ) → ℕ → Fin count → ℕ
  | 0, _ => Fin.elim0
  | count + 1, code => Fin.cons code.unpair.1 (unpack count code.unpair.2)

def pack : {count : ℕ} → (Fin count → ℕ) → ℕ
  | 0, _ => 0
  | count + 1, values => Nat.pair (values 0) (pack (fun index : Fin count => values index.succ))

theorem unpack_pack (count : ℕ) : ∀ values : Fin count → ℕ, unpack count (pack values) = values := by
  induction count with
  | zero => intro values; funext index; exact Fin.elim0 index
  | succ count induction =>
      intro values
      funext index
      refine Fin.cases ?_ ?_ index
      · simp [pack, unpack]
      · intro tail
        simpa [pack, unpack] using congrFun (induction (fun index : Fin count => values index.succ)) tail

theorem unpack_le (count code : ℕ) (index : Fin count) : unpack count code index ≤ code := by
  induction count generalizing code with
  | zero => exact Fin.elim0 index
  | succ count induction =>
      refine Fin.cases ?_ ?_ index
      · simpa [unpack] using Nat.unpair_left_le code
      · intro tail
        exact (induction code.unpair.2 tail).trans (Nat.unpair_right_le code)

/-- Structural truncation only visits predecessors already carried in this
history. Requests beyond its end return the current prefix. -/
def historyPrefix {current : SpinPair.V.Current} :
    MotherRoot.toRoot.ReachableAt current → ℕ → RootVisit MotherRoot.toRoot
  | .initial, _ => ⟨_, .initial⟩
  | .step prior transition, depth =>
      if ProductiveFiniteRootHistoryAt.causalDepth prior < depth then ⟨_, .step prior transition⟩
      else historyPrefix prior depth

theorem prefix_depth {current : SpinPair.V.Current}
    (history : MotherRoot.toRoot.ReachableAt current) (depth : ℕ) :
    ProductiveFiniteRootHistoryAt.causalDepth (historyPrefix history depth).history =
      min depth (ProductiveFiniteRootHistoryAt.causalDepth history) := by
  induction history with
  | initial => simp [historyPrefix, ProductiveFiniteRootHistoryAt.causalDepth]
  | @step current target prior transition induction =>
      simp only [historyPrefix]
      by_cases before : ProductiveFiniteRootHistoryAt.causalDepth prior < depth
      · rw [if_pos before]
        simp only [ProductiveFiniteRootHistoryAt.causalDepth]
        omega
      · rw [if_neg before, induction]
        simp only [ProductiveFiniteRootHistoryAt.causalDepth]
        omega

def pastVisit (visit : MotherVisit) (address : ℕ) : MotherVisit :=
  .finite (historyPrefix (finiteVisit visit).history (originDepth + address))

theorem past_depth_le (visit : MotherVisit) (address : ℕ) :
    temporalDepth (pastVisit visit address).history ≤ temporalDepth visit.history := by
  change ProductiveFiniteRootHistoryAt.causalDepth
    (historyPrefix (finiteVisit visit).history (originDepth + address)).history ≤ _
  rw [prefix_depth, finite_depth]
  exact Nat.min_le_right _ _

theorem past_code (visit : MotherVisit) (address : ℕ) (past : address ≤ codeOf visit) :
    codeOf (pastVisit visit address) = address := by
  change ProductiveFiniteRootHistoryAt.causalDepth
    (historyPrefix (finiteVisit visit).history (originDepth + address)).history - originDepth = address
  rw [prefix_depth, finite_depth]
  unfold codeOf at past
  by_cases afterOrigin : originDepth ≤ temporalDepth visit.history
  · rw [min_eq_left (by omega)]
    omega
  · have zero : address = 0 := by omega
    subst address
    omega

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.RationalSourceFormation
