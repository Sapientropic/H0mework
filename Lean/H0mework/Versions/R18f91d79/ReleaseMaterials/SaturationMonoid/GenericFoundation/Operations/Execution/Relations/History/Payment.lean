import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Occurrence.Cut

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationPaidRelations

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation

variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {environment : Env Value Var} {before after : Expr Value Var sort}

private def rankCharge (rank : Nat) : Nat →₀ ℤ :=
  (Finset.range rank).sum fun k => Finsupp.single (k+1) 1

private def cumulativeRank : Formal ℤ Value Var sort →ₗ[ℤ] (Nat →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun expression => rankCharge (remaining expression)

private theorem step_rank (step : Step environment before after) :
    cumulativeRank (Finsupp.single before 1 - Finsupp.single after 1) =
      Finsupp.single (remaining before) 1 := by
  simp only [map_sub, cumulativeRank, Finsupp.linearCombination_single, one_smul]
  rw [step.remaining_eq]
  simp only [rankCharge, Finset.sum_range_succ, add_sub_cancel_left]

private theorem occurrence_rank (trace : Trace environment before after)
    (index : Fin (words trace).length) :
    cumulativeRank ((words trace).get index) =
      Finsupp.single (remaining before - index.val) 1 := by
  let cut := paidCut trace index
  have written : (words trace).get index =
      Finsupp.single cut.entry 1 - Finsupp.single cut.exit 1 :=
    (stepOccurrence_word trace index).symm.trans (paidCut_word trace index)
  have remainingEq := cut.past.remaining_eq
  rw [cut.position_eq] at remainingEq
  have rank : remaining cut.entry = remaining before - index.val := by omega
  rw [written, step_rank cut.step, rank]

/-- Integer charges indexed by the actual paid Steps write into the source relation word. -/
def writePayment (trace : Trace environment before after) :
    (Fin (words trace).length →₀ ℤ) →ₗ[ℤ] Formal ℤ Value Var sort :=
  Finsupp.linearCombination ℤ (words trace).get

/-- The source reduction rank reads each actual Step's coefficient from the word. -/
def readPayment (trace : Trace environment before after) :
    Formal ℤ Value Var sort →ₗ[ℤ] (Fin (words trace).length →₀ ℤ) :=
  (Finsupp.linearEquivFunOnFinite ℤ ℤ _).symm.toLinearMap.comp
    (LinearMap.pi fun index => (Finsupp.lapply (remaining before - index.val)).comp cumulativeRank)

private theorem read_payment_edge (trace : Trace environment before after)
    (index : Fin (words trace).length) :
    readPayment trace ((words trace).get index) = Finsupp.single index 1 := by
  ext probe
  change cumulativeRank ((words trace).get index) (remaining before - probe.val) = _
  rw [occurrence_rank]
  by_cases same : probe = index
  · subst probe
    simp only [Finsupp.single_eq_same]
  · have length := complete_steps trace
    have remainingEq := trace.remaining_eq
    have indexBound := index.isLt
    have probeBound := probe.isLt
    have distinct : remaining before - probe.val ≠ remaining before - index.val := by
      intro ranks
      exact same (Fin.ext (by omega))
    rw [Finsupp.single_eq_of_ne distinct, Finsupp.single_eq_of_ne same]

theorem read_write_payment (trace : Trace environment before after) :
    Function.LeftInverse (readPayment trace) (writePayment trace) := by
  have composition : (readPayment trace).comp (writePayment trace) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro index coefficient
    simp only [LinearMap.comp_apply, writePayment, Finsupp.linearCombination_single,
      map_smul, read_payment_edge, LinearMap.id_apply, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact LinearMap.congr_fun composition

theorem write_payment_range (trace : Trace environment before after) :
    LinearMap.range (writePayment trace) = Submodule.span ℤ {word | word ∈ words trace} := by
  rw [writePayment, Finsupp.range_linearCombination]
  congr 1
  exact Set.ext fun _ => List.mem_iff_get.symm

def fullPayment (trace : Trace environment before after) : Fin (words trace).length →₀ ℤ :=
  (Finsupp.linearEquivFunOnFinite ℤ ℤ _).symm fun _ => 1

theorem write_full_payment (trace : Trace environment before after) :
    writePayment trace (fullPayment trace) =
      relationMap (R := ℤ) environment (trace.relationWords (R := ℤ)) := by
  rw [← paid_boundary]
  unfold writePayment fullPayment
  rw [Finsupp.linearCombination_eq_fintype_linearCombination_apply, Fintype.linearCombination_apply]
  simp only [one_smul]
  rw [← List.sum_ofFn, List.ofFn_get]

end SourceOperationPaidRelations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
