import H0mework.Realization.Operations.InventoryLift
import H0mework.Realization.Operations.Execution.Relations.History.Events

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.SourceOperationScalarInventoryLift.Rechart

open SourceOperationEffects SourceOperationScalarRelations SourceOperationExecution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedScalarDifferentialResidual

universe u
variable {S : Type u} {V W X : S → Type u}
variable [∀ s, AddCommGroup (V s)] [∀ s, AddCommGroup (W s)]
variable (chart : ∀ s, V s ≃+ W s)

private def linear {s t : S} (f : V s →+ V t) : W s →+ W t :=
  (chart t).toAddMonoidHom.comp (f.comp (chart s).symm.toAddMonoidHom)

private def bilinear {s t r : S} (f : V s →+ V t →+ V r) : W s →+ W t →+ W r where
  toFun a := linear chart (f ((chart s).symm a))
  map_zero' := by ext b; simp [linear]
  map_add' a b := by ext z; simp [linear, map_add]

/-- Change the coordinates of the actual operation at every syntax node. -/
def expr {s : S} : Expr V X s → Expr W X s
  | .var name => .var name
  | .const value => .const (chart s value)
  | .add a b => .add (expr a) (expr b)
  | .linear f a => .linear (linear chart f) (expr a)
  | .bilinear f a b => .bilinear (bilinear chart f) (expr a) (expr b)

private theorem linear_back {s t : S} (f : V s →+ V t) :
    linear (fun z => (chart z).symm) (linear chart f) = f := by
  ext a
  simp [linear]

private theorem bilinear_back {s t r : S} (f : V s →+ V t →+ V r) :
    bilinear (fun z => (chart z).symm) (bilinear chart f) = f := by
  ext a b
  simp [bilinear, linear]

private theorem expr_back {s : S} (term : Expr V X s) :
    expr (fun z => (chart z).symm) (expr chart term) = term := by
  induction term with
  | var _ => rfl
  | const _ => simp only [expr, AddEquiv.symm_apply_apply]
  | add a b ha hb => simp only [expr, ha, hb]
  | linear f a ha => simp only [expr, linear_back, ha]
  | bilinear f a b ha hb => simp only [expr, bilinear_back, ha, hb]

def exprEquiv (s : S) : Expr V X s ≃ Expr W X s where
  toFun := expr chart
  invFun := expr (fun z => (chart z).symm)
  left_inv := expr_back chart
  right_inv term := by simpa only [AddEquiv.symm_symm] using expr_back (fun z => (chart z).symm) term

def env (old : Env V X) : Env W X := fun s name => chart s (old s name)

theorem expr_remaining {s : S} (term : Expr V X s) :
    remaining (expr chart term) = remaining term := by
  induction term <;> simp_all only [expr, remaining]

theorem eval_expr {s : S} (term : Expr V X s) (old : Env V X) :
    (expr chart term).eval (env chart old) = chart s (term.eval old) := by
  induction term <;>
    simp_all [expr, Expr.eval, env, linear, bilinear, map_add]

theorem effect_expr {s : S} (term : Expr V X s) (old increment : Env V X) :
    (expr chart term).effect (env chart old) (env chart increment) = chart s (term.effect old increment) := by
  have together : env chart old + env chart increment = env chart (old+increment) := by
    funext target name
    exact (map_add (chart target) _ _).symm
  have update := (expr chart term).eval_update (env chart old) (env chart increment)
  rw [together, eval_expr, term.eval_update, map_add, eval_expr] at update
  exact (add_left_cancel update).symm

/-- Rechart each existing formal atom bijectively, retaining its exact integer coefficient. -/
def word (s : S) : Formal ℤ V X s ≃ₗ[ℤ] Formal ℤ W X s :=
  Finsupp.domLCongr (exprEquiv chart s)

theorem coefficient {s : S} (relation : Formal ℤ V X s) (term : Expr V X s) :
    word chart s relation (expr chart term) = relation term := by
  change Finsupp.equivMapDomain (exprEquiv chart s) relation ((exprEquiv chart s) term) = relation term
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]

private theorem word_single {s : S} (term : Expr V X s) (count : ℤ) :
    word chart s (Finsupp.single term count) = Finsupp.single (expr chart term) count :=
  Finsupp.equivMapDomain_single (exprEquiv chart s) term count

/-- Re-express each original typed step, with its actual endpoints and environment. -/
def step {old : Env V X} {s : S} {before after : Expr V X s}
    (paid : Step old before after) :
    Step (env chart old) (expr chart before) (expr chart after) := by
  induction paid with
  | bind name => exact .bind name
  | @addConst sort left right =>
    simpa only [expr, map_add] using
      (Step.addConst (environment := env chart old) (chart sort left) (chart sort right))
  | @linearConst source target operation value =>
    simpa [expr, linear] using
      (Step.linearConst (environment := env chart old) (linear chart operation) (chart source value))
  | @bilinearConst leftSort rightSort target operation left right =>
    simpa [expr, bilinear, linear] using
      (Step.bilinearConst (environment := env chart old) (bilinear chart operation)
        (chart leftSort left) (chart rightSort right))
  | addLeft _ previous => exact .addLeft previous
  | addRight _ previous => exact .addRight previous
  | linear operation _ previous => exact .linear (linear chart operation) previous
  | bilinearLeft operation _ previous => exact .bilinearLeft (bilinear chart operation) previous
  | bilinearRight operation _ previous => exact .bilinearRight (bilinear chart operation) previous

def trace {old : Env V X} {s : S} {before after : Expr V X s}
    (paid : Trace old before after) :
    Trace (env chart old) (expr chart before) (expr chart after) :=
  match paid with
  | .nil term => .nil (expr chart term)
  | .cons first rest => .cons (step chart first) (trace rest)

theorem trace_length {old : Env V X} {s : S} {before after : Expr V X s}
    (paid : Trace old before after) : (trace chart paid).length = paid.length := by
  induction paid <;> simp_all only [trace, Trace.length]

theorem paid_words {old : Env V X} {s : S} {before after : Expr V X s}
    (paid : Trace old before after) :
    SourceOperationPaidRelations.words (trace chart paid) =
      (SourceOperationPaidRelations.words paid).map (word chart s) := by
  induction paid with
  | nil => rfl
  | @cons first middle last _ tail previous =>
    change (Finsupp.single (expr chart first) 1-Finsupp.single (expr chart middle) 1) ::
        SourceOperationPaidRelations.words (trace chart tail) =
      word chart s (Finsupp.single first 1-Finsupp.single middle 1) ::
        (SourceOperationPaidRelations.words tail).map (word chart s)
    rw [map_sub, word_single, word_single, previous]

/-- The two-sided word chart generates the full old/effect square used by the existing coimage. -/
def inventoryMorphism {s : S} (old increment : Env V X) :
    Morphism (updateInventory (R := ℤ) (s := s) old increment)
      (updateInventory (R := ℤ) (s := s) (env chart old) (env chart increment)) where
  sourceMap := (word chart s).toLinearMap
  targetMap := (((chart s).prodCongr (chart s)).toIntLinearEquiv).toLinearMap
  commutes := by
    apply Finsupp.lhom_ext
    intro term count
    change ((chart s).prodCongr (chart s)) (updateInventory (R := ℤ) old increment (Finsupp.single term count)) =
      updateInventory (R := ℤ) (env chart old) (env chart increment) (word chart s (Finsupp.single term count))
    rw [word_single]
    let e : V s ≃ₗ[ℤ] W s := (chart s).toIntLinearEquiv
    change (e (evaluation (R := ℤ) old (Finsupp.single term count)),
      e (effectEvaluator (R := ℤ) old increment (Finsupp.single term count))) =
      (evaluation (R := ℤ) (env chart old) (Finsupp.single (expr chart term) count),
        effectEvaluator (R := ℤ) (env chart old) (env chart increment) (Finsupp.single (expr chart term) count))
    simp only [evaluation, effectEvaluator, Finsupp.linearCombination_single, eval_expr, effect_expr]
    exact Prod.ext (map_smul e count _) (map_smul e count _)

theorem inventory {s : S} (old increment : Env V X) (relation : Formal ℤ V X s) :
    updateInventory (R := ℤ) (env chart old) (env chart increment) (word chart s relation) =
      (chart s (evaluation (R := ℤ) old relation),
        chart s (effectEvaluator (R := ℤ) old increment relation)) :=
  (LinearMap.congr_fun (inventoryMorphism chart old increment).commutes relation).symm

/-- The same full old/effect fibre is read in both coordinates. -/
theorem inventory_fibre {s : S} (old increment : Env V X) (left right : Formal ℤ V X s) :
    canonicalResidual (updateInventory (R := ℤ) (env chart old) (env chart increment)) (word chart s left) =
        canonicalResidual (updateInventory (R := ℤ) (env chart old) (env chart increment)) (word chart s right) ↔
      canonicalResidual (updateInventory (R := ℤ) old increment) left =
        canonicalResidual (updateInventory (R := ℤ) old increment) right := by
  simp only [canonicalResidual, Submodule.mkQ_apply, Submodule.Quotient.eq, LinearMap.mem_ker, ← map_sub]
  rw [inventory]
  let e := (chart s).prodCongr (chart s)
  change e (updateInventory (R := ℤ) old increment (left-right)) = 0 ↔ _
  rw [← map_zero e, e.injective.eq_iff]

end SaturationMonoid.SourceOperationScalarInventoryLift.Rechart
