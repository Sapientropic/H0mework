import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Shared

/-! Source-generated support and syntactic implication shrink the actual SAT frontier. -/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Shared

def sourceVars {n : Nat} (formula : CNFFormula n) : List (Fin n) :=
  (formula.flatten.map CNFLiteral.var).dedup

theorem sourceVars_supported {n : Nat} (formula : CNFFormula n) :
    SupportedBy formula (sourceVars formula) := by
  intro clause hc lit hl
  simp only [sourceVars, List.mem_dedup, List.mem_map]
  exact ⟨lit, List.mem_flatten.mpr ⟨clause, hc, hl⟩, rfl⟩

theorem sourceVars_length_le {n : Nat} (formula : CNFFormula n) :
    (sourceVars formula).length ≤ formula.flatten.length := by
  exact (List.dedup_sublist _).length_le.trans_eq (List.length_map ..)

def subsumes {n : Nat} (easier harder : CNFFormula n) : Bool :=
  easier.all fun clause => decide (clause ∈ harder)

theorem subsumes_sat {n : Nat} (easier harder : CNFFormula n)
    (hsub : subsumes easier harder = true) (hs : CNFSatisfiable harder) :
    CNFSatisfiable easier := by
  obtain ⟨assignment, hs⟩ := hs
  refine ⟨assignment, ?_⟩
  rw [CNFFormula.eval, List.all_eq_true] at hs ⊢
  intro clause hc
  exact hs clause (of_decide_eq_true ((List.all_eq_true.mp hsub) clause hc))

def prune {n : Nat} : List (CNFFormula n) → List (CNFFormula n)
  | [] => []
  | formula :: rest =>
      let tail := prune rest
      if tail.any (fun easier => subsumes easier formula) then tail else formula :: tail

theorem prune_subset {n : Nat} (frontier : List (CNFFormula n)) :
    prune frontier ⊆ frontier := by
  induction frontier with
  | nil => exact List.Subset.refl _
  | cons formula rest ih =>
      intro f hf
      simp only [prune] at hf
      split at hf
      · exact List.mem_cons_of_mem _ (ih hf)
      · rcases List.mem_cons.mp hf with rfl | hf
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih hf)

theorem prune_live {n : Nat} (frontier : List (CNFFormula n)) :
    live (prune frontier) ↔ live frontier := by
  induction frontier with
  | nil => rfl
  | cons formula rest ih =>
      constructor
      · rintro ⟨f, hf, hs⟩
        exact ⟨f, prune_subset _ hf, hs⟩
      · rintro ⟨f, hf, hs⟩
        simp only [prune]
        rcases List.mem_cons.mp hf with rfl | hf
        · split
          · rename_i habsorb
            obtain ⟨easier, he, hsub⟩ := List.any_eq_true.mp habsorb
            exact ⟨easier, he, subsumes_sat easier f hsub hs⟩
          · exact ⟨f, List.mem_cons_self, hs⟩
        · have hr := ih.mpr ⟨f, hf, hs⟩
          split
          · exact hr
          · obtain ⟨g, hg, hgs⟩ := hr
            exact ⟨g, List.mem_cons_of_mem _ hg, hgs⟩

def runPruned {n : Nat} : List (Fin n) → List (CNFFormula n) → List (CNFFormula n)
  | [], frontier => frontier
  | v :: vars, frontier => runPruned vars (prune (advance frontier v))

theorem runPruned_live {n : Nat} (vars : List (Fin n))
    (frontier : List (CNFFormula n)) : live (runPruned vars frontier) ↔ live frontier := by
  induction vars generalizing frontier with
  | nil => rfl
  | cons v vars ih =>
      exact (ih _).trans ((prune_live _).trans (advance_live frontier v))

theorem runPruned_supported {n : Nat} (vars : List (Fin n))
    (frontier : List (CNFFormula n))
    (hs : ∀ formula ∈ frontier, SupportedBy formula vars) :
    ∀ formula ∈ runPruned vars frontier, SupportedBy formula [] := by
  induction vars generalizing frontier with
  | nil => exact hs
  | cons v vars ih =>
      apply ih
      intro formula hf
      exact advance_supported frontier v vars hs formula (prune_subset _ hf)

def decideSource {n : Nat} (formula : CNFFormula n) : Bool :=
  (runPruned (sourceVars formula) [formula]).any
    fun residual => CNFFormula.eval residual (fun _ => false)

theorem decideSource_correct {n : Nat} (formula : CNFFormula n) :
    decideSource formula = true ↔ CNFSatisfiable formula := by
  have hsupport : ∀ f ∈ runPruned (sourceVars formula) [formula], SupportedBy f [] := by
    apply runPruned_supported
    intro f hf
    obtain rfl := List.mem_singleton.mp hf
    exact sourceVars_supported f
  have hread : decideSource formula = true ↔
      live (runPruned (sourceVars formula) [formula]) := by
    change (List.any _ _) = true ↔ _
    rw [List.any_eq_true]
    constructor
    · rintro ⟨f, hf, hs⟩
      exact ⟨f, hf, ⟨fun _ => false, hs⟩⟩
    · rintro ⟨f, hf, assignment, hs⟩
      exact ⟨f, hf, (eval_eq_of_supported_nil f (hsupport f hf)
        assignment (fun _ => false)) ▸ hs⟩
  rw [hread, runPruned_live]
  simp only [live, List.mem_singleton, exists_eq_left]

theorem decideSource_no {n : Nat} (formula : CNFFormula n) :
    decideSource formula = false ↔ ¬ CNFSatisfiable formula := by
  rw [Bool.eq_false_iff]
  exact not_congr (decideSource_correct formula)

end SaturationMonoid.ComplexityProjection.SATSource.Shared
