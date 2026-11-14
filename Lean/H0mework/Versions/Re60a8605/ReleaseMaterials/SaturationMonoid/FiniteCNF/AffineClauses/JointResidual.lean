import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.ResidualDecision
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.ResidualCost

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineJointResidual
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineClauses (Clause Formula formulaRead Within)
open AffineClauses.Cost (rowCount termCount)
open AffineClauseProduct (Satisfiable)

/-- Stabilize the variable order before the kernel selects downstream pivots. -/
def canonicalRows (formula : Formula) : Formula := formula.map (fun clause => clause.map Atoms.canonical)

theorem canonical_read (formula : Formula) (assignment : Nat → Bool) :
    formulaRead (canonicalRows formula) assignment=formulaRead formula assignment := by
  simp [canonicalRows,formulaRead,AffineClauses.clauseRead,Function.comp_def,Atoms.canonical_holds]

theorem canonical_possible (formula : Formula) : Satisfiable (canonicalRows formula) ↔ Satisfiable formula := by
  simp only [Satisfiable,canonical_read]

theorem canonical_within (n : Nat) (formula : Formula) (inside : Within n formula) :
    Within n (canonicalRows formula) := by
  intro clause member row present i hit
  obtain ⟨original,inFormula,rfl⟩ := List.mem_map.mp member
  obtain ⟨source,inClause,rfl⟩ := List.mem_map.mp present
  exact inside original inFormula source inClause i
    ((List.mergeSort_perm source.vars _).mem_iff.mp hit)

theorem canonical_length (formula : Formula) : (canonicalRows formula).length=formula.length := by
  simp only [canonicalRows,List.length_map]

theorem canonical_rows (formula : Formula) : rowCount (canonicalRows formula)=rowCount formula := by
  simp [canonicalRows,rowCount,Function.comp_def]

private theorem body_canonical (formula : Formula) :
    AffineClauses.Future.body (canonicalRows formula)=canonicalRows (AffineClauses.Future.body formula) := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      simp only [canonicalRows,List.map_cons,AffineClauses.Future.body,List.filter_cons,List.length_map] at ih ⊢
      split <;> simp_all

/-- The tagged image is retained; an ordered copy of all constraints enters the seed. -/
def generate (_n : Nat) (formula : Formula) : Option (Nat × Formula) :=
  let image := AtomImage.generate (AffineClauseImage.table formula)
  AffineResidualDecision.prepare (AffineClauseImage.width formula)
    (canonicalRows (AffineClauseImage.constraints formula image))

theorem constraints_possible (formula : Formula) :
    Satisfiable (AffineClauseImage.constraints formula
      (AtomImage.generate (AffineClauseImage.table formula))) ↔ Satisfiable formula := by
  constructor
  · rintro ⟨target,accepted⟩
    rw [AffineClauseImage.constraints_read] at accepted
    have facts : CNFFormula.eval (AffineClauseImage.atomFormula formula) target=true ∧
        holds (AtomImage.generate (AffineClauseImage.table formula)).kernel target=true := by
      simpa only [Bool.and_eq_true] using accepted
    let point := AtomImage.decode (AffineClauseImage.table formula) target
    have realized := AtomImage.decode_realizes (AffineClauseImage.table formula) target facts.2
    refine ⟨point,?_⟩
    rw [← AffineClauseImage.atomFormula_read]
    have same : CNFFormula.eval (AffineClauseImage.atomFormula formula)
        (Gates.coordinate (AffineClauseImage.table formula) point) =
        CNFFormula.eval (AffineClauseImage.atomFormula formula) target := by
      apply Factor.formula_eval_agree
      intro clause _ literal _
      exact realized ⟨literal.var.val,by simpa only [AffineClauseImage.table_size] using literal.var.isLt⟩
    exact same.trans facts.1
  · rintro ⟨input,accepted⟩
    refine ⟨Gates.coordinate (AffineClauseImage.table formula) input,?_⟩
    rw [AffineClauseImage.constraints_read,AffineClauseImage.atomFormula_read,accepted]
    have realized := (AtomImage.image_iff_kernel (AffineClauseImage.table formula) _).mp
      ⟨input,fun _ => rfl⟩
    rw [realized]
    rfl

theorem generate_possible (n : Nat) (formula : Formula) (inside : Within n formula) :
    (match generate n formula with | none => False | some (_,data) => Satisfiable data) ↔
      Satisfiable formula :=
  (AffineResidualDecision.prepare_possible _ _
    (canonical_within _ _ (AffineClauseImage.constraints_within n formula inside))).trans
    ((canonical_possible _).trans (constraints_possible formula))

theorem generate_within (n : Nat) (formula : Formula) (width : Nat) (data : Formula)
    (found : generate n formula=some (width,data)) : Within width data :=
  AffineResidualDecision.prepare_within _ _ width data found

private theorem body_append (left right : Formula) :
    AffineClauses.Future.body (left++right) =
      AffineClauses.Future.body left++AffineClauses.Future.body right := by
  simp only [AffineClauses.Future.body,List.filter_append]

private theorem body_singletons (rows : List Row) :
    AffineClauses.Future.body (rows.map (fun row => [row]))=[] := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp [AffineClauses.Future.body] at ih ⊢

private theorem body_singleton_cons (row : Row) (rest : Formula) :
    AffineClauses.Future.body ([row]::rest)=AffineClauses.Future.body rest := by
  simp [AffineClauses.Future.body]

private theorem body_clean (formula : Formula) :
    AffineClauses.Future.body (AffineClauses.clean formula) =
      AffineClauses.clean (AffineClauses.Future.body formula) := by
  simp only [AffineClauses.Future.body,AffineClauses.clean,List.filter_filter,Bool.and_comm]

private theorem body_rows (formula : Formula) :
    rowCount (AffineClauses.Future.body formula) ≤ rowCount formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      simp only [AffineClauses.Future.body] at ih
      simp only [AffineClauses.Future.body,List.filter_cons]
      split <;> simp only [AffineClauses.Cost.rowCount_cons] at * <;> omega

theorem constraints_body_length (formula : Formula) (image : AtomImage.State) :
    (AffineClauses.Future.body (AffineClauseImage.constraints formula image)).length ≤ formula.length := by
  rw [AffineClauseImage.constraints,body_append,body_singletons,List.append_nil]
  simp only [AffineClauseImage.atomFormula,AffineClauseImage.width,AffineClauseImage.liftCNF,
    Atoms.compile,List.map_cons,List.map_nil]
  rw [body_singleton_cons]
  exact (List.length_filter_le _ _).trans_eq (by simp [AffineClauseImage.violations])

theorem constraints_body_rows (formula : Formula) (image : AtomImage.State) :
    rowCount (AffineClauses.Future.body (AffineClauseImage.constraints formula image)) ≤ rowCount formula := by
  rw [AffineClauseImage.constraints,body_append,body_singletons,List.append_nil]
  simp only [AffineClauseImage.atomFormula,AffineClauseImage.width,AffineClauseImage.liftCNF,
    Atoms.compile,List.map_cons,List.map_nil]
  rw [body_singleton_cons]
  apply (body_rows _).trans_eq
  simp [rowCount,AffineClauseImage.violations,Atoms.clause,Function.comp_def]

private theorem prepared_bounds (n : Nat) (formula : Formula) (width : Nat) (data : Formula)
    (found : AffineResidualDecision.prepare n formula=some (width,data)) :
    data.length ≤ (AffineClauses.Future.body formula).length ∧
    rowCount data ≤ rowCount (AffineClauses.Future.body formula) ∧ width ≤ n ∧
    AffineClauses.formulaSize data ≤
      rowCount (AffineClauses.Future.body formula)*(width+2)+(AffineClauses.Future.body formula).length+1 := by
  cases seed : (AffineClauses.Seed.generate (AffineClauses.clean formula)).value with
  | contradiction => simp [AffineResidualDecision.prepare,AffineClauses.cleanRun_value,seed] at found
  | basis basis =>
      simp only [AffineResidualDecision.prepare,AffineClauses.cleanRun_value,seed,
        Option.some.injEq,Prod.mk.injEq] at found
      rcases found with ⟨rfl,rfl⟩
      have length : (AffineClauses.Future.body (AffineClauses.clean formula)).length ≤
          (AffineClauses.Future.body formula).length := by
        rw [body_clean]
        exact List.length_filter_le _ _
      have rows : rowCount (AffineClauses.Future.body (AffineClauses.clean formula)) ≤
          rowCount (AffineClauses.Future.body formula) := by
        rw [body_clean]
        exact AffineResidual.Cost.clean_rows _
      refine ⟨(AffineResidual.generate_length _ _ _).trans length,
        (AffineResidual.Cost.generate_rows _ _ _).trans rows,Table.freeWidth_le n basis,?_⟩
      apply (AffineResidual.Cost.generate_size n basis _).trans
      gcongr

theorem observation_width (formula : Formula) : AffineClauseImage.width formula ≤ rowCount formula+1 := by
  have rows : (AffineClauseImage.violations formula).flatten.length = rowCount formula := by
    simp [AffineClauseImage.violations,List.length_flatten,rowCount,Function.comp_def]
  exact (Atoms.keys_length (AffineClauseImage.violations formula)).trans_eq (by rw [rows])

theorem generate_length (n : Nat) (formula : Formula) (width : Nat) (data : Formula)
    (found : generate n formula=some (width,data)) : data.length ≤ formula.length := by
  have paid := (prepared_bounds _ _ width data found).1
  rw [body_canonical,canonical_length] at paid
  exact paid.trans (constraints_body_length formula _)

theorem generate_rows (n : Nat) (formula : Formula) (width : Nat) (data : Formula)
    (found : generate n formula=some (width,data)) : rowCount data ≤ rowCount formula := by
  have paid := (prepared_bounds _ _ width data found).2.1
  rw [body_canonical,canonical_rows] at paid
  exact paid.trans (constraints_body_rows formula _)

theorem generate_width (n : Nat) (formula : Formula) (width : Nat) (data : Formula)
    (found : generate n formula=some (width,data)) : width ≤ rowCount formula+1 :=
  (prepared_bounds _ _ width data found).2.2.1.trans (observation_width formula)

theorem generate_size (n : Nat) (formula : Formula) (width : Nat) (data : Formula)
    (found : generate n formula=some (width,data)) :
    AffineClauses.formulaSize data ≤ rowCount formula*(rowCount formula+3)+formula.length+1 := by
  have paid := (prepared_bounds _ _ width data found).2.2.2
  rw [body_canonical,canonical_rows,canonical_length] at paid
  have rows := constraints_body_rows formula (AtomImage.generate (AffineClauseImage.table formula))
  have length := constraints_body_length formula (AtomImage.generate (AffineClauseImage.table formula))
  have dimension := generate_width n formula width data found
  have terms := Nat.mul_le_mul rows (show width+2 ≤ rowCount formula+3 by omega)
  omega

end SaturationMonoid.ComplexityProjection.SATSource.AffineJointResidual
