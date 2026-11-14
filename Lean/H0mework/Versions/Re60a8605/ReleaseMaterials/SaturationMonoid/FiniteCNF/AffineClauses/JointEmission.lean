import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.BinaryContext

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineJointEmission
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineClauses (Formula formulaRead Within)

structure Output (n : Nat) where
  private mk ::
  query : CNFFormula n
  context : List Row
  strong : Result
  queries : Nat
  deriving Repr

/-- One enhancement supplies both the emitted query and the actual strong-row generation. -/
def emit {n : Nat} (formula : CNFFormula n) (context : List Row) : Output n :=
  let enhanced := AffineBinaryContext.generate formula context
  let extracted := Extract.extract enhanced.formula
  let prepared := CapacityMatching.RowCost.prepare enhanced.formula
  let strong := TightFeedback.generate enhanced.formula (context++extracted++prepared.value)
  ⟨enhanced.formula,context,strong,enhanced.queries⟩

theorem emit_query {n : Nat} (formula : CNFFormula n) (context : List Row) :
    (emit formula context).query=(AffineBinaryContext.generate formula context).formula := rfl

theorem emit_context {n : Nat} (formula : CNFFormula n) (context : List Row) :
    (emit formula context).context=context := rfl

theorem emit_strong {n : Nat} (formula : CNFFormula n) (context : List Row) :
    (emit formula context).strong=AffineBinaryContext.seed formula context := rfl

def read {n : Nat} (output : Output n) (assignment : Nat → Bool) : Bool :=
  CNFFormula.eval output.query assignment && holds output.context assignment && output.strong.holds assignment

theorem emit_read {n : Nat} (formula : CNFFormula n) (context : List Row) (assignment : Nat → Bool) :
    read (emit formula context) assignment =
      (CNFFormula.eval formula assignment && holds context assignment) := by
  simp only [read,emit_query,emit_context,emit_strong,AffineBinaryContext.generate_value]
  exact AffineBinaryContext.seed_preserves formula context assignment

def Bounded {n : Nat} (output : Output n) : Prop :=
  output.strong.triangular ∧ output.strong.within n ∧ RowsWithin n output.context

theorem emit_bounded {n : Nat} (formula : CNFFormula n) (context : List Row) (inside : RowsWithin n context) :
    Bounded (emit formula context) :=
  ⟨(AffineBinaryContext.seed_valid formula context inside).1,
    (AffineBinaryContext.seed_valid formula context inside).2,inside⟩

theorem emit_length {n : Nat} (formula : CNFFormula n) (context : List Row) :
    (emit formula context).query.length ≤ formula.length+4*n*n := AffineBinaryContext.generate_length _ _

theorem emit_literals {n : Nat} (formula : CNFFormula n) (context : List Row) :
    Extract.literalCount (emit formula context).query ≤ Extract.literalCount formula+8*n*n :=
  AffineBinaryContext.generate_literals _ _

theorem emit_queries {n : Nat} (formula : CNFFormula n) (context : List Row) :
    (emit formula context).queries ≤ 16*n^4 := AffineBinaryContext.generate_queries _ _

theorem emit_source_read (formula : Formula) (input : Nat → Bool) :
    read (emit (AffineClauseImage.atomFormula formula)
      (AtomImage.generate (AffineClauseImage.table formula)).kernel)
      (Gates.coordinate (AffineClauseImage.table formula) input)=formulaRead formula input := by
  rw [emit_read,AffineClauseImage.atomFormula_read]
  have realized := (AtomImage.image_iff_kernel (AffineClauseImage.table formula) _).mp ⟨input,fun _ => rfl⟩
  rw [realized,Bool.and_true]

theorem emit_source_bounded (n : Nat) (formula : Formula) (inside : Within n formula) :
    Bounded (emit (AffineClauseImage.atomFormula formula)
      (AtomImage.generate (AffineClauseImage.table formula)).kernel) := by
  apply emit_bounded
  intro row member
  have bounded := ((AtomImage.generate_valid n (AffineClauseImage.table formula)
    (AffineClauseImage.source_within n formula inside)).2 row member).2
  simpa only [AffineClauseImage.table_size] using bounded

/-- The emitted query acts together with its actual context and strong affine relations. -/
def constraints {n : Nat} (output : Output n) : Formula :=
  match output.strong with
  | .contradiction => [[]]
  | .basis basis => AffineClauseImage.liftCNF output.query++(output.context++basis).map (fun row => [row])

theorem constraints_read {n : Nat} (output : Output n) (assignment : Nat → Bool) :
    formulaRead (constraints output) assignment=read output assignment := by
  cases strong : output.strong with
  | contradiction => simp [constraints,strong,read,Result.holds,formulaRead,AffineClauses.clauseRead]
  | basis basis =>
      simp only [constraints,strong,formulaRead,List.all_append,List.all_map,Function.comp_def]
      change (formulaRead (AffineClauseImage.liftCNF output.query) assignment &&
        (output.context.all (fun row => AffineClauses.clauseRead [row] assignment) &&
          basis.all (fun row => AffineClauses.clauseRead [row] assignment)))=_
      rw [AffineClauseImage.liftCNF_read]
      simp [read,strong,Result.holds,holds,AffineClauses.clauseRead,Bool.and_assoc]

theorem constraints_within {n : Nat} (output : Output n) (bounded : Bounded output) :
    Within n (constraints output) := by
  cases strong : output.strong with
  | contradiction => simp [constraints,strong,Within,RowsWithin]
  | basis basis =>
      have inside : RowsWithin n basis := by simpa only [strong,Result.within] using bounded.2.1
      intro clause member
      simp only [constraints,strong] at member
      rcases List.mem_append.mp member with query | rows
      · exact AffineClauseImage.liftCNF_within output.query clause query
      · obtain ⟨row,rowMember,rfl⟩ := List.mem_map.mp rows
        intro other present
        have same : other=row := List.mem_singleton.mp present
        subst other
        rcases List.mem_append.mp rowMember with original | generated
        · exact bounded.2.2 row original
        · exact inside row generated

theorem constraints_body_sublist {n : Nat} (output : Output n) :
    List.Sublist ((constraints output).filter (fun clause => decide (2 ≤ clause.length)))
      ((AffineClauseImage.liftCNF output.query).filter (fun clause => decide (2 ≤ clause.length))) := by
  have singletons (rows : List Row) :
      ((rows.map (fun row => [row])).filter (fun clause => decide (2 ≤ clause.length)))=[] := by
    induction rows <;> simp_all
  cases strong : output.strong with
  | contradiction => simp [constraints,strong]
  | basis basis =>
      simp only [constraints,strong,List.filter_append,singletons,List.append_nil]
      exact List.Sublist.refl _

theorem constraints_body_length {n : Nat} (output : Output n) :
    ((constraints output).filter (fun clause => decide (2 ≤ clause.length))).length ≤ output.query.length := by
  have bound := (constraints_body_sublist output).length_le
  have filtered := List.length_filter_le (fun clause => decide (2 ≤ clause.length)) (AffineClauseImage.liftCNF output.query)
  simpa only [AffineClauseImage.liftCNF,List.length_map] using bound.trans filtered

theorem constraints_body_rows {n : Nat} (output : Output n) :
    ((constraints output).filter (fun clause => decide (2 ≤ clause.length))).flatten.length ≤
      Extract.literalCount output.query := by
  have body : List.Sublist ((AffineClauseImage.liftCNF output.query).filter (fun clause => decide (2 ≤ clause.length)))
      (AffineClauseImage.liftCNF output.query) := List.filter_sublist
  have bound := ((constraints_body_sublist output).trans body).flatten.length_le
  simpa [AffineClauseImage.liftCNF,List.length_flatten,Extract.literalCount,Function.comp_def] using bound

end SaturationMonoid.ComplexityProjection.SATSource.AffineJointEmission
