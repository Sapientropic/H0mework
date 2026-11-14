import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Residual

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineResidualDecision
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineClauses (Clause Formula formulaRead Within)
open AffineClauseProduct (Satisfiable)

/-- Every relation is consumed before the remaining program is rewritten in its generated coordinates. -/
def prepare (n : Nat) (formula : Formula) : Option (Nat × Formula) :=
  let cleaned := AffineClauses.cleanRun formula
  let seed := AffineClauses.Seed.generate cleaned.value
  match seed.value with
  | .contradiction => none
  | .basis basis =>
      let residual := AffineResidual.generate n basis (AffineClauses.Future.body cleaned.value)
      some ((freeIndices n basis).length,residual.value)

theorem prepare_within (n : Nat) (formula : Formula) (width : Nat) (data : Formula)
    (found : prepare n formula=some (width,data)) : Within width data := by
  cases seed : (AffineClauses.Seed.generate (AffineClauses.clean formula)).value with
  | contradiction => simp [prepare,AffineClauses.cleanRun_value,seed] at found
  | basis basis =>
      simp only [prepare,AffineClauses.cleanRun_value,seed,Option.some.injEq,Prod.mk.injEq] at found
      rcases found with ⟨rfl,rfl⟩
      exact AffineResidual.generate_within n basis _

theorem prepare_length (n : Nat) (formula : Formula) (width : Nat) (data : Formula)
    (found : prepare n formula=some (width,data)) : data.length ≤ formula.length := by
  cases seed : (AffineClauses.Seed.generate (AffineClauses.clean formula)).value with
  | contradiction => simp [prepare,AffineClauses.cleanRun_value,seed] at found
  | basis basis =>
      simp only [prepare,AffineClauses.cleanRun_value,seed,Option.some.injEq,Prod.mk.injEq] at found
      rcases found with ⟨rfl,rfl⟩
      exact (AffineResidual.generate_length n basis _).trans
        ((List.length_filter_le _ _).trans (List.length_filter_le _ _))

theorem prepare_possible (n : Nat) (formula : Formula) (inside : Within n formula) :
    (match prepare n formula with | none => False | some (_,data) => Satisfiable data) ↔ Satisfiable formula := by
  have seedValid := AffineClauses.Seed.generate_valid n (AffineClauses.clean formula) (AffineClauses.clean_within n formula inside)
  simp only [prepare,AffineClauses.cleanRun_value]
  cases seed : (AffineClauses.Seed.generate (AffineClauses.clean formula)).value with
  | contradiction =>
      simp only [false_iff]
      rintro ⟨point,accepted⟩
      have inSeed := AffineClauses.Seed.generate_entails (AffineClauses.clean formula) point
        ((AffineClauses.clean_read formula point).trans accepted)
      rw [seed] at inSeed
      cases inSeed
  | basis basis =>
      have valid : Triangular basis ∧ RowsWithin n basis := by simpa only [seed,Result.triangular,Result.within] using seedValid
      dsimp only
      rw [AffineResidual.generate_possible n basis _ valid]
      constructor
      · rintro ⟨point,inBasis,accepted⟩
        refine ⟨extendAssignment point,?_⟩
        have same := AffineClauses.Future.seed_body_read (AffineClauses.clean formula) (extendAssignment point)
        rw [seed,Result.holds,inBasis,accepted,AffineClauses.clean_read] at same
        exact same.symm
      · rintro ⟨point,accepted⟩
        let original : Assignment n := fun i => point i.val
        have finite := (AffineClauseProduct.formula_restrict n formula inside point).trans accepted
        have same := AffineClauses.Future.seed_body_read (AffineClauses.clean formula) (extendAssignment original)
        rw [seed,Result.holds,AffineClauses.clean_read,finite] at same
        exact ⟨original,by simpa only [Bool.and_eq_true] using same⟩

/-- Source component separation is tried again after every affine rewrite. -/
def solve : Nat → Nat → Formula → Bool
  | 0,_,formula => formula.isEmpty
  | fuel+1,n,formula =>
      match prepare n formula with
      | none => false
      | some (width,data) =>
          match data with
          | [] => true
          | clause::rest =>
              let split := AffineClauseProduct.Cost.grow rest.length [clause] rest
              if split.value.2.isEmpty then
                let branches := AffineClauses.clauseAction clause [[]]
                branches.value.any (fun basis =>
                  solve fuel (freeIndices width basis).length (AffineResidual.generate width basis rest).value)
              else solve fuel width split.value.1 && solve fuel width split.value.2



theorem branches_valid (n : Nat) (clause : Clause) (inside : RowsWithin n clause) :
    AffineCarrier.Valid n (AffineClauses.clauseAction clause [[]]).value :=
  AffineClauses.clauseAction_valid n clause inside [[]] (by
    intro basis member
    have same : basis=[] := List.mem_singleton.mp member
    subst basis
    exact ⟨triangular_nil,by simp [RowsWithin]⟩)

theorem branches_read (clause : Clause) (assignment : Nat → Bool) :
    AffineCarrier.read (AffineClauses.clauseAction clause [[]]).value assignment =
      AffineClauses.clauseRead clause assignment := by
  rw [AffineClauses.clauseAction_read]
  simp [AffineCarrier.read,holds]

theorem branches_possible (n : Nat) (clause : Clause) (remaining : Formula) (inside : Within n (clause::remaining)) :
    (∃ basis ∈ (AffineClauses.clauseAction clause [[]]).value,
      Satisfiable (AffineResidual.generate n basis remaining).value) ↔ Satisfiable (clause::remaining) := by
  have valid := branches_valid n clause (inside clause (by simp))
  constructor
  · rintro ⟨basis,member,accepted⟩
    obtain ⟨point,inBasis,inRest⟩ := (AffineResidual.generate_possible n basis remaining (valid basis member)).mp accepted
    have inBranch := AffineCarrier.member_read _ basis member (extendAssignment point) inBasis
    rw [branches_read] at inBranch
    refine ⟨extendAssignment point,?_⟩
    simpa only [formulaRead,List.all_cons,Bool.and_eq_true] using And.intro inBranch inRest
  · rintro ⟨point,accepted⟩
    let original : Assignment n := fun i => point i.val
    have finite := (AffineClauseProduct.formula_restrict n (clause::remaining) inside point).trans accepted
    have facts : AffineClauses.clauseRead clause (extendAssignment original)=true ∧
        formulaRead remaining (extendAssignment original)=true := by
      simpa only [formulaRead,List.all_cons,Bool.and_eq_true] using finite
    have inBranch := (branches_read clause (extendAssignment original)).trans facts.1
    obtain ⟨basis,member,inBasis⟩ := List.any_eq_true.mp inBranch
    exact ⟨basis,member,(AffineResidual.generate_possible n basis remaining (valid basis member)).mpr ⟨original,inBasis,facts.2⟩⟩

theorem solve_correct (fuel n : Nat) (formula : Formula) (inside : Within n formula) (enough : formula.length ≤ fuel) :
    solve fuel n formula=true ↔ Satisfiable formula := by
  induction fuel generalizing n formula with
  | zero =>
      have empty : formula=[] := List.eq_nil_of_length_eq_zero (by omega)
      simp [empty,solve,Satisfiable,formulaRead]
  | succ fuel ih =>
      have spec := prepare_possible n formula inside
      cases prepared : prepare n formula with
      | none => simpa only [solve,prepared,Bool.false_eq_true] using spec
      | some data =>
          obtain ⟨width,data⟩ := data
          simp only [prepared] at spec
          apply Iff.trans ?_ spec
          have bounded := prepare_within n formula width data prepared
          have size := (prepare_length n formula width data prepared).trans enough
          simp only [solve,prepared]
          cases data with
          | nil => simp [Satisfiable,formulaRead]
          | cons clause rest =>
              have restSize : rest.length ≤ fuel := by simp only [List.length_cons] at size; omega
              dsimp only
              split
              · simp only [List.any_eq_true]
                apply Iff.trans ?_ (branches_possible width clause rest bounded)
                constructor
                · rintro ⟨basis,member,accepted⟩
                  exact ⟨basis,member,(ih _ _ (AffineResidual.generate_within width basis rest)
                    ((AffineResidual.generate_length width basis rest).trans restSize)).mp accepted⟩
                · rintro ⟨basis,member,accepted⟩
                  exact ⟨basis,member,(ih _ _ (AffineResidual.generate_within width basis rest)
                    ((AffineResidual.generate_length width basis rest).trans restSize)).mpr accepted⟩
              · rename_i connected
                have nonempty : (AffineClauseProduct.Cost.grow rest.length [clause] rest).value.2 ≠ [] := by
                  intro empty
                  simp [empty] at connected
                have counts := (AffineClauseProduct.Cost.grow_counts rest.length [clause] rest).1
                have positive := List.length_pos_iff.mpr nonempty
                have leftSize : (AffineClauseProduct.Cost.grow rest.length [clause] rest).value.1.length ≤ fuel := by
                  simp only [List.length_singleton] at counts
                  omega
                have rightSize : (AffineClauseProduct.Cost.grow rest.length [clause] rest).value.2.length ≤ fuel := by
                  rw [AffineClauseProduct.Cost.grow_value]
                  exact (AffineClauseProduct.grow_rest_length _ _ _).trans restSize
                have domains := AffineClauseProduct.grow_within width rest.length [clause] rest bounded
                have apart := AffineClauseProduct.grow_apart rest.length [clause] rest (Nat.le_refl _)
                rw [AffineClauseProduct.Cost.grow_value] at leftSize rightSize ⊢
                rw [Bool.and_eq_true,ih _ _ domains.1 leftSize,ih _ _ domains.2 rightSize,
                  ← AffineClauseProduct.separated_sat _ _ apart]
                apply exists_congr
                intro assignment
                simp only [formulaRead,List.all_append]
                exact Iff.of_eq (congrArg (fun b => b=true) (AffineClauseProduct.grow_read clause rest assignment))

def decide (n : Nat) (formula : Formula) : Bool := solve formula.length n formula

theorem decide_correct (n : Nat) (formula : Formula) (inside : Within n formula) :
    decide n formula=true ↔ Satisfiable formula := solve_correct _ n formula inside (Nat.le_refl _)

end SaturationMonoid.ComplexityProjection.SATSource.AffineResidualDecision
