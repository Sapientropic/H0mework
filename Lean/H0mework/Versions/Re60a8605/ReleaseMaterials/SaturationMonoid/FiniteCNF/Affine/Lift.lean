import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Indices

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine

open InterferenceProgram

def Row.bind (row : Row) (assignment : Nat → Bool) : Nat → Bool :=
  match row.vars with
  | [] => assignment
  | p :: tail => Function.update assignment p (row.rhs ^^ Parity.eval assignment tail)

theorem parity_update (vars : List Nat) (assignment : Nat → Bool) (p : Nat) (value : Bool)
    (absent : p ∉ vars) :
    Parity.eval (Function.update assignment p value) vars = Parity.eval assignment vars := by
  apply Parity.eval_congr
  intro i member
  have different : i ≠ p := by rintro rfl; exact absent member
  simp [different]

theorem Row.bind_holds (row : Row) (assignment : Nat → Bool)
    (nodup : row.vars.Nodup) (nonempty : row.vars ≠ []) : row.holds (row.bind assignment) = true := by
  rw [Row.holds_iff]
  cases shape : row.vars with
  | nil => exact False.elim (nonempty shape)
  | cons p tail =>
      have absent : p ∉ tail := (List.nodup_cons.mp (shape ▸ nodup)).1
      simp only [Row.eval, Row.bind, shape, Parity.eval, Function.update_self,
        parity_update tail assignment p _ absent]
      simp

theorem Row.bind_fixes (row : Row) (assignment : Nat → Bool) (accepted : row.holds assignment = true) :
    row.bind assignment = assignment := by
  have satisfies := (row.holds_iff assignment).mp accepted
  cases shape : row.vars with
  | nil => simp [Row.bind, shape]
  | cons p tail =>
      have value : (row.rhs ^^ Parity.eval assignment tail) = assignment p := by
        change Parity.eval assignment row.vars = row.rhs at satisfies
        rw [shape, Parity.eval] at satisfies
        rw [← satisfies]
        simp
      simp only [Row.bind, shape, value, Function.update_eq_self]

theorem Row.bind_other (row other : Row) (assignment : Nat → Bool) (apart : Above row other) :
    other.holds (row.bind assignment) = other.holds assignment := by
  cases shape : row.vars with
  | nil => simp [Row.bind, shape]
  | cons p tail =>
      have absent : p ∉ other.vars := apart p (by simp [shape])
      simp only [Row.holds, Row.eval, Row.bind, shape, parity_update other.vars assignment p _ absent]

def fill (basis : List Row) (assignment : Nat → Bool) : Nat → Bool := basis.foldr Row.bind assignment

theorem fill_holds (basis : List Row) (triangular : Triangular basis) (assignment : Nat → Bool) :
    holds basis (fill basis assignment) = true := by
  induction basis with
  | nil => rfl
  | cons row rest ih =>
      have tail := ih (triangular_tail row rest triangular)
      have first := Row.bind_holds row (fill rest assignment)
        (triangular.1 row (by simp)) (triangular.2.1 row (by simp))
      have later := (List.pairwise_cons.mp triangular.2.2).1
      apply (holds_iff _ _).mpr
      intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact first
      · change other.holds (row.bind (fill rest assignment)) = true
        rw [Row.bind_other row other _ (later other member)]
        exact ((holds_iff _ _).mp tail) other member

theorem fill_fixes (basis : List Row) (assignment : Nat → Bool) (accepted : holds basis assignment = true) :
    fill basis assignment = assignment := by
  induction basis with
  | nil => rfl
  | cons row rest ih =>
      have head := ((holds_iff _ _).mp accepted) row (by simp)
      have tail : holds rest assignment = true := (holds_iff _ _).mpr
        (fun other member => ((holds_iff _ _).mp accepted) other (by simp [member]))
      simp only [fill, List.foldr_cons]
      change row.bind (fill rest assignment) = assignment
      rw [ih tail]
      exact Row.bind_fixes row assignment head

theorem fill_idempotent (basis : List Row) (triangular : Triangular basis) (assignment : Nat → Bool) :
    fill basis (fill basis assignment) = fill basis assignment :=
  fill_fixes basis _ (fill_holds basis triangular assignment)

theorem Row.bind_read (row : Row) (assignment : Nat → Bool) (i : Nat)
    (notPivot : row.vars.head? ≠ some i) : row.bind assignment i = assignment i := by
  cases shape : row.vars with
  | nil => simp [Row.bind, shape]
  | cons p tail =>
      have different : i ≠ p := by
        intro same
        exact notPivot (by simp [shape, same])
      simp [Row.bind, shape, different]

theorem fill_read (basis : List Row) (assignment : Nat → Bool) (i : Nat)
    (notPivot : i ∉ pivots basis) : fill basis assignment i = assignment i := by
  induction basis with
  | nil => rfl
  | cons row rest ih =>
      have head : row.vars.head? ≠ some i := by
        intro same
        exact notPivot ((mem_pivots _ i).mpr ⟨row, by simp, same⟩)
      have tail : i ∉ pivots rest := by
        intro member
        obtain ⟨other, member, same⟩ := (mem_pivots rest i).mp member
        exact notPivot ((mem_pivots _ i).mpr ⟨other, by simp [member], same⟩)
      change row.bind (fill rest assignment) i = assignment i
      rw [Row.bind_read row _ i head, ih tail]

theorem Row.bind_update_absent (row : Row) (assignment : Nat → Bool) (p : Nat) (b : Bool)
    (absent : p ∉ row.vars) :
    row.bind (Function.update assignment p b) = Function.update (row.bind assignment) p b := by
  cases shape : row.vars with
  | nil => simp [Row.bind, shape]
  | cons q tail =>
      have separate : p ≠ q ∧ p ∉ tail := by simpa [shape] using absent
      simp only [Row.bind, shape, parity_update tail assignment p b separate.2]
      exact Function.update_comm separate.1 _ _ _

theorem fill_update_absent (basis : List Row) (assignment : Nat → Bool) (p : Nat) (b : Bool)
    (absent : ∀ row ∈ basis, p ∉ row.vars) :
    fill basis (Function.update assignment p b) = Function.update (fill basis assignment) p b := by
  induction basis with
  | nil => rfl
  | cons row rest ih =>
      have tail : ∀ other ∈ rest, p ∉ other.vars := fun other member => absent other (by simp [member])
      change row.bind (fill rest (Function.update assignment p b)) =
        Function.update (row.bind (fill rest assignment)) p b
      rw [ih tail, Row.bind_update_absent row _ p b (absent row (by simp))]

theorem Row.bind_update_pivot (row : Row) (assignment : Nat → Bool) (p : Nat) (b : Bool)
    (nodup : row.vars.Nodup) (head : row.vars.head? = some p) :
    row.bind (Function.update assignment p b) = row.bind assignment := by
  cases shape : row.vars with
  | nil => simp [shape] at head
  | cons q tail =>
      have same : q = p := by simpa [shape] using head
      subst q
      have absent : p ∉ tail := (List.nodup_cons.mp (shape ▸ nodup)).1
      simp only [Row.bind, shape, parity_update tail assignment p b absent, Function.update_idem]

theorem fill_update_pivot (basis : List Row) (triangular : Triangular basis)
    (assignment : Nat → Bool) (p : Nat) (b : Bool) (member : p ∈ pivots basis) :
    fill basis (Function.update assignment p b) = fill basis assignment := by
  induction basis with
  | nil => simp [pivots] at member
  | cons row rest ih =>
      obtain ⟨owner, ownerMember, head⟩ := (mem_pivots _ p).mp member
      rcases List.mem_cons.mp ownerMember with same | ownerMember
      · subst owner
        have later := (List.pairwise_cons.mp triangular.2.2).1
        have absent : ∀ other ∈ rest, p ∉ other.vars := fun other member => later other member p head
        change row.bind (fill rest (Function.update assignment p b)) = row.bind (fill rest assignment)
        rw [fill_update_absent rest assignment p b absent]
        exact Row.bind_update_pivot row _ p b (triangular.1 row (by simp)) head
      · change row.bind (fill rest (Function.update assignment p b)) = row.bind (fill rest assignment)
        rw [ih (triangular_tail row rest triangular) ((mem_pivots rest p).mpr ⟨owner, ownerMember, head⟩)]

def restore (indices : List Nat) (target seed : Nat → Bool) : Nat → Bool :=
  indices.foldl (fun current i => Function.update current i (target i)) seed

theorem restore_read (indices : List Nat) (target seed : Nat → Bool) (i : Nat) :
    restore indices target seed i = if i ∈ indices then target i else seed i := by
  induction indices generalizing seed with
  | nil => simp [restore]
  | cons p rest ih =>
      change restore rest target (Function.update seed p (target p)) i = _
      rw [ih]
      by_cases later : i ∈ rest
      · simp [later]
      · by_cases same : i = p <;> simp [later, same]

theorem fill_restore (basis : List Row) (triangular : Triangular basis) (indices : List Nat)
    (inside : ∀ i ∈ indices, i ∈ pivots basis) (target seed : Nat → Bool) :
    fill basis (restore indices target seed) = fill basis seed := by
  induction indices generalizing seed with
  | nil => rfl
  | cons p rest ih =>
      change fill basis (restore rest target (Function.update seed p (target p))) = _
      rw [ih (fun i member => inside i (by simp [member])),
        fill_update_pivot basis triangular seed p (target p) (inside p (by simp))]

theorem fill_congr (basis : List Row) (triangular : Triangular basis) (left right : Nat → Bool)
    (agree : ∀ i, i ∉ pivots basis → left i = right i) : fill basis left = fill basis right := by
  have recover : restore (pivots basis) right left = right := by
    funext i
    rw [restore_read]
    split
    · rfl
    · exact agree i ‹_›
  rw [← recover, fill_restore basis triangular (pivots basis) (fun _ member => member)]

theorem fill_recovers (basis : List Row) (triangular : Triangular basis) (seed target : Nat → Bool)
    (accepted : holds basis target = true)
    (agree : ∀ i, i ∉ pivots basis → seed i = target i) : fill basis seed = target := by
  rw [fill_congr basis triangular seed target agree, fill_fixes basis target accepted]

def freeSeed (n : Nat) (basis : List Row) (parameters : Nat → Bool) : Nat → Bool :=
  let free := freeIndices n basis
  fun i => if i ∈ free then parameters (free.idxOf i) else false

def projectFree (n : Nat) (basis : List Row) (assignment : Assignment n) :
    Assignment (freeIndices n basis).length := fun i => assignment (freeVariable n basis i)

def parameterLift (n : Nat) (basis : List Row)
    (parameters : Assignment (freeIndices n basis).length) : Assignment n :=
  fun i => fill basis (freeSeed n basis (extendAssignment parameters)) i.val

theorem freeSeed_outside (n : Nat) (basis : List Row) (parameters : Nat → Bool) (i : Nat)
    (outside : ¬ i < n) : freeSeed n basis parameters i = false := by
  have absent : i ∉ freeIndices n basis := fun member => outside (freeIndices_within n basis i member)
  simp [freeSeed, absent]

theorem extend_parameterLift (n : Nat) (basis : List Row) (inside : RowsWithin n basis)
    (parameters : Assignment (freeIndices n basis).length) :
    extendAssignment (parameterLift n basis parameters) =
      fill basis (freeSeed n basis (extendAssignment parameters)) := by
  funext i
  by_cases valid : i < n
  · simp [extendAssignment, valid, parameterLift]
  · have notPivot : i ∉ pivots basis := fun member => valid (pivots_within n basis inside i member)
    rw [fill_read basis _ i notPivot, freeSeed_outside n basis _ i valid]
    simp [extendAssignment, valid]

theorem parameterLift_holds (n : Nat) (basis : List Row) (triangular : Triangular basis)
    (inside : RowsWithin n basis) (parameters : Assignment (freeIndices n basis).length) :
    holds basis (extendAssignment (parameterLift n basis parameters)) = true := by
  rw [extend_parameterLift n basis inside]
  exact fill_holds basis triangular _

theorem freeSeed_projectFree (n : Nat) (basis : List Row) (assignment : Assignment n) (i : Nat)
    (notPivot : i ∉ pivots basis) :
    freeSeed n basis (extendAssignment (projectFree n basis assignment)) i =
      extendAssignment assignment i := by
  by_cases valid : i < n
  · have member := (mem_freeIndices n basis i).mpr ⟨valid, notPivot⟩
    have address := (freeAddress n basis i member).isLt
    simp only [freeSeed, if_pos member]
    change extendAssignment (projectFree n basis assignment) (freeAddress n basis i member).val = _
    rw [extendAssignment_apply]
    change assignment (freeVariable n basis (freeAddress n basis i member)) = _
    have same : freeVariable n basis (freeAddress n basis i member) = ⟨i, valid⟩ := by
      apply Fin.ext
      exact free_get_address n basis i member
    rw [same]
    simp [extendAssignment, valid]
  · rw [freeSeed_outside n basis _ i valid]
    simp [extendAssignment, valid]

theorem parameterLift_projectFree (n : Nat) (basis : List Row) (triangular : Triangular basis)
    (assignment : Assignment n) (accepted : holds basis (extendAssignment assignment) = true) :
    parameterLift n basis (projectFree n basis assignment) = assignment := by
  have recovered := fill_recovers basis triangular
    (freeSeed n basis (extendAssignment (projectFree n basis assignment)))
    (extendAssignment assignment) accepted (freeSeed_projectFree n basis assignment)
  funext i
  change fill basis _ i.val = assignment i
  rw [recovered, extendAssignment_apply]

theorem projectFree_parameterLift (n : Nat) (basis : List Row)
    (parameters : Assignment (freeIndices n basis).length) :
    projectFree n basis (parameterLift n basis parameters) = parameters := by
  funext i
  have member : (freeIndices n basis).get i ∈ freeIndices n basis := List.get_mem _ i
  have notPivot := ((mem_freeIndices n basis _).mp member).2
  change fill basis (freeSeed n basis (extendAssignment parameters)) ((freeIndices n basis).get i) = _
  rw [fill_read basis _ _ notPivot]
  simp only [freeSeed, if_pos member, free_idxOf_get, extendAssignment_apply]

theorem parameterLift_injective (n : Nat) (basis : List Row) :
    Function.Injective (parameterLift n basis) := by
  intro left right same
  rw [← projectFree_parameterLift n basis left, ← projectFree_parameterLift n basis right, same]

theorem parameterLift_image (n : Nat) (basis : List Row) (triangular : Triangular basis)
    (inside : RowsWithin n basis) (assignment : Assignment n) :
    (∃ parameters, parameterLift n basis parameters = assignment) ↔
      holds basis (extendAssignment assignment) = true := by
  constructor
  · rintro ⟨parameters, rfl⟩
    exact parameterLift_holds n basis triangular inside parameters
  · intro accepted
    exact ⟨projectFree n basis assignment, parameterLift_projectFree n basis triangular assignment accepted⟩

theorem extracted_parameterLift_image {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : eliminate (Extract.extract formula) = .basis basis) (assignment : Assignment n) :
    (∃ parameters, parameterLift n basis parameters = assignment) ↔
      holds (Extract.extract formula) (extendAssignment assignment) = true := by
  have triangular := eliminate_triangular (Extract.extract formula)
  rw [generated] at triangular
  rw [parameterLift_image n basis triangular (extracted_basis_within formula basis generated),
    basis_solutions (Extract.extract formula) basis generated]

end SaturationMonoid.ComplexityProjection.SATSource.Affine
