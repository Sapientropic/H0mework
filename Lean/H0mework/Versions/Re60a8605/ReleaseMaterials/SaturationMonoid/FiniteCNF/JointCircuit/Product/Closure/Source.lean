import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Product.Cost

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ProductClosure
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)

def table (frame : Frame) (keep : Nat) (basis : List Row) : Array Row :=
  let source := Table.coordinates frame.state.arena.code.size basis
  Array.ofFn (fun i : Fin keep => source.getD (PortEmbedding.ref frame.state frame.ports i.val).val Gates.zeroRow)

theorem table_size (frame : Frame) (keep : Nat) (basis : List Row) : (table frame keep basis).size=keep := by simp only [table,Array.size_ofFn]

theorem table_valid (frame : Frame) (keep : Nat) (basis : List Row) :
    Table.Valid frame.state.arena.code.size (table frame keep basis) := by
  intro row member
  simp only [table,Array.toList_ofFn,List.mem_ofFn] at member
  obtain ⟨i,rfl⟩ := member
  have original := Table.read_valid _ _ (Table.coordinates_valid frame.state.arena.code.size basis)
    (PortEmbedding.ref frame.state frame.ports i.val).val
  exact PortCost.rowValid_mono _ _ _ original (Table.freeWidth_le _ _)

theorem table_realizes (frame : Frame) (keep : Nat) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis) (point : Nat → Bool)
    (accepted : holds basis (JointCircuit.lift frame.state point)=true) :
    AtomImage.Realizes (table frame keep basis)
      (PortRelations.parameters frame.state.arena.code.size basis (JointCircuit.lift frame.state point)) (frame.read point) := by
  intro i
  have inside : i.val < keep := by simpa only [table_size] using i.isLt
  rw [Table.coordinate_getD]
  have source : (table frame keep basis).getD i.val Gates.zeroRow=
      (Table.coordinates frame.state.arena.code.size basis).getD (PortEmbedding.ref frame.state frame.ports i.val).val Gates.zeroRow := by
    simp [table,Array.getD,inside]
  rw [source,PortRelations.coordinate_recover _ basis valid _ accepted]
  rfl

def project (frame : Frame) (keep : Nat) (basis : List Row) : List Row := (AtomImage.generate (table frame keep basis)).kernel

theorem project_holds (frame : Frame) (keep : Nat) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis) (point : Nat → Bool)
    (accepted : holds basis (JointCircuit.lift frame.state point)=true) : holds (project frame keep basis) (frame.read point)=true :=
  (AtomImage.image_iff_kernel _ _).mp ⟨PortRelations.parameters _ basis (JointCircuit.lift frame.state point),table_realizes frame keep basis valid point accepted⟩

theorem project_valid (frame : Frame) (keep : Nat) (basis : List Row) (row : Row) (member : row ∈ project frame keep basis) :
    Table.RowValid keep row := by
  have source := (AtomImage.generate_valid frame.state.arena.code.size (table frame keep basis)
    (fun row member => (table_valid frame keep basis row member).2)).2 row member
  simpa only [table_size] using source

theorem project_count (frame : Frame) (keep : Nat) (basis : List Row) : (project frame keep basis).length ≤ keep := by
  have count := AtomImage.generate_count (table frame keep basis)
  rw [table_size] at count
  change _+(project frame keep basis).length=keep at count
  omega

theorem project_storage (frame : Frame) (keep : Nat) (basis : List Row) :
    CapacityMatching.RowCost.rowsCells (project frame keep basis) ≤ keep*(keep+2) :=
  (AffineClauses.Cost.source_storage keep _ (project_valid frame keep basis)).trans (by gcongr; exact project_count frame keep basis)

def frame (state : ArenaSource.State) : Frame := ProductBatch.generate (PortEmbedding.initial state)

def consequences (state : ArenaSource.State) (basis : List Row) : List Row :=
  let projected := project (frame state) state.arena.code.size basis
  ProductSource.rows (PortEmbedding.initial state) projected

theorem project_original (state : ArenaSource.State) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin (frame state).state.arena.code.size basis) (point : Nat → Bool)
    (accepted : holds basis (JointCircuit.lift (frame state).state point)=true) :
    holds (project (frame state) state.arena.code.size basis) ((PortEmbedding.initial state).read point)=true := by
  have source := project_holds (frame state) state.arena.code.size basis valid point accepted
  apply (holds_iff _ _).mpr
  intro row member
  have first := (holds_iff _ _).mp source row member
  have within := (project_valid (frame state) state.arena.code.size basis row member).2
  have same := Parity.eval_congr (fun i => (frame state).read point i) ((PortEmbedding.initial state).read point) row.vars
    (fun i hit => ProductBatch.generate_old (PortEmbedding.initial state) point i (by rw [PortEmbedding.initial_size]; exact within i hit))
  simpa only [Row.holds,Row.eval,same] using first

theorem consequences_holds (state : ArenaSource.State) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin (frame state).state.arena.code.size basis) (point : Nat → Bool)
    (accepted : holds basis (JointCircuit.lift (frame state).state point)=true) :
    holds (consequences state basis) ((frame state).read point)=true := by
  have original := project_original state basis valid point accepted
  apply ProductRows.rows_holds (PortEmbedding.initial state) _ _ point original
  intro row member
  rw [PortEmbedding.initial_size]
  exact (project_valid (frame state) state.arena.code.size basis row member).2

theorem consequences_storage (state : ArenaSource.State) (basis : List Row) :
    CapacityMatching.RowCost.rowsCells (consequences state basis) ≤
      state.arena.code.size*(state.arena.code.size*(state.arena.code.size+2)+state.arena.code.size) := by
  have source := ProductRows.multiplyRows_storage (PortEmbedding.initial state) (project (frame state) state.arena.code.size basis)
  rw [PortEmbedding.initial_size] at source
  have count := project_count (frame state) state.arena.code.size basis
  have storage := project_storage (frame state) state.arena.code.size basis
  exact source.trans (by gcongr)

def step (state : ArenaSource.State) : Result → Result
  | .contradiction => .contradiction
  | .basis basis => Affine.eliminateFrom (.basis basis)
      ((consequences state basis).map (ProductRows.mapped (frame state)))

theorem step_holds (state : ArenaSource.State) (result : Result)
    (valid : result.triangular ∧ result.within (frame state).state.arena.code.size) (point : Nat → Bool) :
    (step state result).holds (JointCircuit.lift (frame state).state point)=result.holds (JointCircuit.lift (frame state).state point) := by
  cases result with
  | contradiction => rfl
  | basis basis =>
      rw [step,Affine.eliminateFrom_holds]
      by_cases accepted : holds basis (JointCircuit.lift (frame state).state point)=true
      · have generated := consequences_holds state basis valid point accepted
        have mapped : holds ((consequences state basis).map (ProductRows.mapped (frame state))) (JointCircuit.lift (frame state).state point)=true := by
          simp only [holds,List.all_map,Function.comp_def,ProductRows.mapped_holds]
          exact generated
        simp only [Result.holds,accepted,mapped,Bool.and_self]
      · simp only [Result.holds,Bool.eq_false_iff.mpr accepted,Bool.false_and]

theorem step_valid (state : ArenaSource.State) (result : Result)
    (valid : result.triangular ∧ result.within (frame state).state.arena.code.size) :
    (step state result).triangular ∧ (step state result).within (frame state).state.arena.code.size := by
  cases result with
  | contradiction => exact valid
  | basis basis =>
      exact ⟨eliminateFrom_triangular _ valid.1 _,eliminateFrom_within _ _ valid.2 _ (by
        intro row member
        obtain ⟨old,_,rfl⟩ := List.mem_map.mp member
        exact ProductRows.mapped_within _ _)⟩

theorem step_progress (state : ArenaSource.State) (result : Result)
    (valid : result.triangular ∧ result.within (frame state).state.arena.code.size) (changed : step state result≠result) :
    Propagation.remaining (frame state).state.arena.code.size (step state result)<Propagation.remaining (frame state).state.arena.code.size result := by
  cases result with
  | contradiction => exact False.elim (changed rfl)
  | basis basis =>
      have original := basis_length_le (frame state).state.arena.code.size basis valid.1 valid.2
      cases generated : step state (.basis basis) with
      | contradiction => simp only [Propagation.remaining]; omega
      | basis next =>
          have pref := Atoms.eliminateFrom_prefix basis ((consequences state basis).map (ProductRows.mapped (frame state))) next generated
          have longer : basis.length < next.length := by
            have length := pref.length_le
            by_contra shorter
            have same : basis=next := pref.eq_of_length_le (by omega)
            apply changed
            rw [generated,same]
          have known := step_valid state (.basis basis) valid
          have nextValid : Triangular next ∧ RowsWithin (frame state).state.arena.code.size next := by
            simpa only [generated,Result.triangular,Result.within] using known
          have rank := basis_length_le (frame state).state.arena.code.size next nextValid.1 nextValid.2
          simp only [Propagation.remaining]
          omega

def iterate (state : ArenaSource.State) : Nat → Result → Result
  | 0,result => result
  | fuel+1,result =>
      let next := step state result
      if next=result then result else iterate state fuel next

theorem iterate_holds (state : ArenaSource.State) (fuel : Nat) (result : Result)
    (valid : result.triangular ∧ result.within (frame state).state.arena.code.size) (point : Nat → Bool) :
    (iterate state fuel result).holds (JointCircuit.lift (frame state).state point)=result.holds (JointCircuit.lift (frame state).state point) := by
  induction fuel generalizing result with
  | zero => rfl
  | succ fuel ih =>
      simp only [iterate]
      split
      · rfl
      · exact (ih _ (step_valid state result valid)).trans (step_holds state result valid point)

theorem iterate_valid (state : ArenaSource.State) (fuel : Nat) (result : Result)
    (valid : result.triangular ∧ result.within (frame state).state.arena.code.size) :
    (iterate state fuel result).triangular ∧ (iterate state fuel result).within (frame state).state.arena.code.size := by
  induction fuel generalizing result with
  | zero => exact valid
  | succ fuel ih =>
      simp only [iterate]
      split
      · exact valid
      · exact ih _ (step_valid state result valid)

theorem iterate_settled (state : ArenaSource.State) (fuel : Nat) (result : Result)
    (valid : result.triangular ∧ result.within (frame state).state.arena.code.size)
    (enough : Propagation.remaining (frame state).state.arena.code.size result ≤ fuel) :
    step state (iterate state fuel result)=iterate state fuel result := by
  induction fuel generalizing result with
  | zero =>
      cases result with
      | contradiction => rfl
      | basis basis =>
          have rank := basis_length_le _ basis valid.1 valid.2
          simp only [Propagation.remaining] at enough
          omega
  | succ fuel ih =>
      simp only [iterate]
      split
      · assumption
      · rename_i changed
        have less := step_progress state result valid changed
        exact ih _ (step_valid state result valid) (by omega)

def run (state : ArenaSource.State) (result : Result) : Result :=
  iterate state ((frame state).state.arena.code.size+1) result

theorem run_holds (state : ArenaSource.State) (result : Result)
    (valid : result.triangular ∧ result.within (frame state).state.arena.code.size) (point : Nat → Bool) :
    (run state result).holds (JointCircuit.lift (frame state).state point)=result.holds (JointCircuit.lift (frame state).state point) :=
  iterate_holds state _ result valid point

theorem run_settled (state : ArenaSource.State) (result : Result)
    (valid : result.triangular ∧ result.within (frame state).state.arena.code.size) : step state (run state result)=run state result := by
  apply iterate_settled state _ result valid
  cases result <;> simp only [Propagation.remaining] <;> omega

def initial (state : ArenaSource.State) : Result :=
  ProductRows.analyze (frame state) (ProductRows.prepare state).rows

theorem initial_valid (state : ArenaSource.State) :
    (initial state).triangular ∧ (initial state).within (frame state).state.arena.code.size := ProductRows.analyze_valid _ _

def generate (state : ArenaSource.State) : Result := run state (initial state)

theorem generate_holds (state : ArenaSource.State) (point : Nat → Bool) (accepted : JointCircuit.read state point=true) :
    (generate state).holds (JointCircuit.lift (frame state).state point)=true := by
  rw [generate,run_holds state _ (initial_valid state),initial,ProductRows.analyze_holds]
  have source := ProductRows.prepare_holds state point
  rw [ProductRows.prepare_frame] at source
  exact source ((ProductBatch.generate_read (PortEmbedding.initial state) point).trans accepted)

theorem generate_valid (state : ArenaSource.State) :
    (generate state).triangular ∧ (generate state).within (frame state).state.arena.code.size :=
  iterate_valid state _ (initial state) (initial_valid state)

theorem generate_settled (state : ArenaSource.State) : step state (generate state)=generate state :=
  run_settled state (initial state) (initial_valid state)

theorem generate_storage (state : ArenaSource.State) :
    AffineCarrier.resultSize (generate state) ≤
      AffineCarrier.Cost.cellBound (state.arena.code.size+state.arena.code.size*state.arena.code.size+1)+1 := by
  have valid := generate_valid state
  have stored := AffineCarrier.Cost.result_size (frame state).state.arena.code.size (generate state) valid.1 valid.2
  have size := ProductBatch.generate_size (PortEmbedding.initial state)
  simp only [PortEmbedding.initial_size] at size
  change (frame state).state.arena.code.size ≤ state.arena.code.size+state.arena.code.size*state.arena.code.size+1 at size
  apply stored.trans
  unfold AffineCarrier.Cost.cellBound
  gcongr

/-- The actual loop receives the already generated inventory. -/
def stepAt (original expanded : Frame) : Result → Result
  | .contradiction => .contradiction
  | .basis basis =>
      let projected := project expanded original.ports.size basis
      let generated := ProductSource.rows original projected
      eliminateFrom (.basis basis) (generated.map (ProductRows.mapped expanded))

theorem stepAt_source (state : ArenaSource.State) (result : Result) :
    stepAt (PortEmbedding.initial state) (frame state) result=step state result := by
  cases result <;> simp only [stepAt,step,consequences,PortEmbedding.initial_size]

def iterateAt (original expanded : Frame) : Nat → Result → Result
  | 0,result => result
  | fuel+1,result =>
      let next := stepAt original expanded result
      if next=result then result else iterateAt original expanded fuel next

theorem iterateAt_source (state : ArenaSource.State) (fuel : Nat) (result : Result) :
    iterateAt (PortEmbedding.initial state) (frame state) fuel result=iterate state fuel result := by
  induction fuel generalizing result with
  | zero => rfl
  | succ fuel ih => simp only [iterateAt,stepAt_source,ih,iterate]

def fromPrepared (original : Frame) (source : ProductRows.Prepared) : Result :=
  let initial := ProductRows.analyze source.frame source.rows
  iterateAt original source.frame (source.frame.state.arena.code.size+1) initial

theorem fromPrepared_source (state : ArenaSource.State) :
    fromPrepared (PortEmbedding.initial state) (ProductRows.prepare state)=generate state := by
  simp only [fromPrepared,ProductRows.prepare_frame]
  change iterateAt (PortEmbedding.initial state) (frame state) ((frame state).state.arena.code.size+1)
    (ProductRows.analyze (frame state) (ProductRows.prepare state).rows)=_
  rw [iterateAt_source]
  rfl

end SaturationMonoid.ComplexityProjection.SATSource.ProductClosure
