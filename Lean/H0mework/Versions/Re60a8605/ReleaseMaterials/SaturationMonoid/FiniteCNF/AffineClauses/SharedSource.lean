import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.JointResidual
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.JointEmission

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineSharedSource
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineClauses (Clause Formula formulaRead Within)
open AffineCarrier (Cells Valid Separated read)

/-- The observation addresses belong to the original source, before any coordinate view. -/
structure Model where
  private mk ::
  table : Array Row
  image : AtomImage.State
  seed : Result
  pending : Formula
  deriving Repr

def width (model : Model) : Nat := model.table.size

def allows (model : Model) (target : Nat → Bool) : Bool :=
  model.seed.holds target && formulaRead model.pending target

private def prepare (table : Array Row) (image : AtomImage.State) (constraints : Formula) : Model :=
  let cleaned := AffineClauses.cleanRun constraints
  let seeded := AffineClauses.Seed.generate cleaned.value
  ⟨table,image,seeded.value,AffineClauses.Future.body cleaned.value⟩

private theorem prepare_read (table : Array Row) (image : AtomImage.State) (constraints : Formula)
    (target : Nat → Bool) : allows (prepare table image constraints) target=formulaRead constraints target := by
  simp only [allows,prepare,AffineClauses.cleanRun_value]
  rw [AffineClauses.Future.seed_body_read,AffineClauses.clean_read]

def generate (formula : Formula) : Model :=
  let table := AffineClauseImage.table formula
  let image := AtomImage.generate table
  let emitted := AffineJointEmission.emit (AffineClauseImage.atomFormula formula) image.kernel
  prepare table image (AffineJointResidual.canonicalRows (AffineJointEmission.constraints emitted))

theorem generate_table (formula : Formula) : (generate formula).table=AffineClauseImage.table formula := rfl

theorem generate_image (formula : Formula) :
    (generate formula).image=AtomImage.generate (AffineClauseImage.table formula) := rfl

theorem generate_width (formula : Formula) : width (generate formula)=AffineClauseImage.width formula := by
  rw [width,generate_table,AffineClauseImage.table_size]

theorem generate_allows (formula : Formula) (target : Nat → Bool) :
    allows (generate formula) target = formulaRead (AffineClauseImage.constraints formula
      (AtomImage.generate (AffineClauseImage.table formula))) target := by
  simp only [generate,prepare_read,AffineJointResidual.canonical_read,
    AffineJointEmission.constraints_read,AffineJointEmission.emit_read,AffineClauseImage.constraints_read]

theorem generate_read (formula : Formula) (input : Nat → Bool) :
    allows (generate formula) (Gates.coordinate (generate formula).table input)=formulaRead formula input := by
  rw [generate_allows,generate_table,AffineClauseImage.constraints_read,AffineClauseImage.atomFormula_read]
  have realized := (AtomImage.image_iff_kernel (AffineClauseImage.table formula) _).mp ⟨input,fun _ => rfl⟩
  rw [realized,Bool.and_true]

def Bounded (model : Model) : Prop :=
  model.seed.triangular ∧ model.seed.within (width model) ∧ Within (width model) model.pending

theorem generate_bounded (n : Nat) (formula : Formula) (inside : Within n formula) : Bounded (generate formula) := by
  have output := AffineJointEmission.emit_source_bounded n formula inside
  have bounded := AffineJointResidual.canonical_within _ _ (AffineJointEmission.constraints_within _ output)
  have cleanInside := AffineClauses.clean_within _ _ bounded
  have seeded := AffineClauses.Seed.generate_valid _ _ cleanInside
  simp only [Bounded,generate,prepare,AffineClauses.cleanRun_value,width,AffineClauseImage.table_size]
  exact ⟨seeded.1,seeded.2,AffineClauses.Future.body_within _ _ cleanInside⟩

structure Current where
  cells : Cells
  pending : Formula
  deriving Repr

def initial (model : Model) : Current := ⟨(AffineCarrier.pack model.seed).value,model.pending⟩

def Current.read (current : Current) (target : Nat → Bool) : Bool :=
  AffineCarrier.read current.cells target && formulaRead current.pending target

def Current.Bounded (q : Nat) (current : Current) : Prop :=
  Valid q current.cells ∧ Separated current.cells ∧ Within q current.pending

theorem initial_read (model : Model) (target : Nat → Bool) :
    (initial model).read target=allows model target := by
  rw [Current.read,initial,AffineCarrier.read_pack]
  rfl

theorem initial_bounded (model : Model) (bounded : Bounded model) : (initial model).Bounded (width model) :=
  ⟨AffineCarrier.pack_valid _ _ bounded.1 bounded.2.1,AffineCarrier.pack_separated _,bounded.2.2⟩

/-- All coordinate views share this one clause action on the original observation addresses. -/
def step (q : Nat) (current : Current) : Current :=
  match current.pending with
  | [] => current
  | clause::rest => ⟨AffineClauses.Joint.step q clause current.cells,rest⟩

theorem step_bounded (q : Nat) (current : Current) (bounded : current.Bounded q) : (step q current).Bounded q := by
  cases shape : current.pending with
  | nil => simpa only [step,shape] using bounded
  | cons clause rest =>
      have within : RowsWithin q clause := bounded.2.2 clause (by simp [shape])
      simp only [Current.Bounded,step,shape]
      exact ⟨AffineClauses.Joint.step_valid q clause within _ bounded.1,
        AffineClauses.Joint.step_separated q clause within _ bounded.1 bounded.2.1,
        fun c member => bounded.2.2 c (by simp [shape,member])⟩

theorem step_read (q : Nat) (current : Current) (bounded : current.Bounded q) (target : Nat → Bool) :
    (step q current).read target=current.read target := by
  cases shape : current.pending with
  | nil => simp only [step,shape]
  | cons clause rest =>
      have within : RowsWithin q clause := bounded.2.2 clause (by simp [shape])
      simp only [step,shape,Current.read,AffineClauses.Joint.step_read q clause within _ bounded.1 bounded.2.1]
      simp [formulaRead,Bool.and_assoc]

def run (q : Nat) : Nat → Current → Current
  | 0,current => current
  | fuel+1,current => run q fuel (step q current)

theorem run_bounded (q fuel : Nat) (current : Current) (bounded : current.Bounded q) :
    (run q fuel current).Bounded q := by
  induction fuel generalizing current with
  | zero => exact bounded
  | succ fuel ih => exact ih _ (step_bounded q current bounded)

theorem run_read (q fuel : Nat) (current : Current) (bounded : current.Bounded q) (target : Nat → Bool) :
    (run q fuel current).read target=current.read target := by
  induction fuel generalizing current with
  | zero => rfl
  | succ fuel ih => exact (ih _ (step_bounded q current bounded)).trans (step_read q current bounded target)

theorem run_pending (q fuel : Nat) (current : Current) : (run q fuel current).pending=current.pending.drop fuel := by
  induction fuel generalizing current with
  | zero => rfl
  | succ fuel ih =>
      rw [run,ih]
      cases shape : current.pending <;> simp [step,shape]

def finish (model : Model) : Current := run (width model) model.pending.length (initial model)

theorem finish_pending (model : Model) : (finish model).pending=[] := by
  rw [finish,run_pending]
  simp [initial]

theorem finish_read (model : Model) (bounded : Bounded model) (target : Nat → Bool) :
    read (finish model).cells target=allows model target := by
  have complete := run_read (width model) model.pending.length (initial model) (initial_bounded model bounded) target
  change (finish model).read target=(initial model).read target at complete
  rw [initial_read,Current.read,finish_pending] at complete
  simpa [formulaRead] using complete

def decide (model : Model) : Bool := !(finish model).cells.isEmpty

theorem decide_correct (n : Nat) (formula : Formula) (inside : Within n formula) :
    decide (generate formula)=true ↔ AffineClauseProduct.Satisfiable formula := by
  have bounded := generate_bounded n formula inside
  have finalValid : Valid (width (generate formula)) (finish (generate formula)).cells :=
    (run_bounded _ (generate formula).pending.length _ (initial_bounded (generate formula) bounded)).1
  rw [decide,AffineCarrier.nonempty_iff _ _ finalValid]
  apply Iff.trans ?_ (AffineJointResidual.constraints_possible formula)
  constructor
  · rintro ⟨point,accepted⟩
    refine ⟨extendAssignment point,?_⟩
    rw [finish_read _ bounded,generate_allows] at accepted
    exact accepted
  · rintro ⟨point,accepted⟩
    refine ⟨fun i => point i.val,?_⟩
    have finite := AffineClauses.Joint.read_restrict _ (finish (generate formula)).cells finalValid point
    rw [finite,finish_read _ bounded,generate_allows]
    exact accepted


/-- A formula presentation is generated from the shared current; it is never used as an independent source. -/
def materialize (table : Array Row) (current : Current) : CapacityMatching.SourceCost.Counted Current :=
  let guards := AffineResidual.rewrite table current.cells
  let pending := AffineResidual.rewrite table current.pending
  ⟨⟨guards.value,pending.value⟩,guards.cells+pending.cells+
    2*(AffineCollect.tableSize table+AffineClauses.formulaSize guards.value+AffineClauses.formulaSize pending.value)+5⟩

def view (table : Array Row) (current : Current) : Current := (materialize table current).value

theorem view_read (table : Array Row) (current : Current) (input : Nat → Bool) :
    (view table current).read input=current.read (Gates.coordinate table input) := by
  have cells : read (view table current).cells input=read current.cells (Gates.coordinate table input) := by
    simp only [view,materialize,AffineResidual.rewrite_value,AffineCarrier.read,List.any_map]
    apply List.any_congr rfl
    intro basis
    simp only [Function.comp_apply,holds,List.all_map]
    apply List.all_congr rfl
    intro row
    exact AffineResidual.combine_holds table row input
  rw [Current.read,cells]
  change (AffineCarrier.read current.cells (Gates.coordinate table input) &&
    formulaRead (AffineResidual.rewrite table current.pending).value input) =
      (AffineCarrier.read current.cells (Gates.coordinate table input) &&
        formulaRead current.pending (Gates.coordinate table input))
  rw [AffineResidual.rewrite_read]

theorem view_step (q : Nat) (table : Array Row) (current : Current) (bounded : current.Bounded q)
    (input : Nat → Bool) : (view table (step q current)).read input=(view table current).read input := by
  rw [view_read,step_read q current bounded,view_read]

theorem view_run (q fuel : Nat) (table : Array Row) (current : Current) (bounded : current.Bounded q)
    (input : Nat → Bool) : (view table (run q fuel current)).read input=(view table current).read input := by
  rw [view_read,run_read q fuel current bounded,view_read]

def sourceView (model : Model) (current : Current) : Current := view model.table current

theorem source_run_read (n fuel : Nat) (formula : Formula) (inside : Within n formula) (input : Nat → Bool) :
    (sourceView (generate formula) (run (width (generate formula)) fuel (initial (generate formula)))).read input =
      formulaRead formula input := by
  rw [sourceView,view_run _ _ _ _ (initial_bounded _ (generate_bounded n formula inside)),
    view_read,initial_read,generate_read]

theorem view_cells_length (table : Array Row) (current : Current) :
    (view table current).cells.length=current.cells.length := AffineResidual.rewrite_length table current.cells

theorem view_pending_length (table : Array Row) (current : Current) :
    (view table current).pending.length=current.pending.length := AffineResidual.rewrite_length table current.pending


def sourceSize (current : Current) : Nat :=
  AffineClauses.formulaSize current.cells+AffineClauses.formulaSize current.pending

def viewBudget (n tableSize size : Nat) : Nat :=
  2*AffineResidual.Cost.rewriteBudget n tableSize size+2*(tableSize*(n+2)+1+2*(n+3)*size)+5

theorem materialize_cells (n : Nat) (table : Array Row) (valid : Table.Valid n table) (current : Current) :
    (materialize table current).cells ≤ viewBudget n table.size (sourceSize current) := by
  have guards := AffineResidual.Cost.rewrite_cells n table valid current.cells
  have pending := AffineResidual.Cost.rewrite_cells n table valid current.pending
  have guardsSize := AffineResidual.Cost.rewrite_size_ceiling n table valid current.cells
  have pendingSize := AffineResidual.Cost.rewrite_size_ceiling n table valid current.pending
  have tableSize := CapacityMatching.RowCost.table_storage n table valid
  have guardsBudget : AffineResidual.Cost.rewriteBudget n table.size (AffineClauses.formulaSize current.cells) ≤
      AffineResidual.Cost.rewriteBudget n table.size (sourceSize current) := by
    unfold AffineResidual.Cost.rewriteBudget AffineResidual.Cost.rewriteRound CapacityMatching.RowCost.decodeBudget sourceSize
    gcongr <;> omega
  have pendingBudget : AffineResidual.Cost.rewriteBudget n table.size (AffineClauses.formulaSize current.pending) ≤
      AffineResidual.Cost.rewriteBudget n table.size (sourceSize current) := by
    unfold AffineResidual.Cost.rewriteBudget AffineResidual.Cost.rewriteRound CapacityMatching.RowCost.decodeBudget sourceSize
    gcongr <;> omega
  simp only [materialize,viewBudget,sourceSize,AffineCollect.tableSize]
  simp only [sourceSize] at guardsBudget pendingBudget
  nlinarith

end SaturationMonoid.ComplexityProjection.SATSource.AffineSharedSource
