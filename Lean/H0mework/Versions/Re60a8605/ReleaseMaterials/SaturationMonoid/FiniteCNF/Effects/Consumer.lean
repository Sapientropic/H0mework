import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Effects.Shared
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Effects.Read

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.EffectConsumer
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine

/-- The selected coordinate comes from the current generated program itself. -/
def step (program : Program) : Program :=
  match (FunctionalSubstitution.inputs program.code).head? with
  | none => program
  | some address => EffectDAG.eliminate program address

theorem step_correct (program : Program) :
    (∃ point, truth ((step program).eval point)=true) ↔ ∃ point, truth (program.eval point)=true := by
  simp only [step]
  split
  · rfl
  · exact EffectDAG.eliminate_correct program _

theorem step_size (program : Program) : (step program).code.size ≤ 10*program.code.size+9 := by
  simp only [step]
  split
  · omega
  · exact EffectDAG.eliminate_size program _

def readOutput (source : PortUpdate.Output) : Bool :=
  if source.rejected then false else EffectReading.read (step source.frame.state.program.program)

theorem readOutput_original (source : PortUpdate.Output) : readOutput source=true ↔ PortUpdate.stateDecision source.frame.state source.rejected=true := by
  cases rejected : source.rejected <;>
    simp only [readOutput,EffectReading.read_value,rejected,Bool.false_eq_true,if_false,if_true,PortUpdate.stateDecision,Bool.not_false,Bool.not_true,
      Bool.true_and,Bool.false_and,ForgettingScalar.programRead_correct,FunctionalSubstitution.decideProgram_correct,step_correct]

def decide {n : Nat} (formula : CNFFormula n) (basis : List Row) : Bool := readOutput (ProductClosureCost.compile formula basis).value

theorem decide_correct {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    decide formula basis=true ↔ ∃ point, CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point)=true :=
  (readOutput_original _).trans (ProductClosureCost.compile_decision formula basis valid)

theorem decide_original {n : Nat} (formula : CNFFormula n) : decide formula []=true ↔ CNFSatisfiable formula := by
  simpa only [FunctionalMessage.empty_formula,CNFSatisfiable] using decide_correct formula [] ⟨triangular_nil,by simp [RowsWithin]⟩

end SaturationMonoid.ComplexityProjection.SATSource.EffectConsumer
