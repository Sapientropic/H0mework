import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.UnifiedFlow.Direct
import H0mework.Physics.Source.EnrichedProofFreeSource

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.UnifiedSource
open SaturationMonoid.PhysicsCore
open StageNineEnrichedProofFreeSource

noncomputable section

/-- One original formula supplies every contact coordinate; no source matrix or answer is passed in. -/
def contact {n : Nat} (formula : CNFFormula n) (point : Assignment n) : SmoothUnifiedSource where
  stageEight := StageEightProofFreeSource.canonicalSource
  continuousContactResidual := 2*(violationCount formula point : ℝ)

def generated {n : Nat} (formula : CNFFormula n) (point : Assignment n) :
    SourceGeneratedTraceCarrier (contact formula point) :=
  sourceGeneratedTraceWriteBack (contact formula point)

theorem original_projection {n : Nat} (formula : CNFFormula n) (point : Assignment n) :
    (contact formula point).forget=StageEightProofFreeSource.canonicalSource.toPhysicalSource := rfl

theorem contact_rate {n : Nat} (formula : CNFFormula n) (point : Assignment n) :
    (contact formula point).continuousContactRate=(violationCount formula point : ℝ) := by
  rw [SmoothUnifiedSource.continuousContactRate_eq_scalar]
  norm_num [contact,SmoothUnifiedSource.legacy,SmoothUnifiedSource.forget,
    StageEightProofFreeSource.Source.toPhysicalSource,StageEightProofFreeSource.canonicalSource,
    ProofFreeRicherAnholonomicSource.Source.sigma]
  ring

theorem generated_rate {n : Nat} (formula : CNFFormula n) (point : Assignment n) :
    (generated formula point).residualTraceShare=(violationCount formula point : ℝ) :=
  contact_rate formula point

theorem generated_phase {n : Nat} (formula : CNFFormula n) (point : Assignment n) (time : ℝ) :
    (generated formula point).closure.quantumPhase.flow.evolve time=
      Circle.exp ((violationCount formula point : ℝ)*time) := by
  change Circle.exp ((contact formula point).continuousContactRate*time)=_
  rw [contact_rate]

theorem generated_curvature {n : Nat} (formula : CNFFormula n) (point : Assignment n) :
    (generated formula point).closure.geometric.curvature 0 1=
      (violationCount formula point : ℝ) • motherHyperchargeDirection := by
  rw [(generated formula point).closure.geometric.curvature_zero_one,contact_rate]

def matrix {n : Nat} (formula : CNFFormula n) : Matrix (Assignment n) (Assignment n) ℂ :=
  Matrix.diagonal (fun point => ((generated formula point).residualTraceShare : ℂ))

theorem matrix_original {n : Nat} (formula : CNFFormula n) : matrix formula=UnifiedFlowProbe.matrix formula := by
  unfold matrix UnifiedFlowProbe.matrix
  congr 1
  funext point
  rw [generated_rate]
  simp

def operator {n : Nat} (formula : CNFFormula n) : UnifiedFlowProbe.Space n →L[ℂ] UnifiedFlowProbe.Space n :=
  Matrix.toEuclideanCLM (n := Assignment n) (𝕜 := ℂ) (matrix formula)

theorem operator_original {n : Nat} (formula : CNFFormula n) : operator formula=UnifiedFlowProbe.operator formula := by
  rw [operator,matrix_original]
  rfl

theorem source_flow {n : Nat} (formula : CNFFormula n) :
    SaturationMonoid.AffineRelaxation.BoundedSelfAdjointHamiltonianSchrodingerFlowCertificate
      (UnifiedFlowProbe.Space n) (operator formula) := by
  rw [operator_original]
  exact UnifiedFlowProbe.source_flow formula

theorem contact_zero_iff {n : Nat} (formula : CNFFormula n) (point : Assignment n) :
    (generated formula point).residualTraceShare=0 ↔ CNFFormula.eval formula (extendAssignment point)=true := by
  rw [generated_rate,Nat.cast_eq_zero]
  exact violationCount_eq_zero_iff_eval formula point

end
end SaturationMonoid.ComplexityProjection.SATSource.UnifiedSource
