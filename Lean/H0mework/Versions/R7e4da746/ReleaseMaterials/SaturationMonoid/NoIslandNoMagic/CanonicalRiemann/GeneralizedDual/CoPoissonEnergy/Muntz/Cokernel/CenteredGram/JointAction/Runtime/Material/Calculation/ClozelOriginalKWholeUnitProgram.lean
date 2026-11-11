import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWholeUnit.Origin
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeTrace

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeUnitProgram
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution FourierTransform
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
namespace Count
export OriginalRieszFinitePairing.CoPoisson.Ward.CountingDual (sourceCLM dual_eq_adjoint)
end Count
namespace Domain
export OriginalRieszFinitePairing.CoPoisson.Ward.RieszEulerDomain (value velocity)
end Domain
noncomputable def dual (N:ℕ) : BurnolL2 →L[ℂ] BurnolL2 := (Count.sourceCLM N).adjoint
private def lin (operation:BurnolL2 →L[ℂ] BurnolL2) (body:Prog.E) : Prog.E :=
  .linear operation.toLinearMap.toAddMonoidHom body
noncomputable def environment (kernel:BurnolL2) : Env Prog.Value Prog.Var := fun _ _=>kernel
def code (N:ℕ) (alpha beta:BurnolL2) : Prog.E :=
  lin (dual N) (.add (.add (.var (0:Fin 2))
    (lin (-ContinuousLinearMap.id ℂ BurnolL2) (.const alpha)))
    (lin (fourierL2.toContinuousLinearEquiv.toContinuousLinearMap) (.const beta)))
theorem code_budget (N:ℕ) (alpha beta:BurnolL2) : remaining (code N alpha beta)=6 := rfl
theorem code_eval (N:ℕ) (kernel alpha beta:BurnolL2) :
    (code N alpha beta).eval (environment kernel)=dual N (kernel-alpha+fourierL2 beta) := by
  change dual N (kernel+(-ContinuousLinearMap.id ℂ BurnolL2) alpha+fourierL2 beta)=_
  simp only [neg_apply,ContinuousLinearMap.id_apply,sub_eq_add_neg]

theorem code_actual (c:BurnolCompletedMellinCoordinate) (N:ℕ) (kernel alpha beta:BurnolL2)
    (kernelSource:kernel=(burnolCompletedMellinRieszVector c:BurnolL2))
    (alphaSource:alpha=OriginalRieszSource.Kernel.A c • OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed)
    (betaSource:beta=OriginalRieszSource.Kernel.beta c • OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed) :
    (code N alpha beta).eval (environment kernel)=
      OriginalRieszFinitePairing.CoPoisson.Ward.DualSource.source N (Domain.value c) := by
  rw [code_eval,kernelSource,alphaSource,betaSource,map_smul]
  exact (Count.dual_eq_adjoint N (Domain.value c)).symm

namespace Traced
variable (N:ℕ) (alpha beta:BurnolL2) {env:Env Prog.Value Prog.Var} {value:BurnolL2}
variable (actual:Trace env (code N alpha beta) (.const value))
noncomputable def outer := Trace.splitLinear actual
noncomputable def sum := Trace.splitAdd (outer N alpha beta actual).trace
noncomputable def base := Trace.splitAdd (sum N alpha beta actual).leftTrace
noncomputable def negative := Trace.splitLinear (base N alpha beta actual).rightTrace
noncomputable def fourier := Trace.splitLinear (sum N alpha beta actual).rightTrace
noncomputable def kernelReceipt : Trace.SourceReceipt actual (.var (0:Fin 2)) :=
  ⟨(base N alpha beta actual).leftValue,(base N alpha beta actual).leftTrace,
    .linear (outer N alpha beta actual) (.left (sum N alpha beta actual) (.left (base N alpha beta actual) (.refl _)))⟩
noncomputable def alphaReceipt : Trace.SourceReceipt actual (.const alpha) :=
  ⟨(negative N alpha beta actual).input,(negative N alpha beta actual).trace,
    .linear (outer N alpha beta actual) (.left (sum N alpha beta actual)
      (.right (base N alpha beta actual) (.linear (negative N alpha beta actual) (.refl _))))⟩
noncomputable def betaReceipt : Trace.SourceReceipt actual (.const beta) :=
  ⟨(fourier N alpha beta actual).input,(fourier N alpha beta actual).trace,
    .linear (outer N alpha beta actual) (.right (sum N alpha beta actual)
      (.linear (fourier N alpha beta actual) (.refl _)))⟩
theorem kernel_read : (kernelReceipt N alpha beta actual).value=env () 0 :=
  (kernelReceipt N alpha beta actual).trace.sound.symm
theorem alpha_read : (alphaReceipt N alpha beta actual).value=alpha :=
  (alphaReceipt N alpha beta actual).trace.sound.symm
theorem beta_read : (betaReceipt N alpha beta actual).value=beta :=
  (betaReceipt N alpha beta actual).trace.sound.symm
end Traced

end OriginalWholeUnitProgram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalWholeUnitProgram"
