import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryGammaResolvent.Inverse
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPairedSecondBProgram

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalBoundaryGammaProgram
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
namespace Price
export OriginalConstantFourierPriceMath (embed read scalarLift scalarRead scalar_lift)
end Price
local notation "H"=>BurnolPaAmbientCarrier
local notation "P"=>burnolEvenAmbientProjection
local notation "h"=>OriginalKPairedBEulerJunctionSource.junctionShift
local notation "K"=>burnolCompletedMellinRieszVector

def physical : BurnolL2 →L[ℂ] BurnolL2 := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL.comp P
/-- Canonical L² extension. On the preceding physical output its restriction is exactly E. -/
def wholeInverse (c:BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL.comp
    ((OriginalBoundaryGammaResolvent.inverse c c.rightHalf).comp P)
def dilation : BurnolL2 →L[ℂ] BurnolL2 := pairedBurnolMultiplicativeDilation h
def environment (raw:BurnolL2) : Env Prog.Value Prog.Var := fun _ _=>raw
private def lin (op:BurnolL2 →L[ℂ] BurnolL2) (body:Prog.E) : Prog.E :=
  .linear op.toLinearMap.toAddMonoidHom body
def physicalCode : Prog.E := lin physical (.var (0:Fin 2))
def recoveredCode (c:BurnolCompletedMellinCoordinate) : Prog.E := lin (wholeInverse c) physicalCode
def pairedCode (c:BurnolCompletedMellinCoordinate) : Prog.E := lin dilation (recoveredCode c)
def b2Code (c:BurnolCompletedMellinCoordinate) : Prog.E := lin OriginalPairedSecondBProgram.wholeB2 (pairedCode c)
def code (c:BurnolCompletedMellinCoordinate) : Prog.E := lin (OriginalSecondBGammaProgram.operation c c) (b2Code c)
theorem code_budget (c:BurnolCompletedMellinCoordinate) : remaining (code c)=6 := rfl
theorem code_eval (c:BurnolCompletedMellinCoordinate) (raw:BurnolL2) :
  (code c).eval (environment raw)=OriginalSecondBGammaProgram.operation c c
    (OriginalPairedSecondBProgram.wholeB2 (dilation (wholeInverse c (physical raw)))) := rfl

theorem inverse_physical (c:BurnolCompletedMellinCoordinate) (raw:BurnolL2) :
    wholeInverse c (physical raw)=(OriginalBoundaryGammaResolvent.inverse c c.rightHalf (P raw):BurnolL2) := by
  change ((OriginalBoundaryGammaResolvent.inverse c c.rightHalf) (P (P raw:BurnolL2)):BurnolL2)=_
  have fixed : P (P raw:BurnolL2)=P raw := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  exact congrArg (fun value:H=>(OriginalBoundaryGammaResolvent.inverse c c.rightHalf value:BurnolL2)) fixed

theorem recovered_actual (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (raw:BurnolL2)
    (actual:P raw=burnolZeroPairedFixedAnnulusBoundary c zero h) :
    wholeInverse c (physical raw)=(K c:BurnolL2) := by
  rw [inverse_physical,actual,OriginalBoundaryGammaResolvent.inverse_original_boundary]

theorem paired_actual (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (raw:BurnolL2)
    (actual:P raw=burnolZeroPairedFixedAnnulusBoundary c zero h) :
    dilation (wholeInverse c (physical raw))=OriginalKPairedBEulerJunctionSource.sourceAction c :=
  congrArg dilation (recovered_actual c zero raw actual)

theorem b2_actual (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (raw:BurnolL2)
    (actual:P raw=burnolZeroPairedFixedAnnulusBoundary c zero h) :
    OriginalPairedSecondBProgram.wholeB2 (dilation (wholeInverse c (physical raw)))=
      burnolQuarterZeroExtension (OriginalKPairedBEulerJunctionSource.sourceSecond c:BurnolQuarterIntervalL2) :=
  OriginalPairedSecondBProgram.wholeB2_actual c _ (paired_actual c zero raw actual)

theorem code_actual (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (raw:BurnolL2)
    (actual:P raw=burnolZeroPairedFixedAnnulusBoundary c zero h) :
    (code c).eval (environment raw)=Price.scalarLift (OriginalWholeDebtRJointMobiusContactPsiPriceSource.nativeGamma c c) :=
  (code_eval c raw).trans (OriginalSecondBGammaProgram.operation_actual c c _ (b2_actual c zero raw actual))

namespace Traced
variable (c:BurnolCompletedMellinCoordinate) {env:Env Prog.Value Prog.Var} {value:BurnolL2}
variable (actual:Trace env (code c) (.const value))
noncomputable def gamma := Trace.splitLinear actual
noncomputable def b2 := Trace.splitLinear (gamma c actual).trace
noncomputable def paired := Trace.splitLinear (b2 c actual).trace
noncomputable def recovered := Trace.splitLinear (paired c actual).trace
noncomputable def projected := Trace.splitLinear (recovered c actual).trace
noncomputable def b2Receipt : Trace.SourceReceipt actual (b2Code c) :=
  ⟨(gamma c actual).input,(gamma c actual).trace,.linear (gamma c actual) (.refl _)⟩
noncomputable def pairedReceipt : Trace.SourceReceipt actual (pairedCode c) :=
  ⟨(b2 c actual).input,(b2 c actual).trace,.linear (gamma c actual) (.linear (b2 c actual) (.refl _))⟩
noncomputable def recoveredReceipt : Trace.SourceReceipt actual (recoveredCode c) :=
  ⟨(paired c actual).input,(paired c actual).trace,
    .linear (gamma c actual) (.linear (b2 c actual) (.linear (paired c actual) (.refl _)))⟩
noncomputable def physicalReceipt : Trace.SourceReceipt actual physicalCode :=
  ⟨(recovered c actual).input,(recovered c actual).trace,
    .linear (gamma c actual) (.linear (b2 c actual) (.linear (paired c actual) (.linear (recovered c actual) (.refl _))))⟩
noncomputable def rawReceipt : Trace.SourceReceipt actual (.var (0:Fin 2)) :=
  ⟨(projected c actual).input,(projected c actual).trace,
    .linear (gamma c actual) (.linear (b2 c actual) (.linear (paired c actual)
      (.linear (recovered c actual) (.linear (projected c actual) (.refl _)))))⟩
theorem raw_read : (rawReceipt c actual).value=env () 0 := (rawReceipt c actual).trace.sound.symm
theorem physical_read : (physicalReceipt c actual).value=physical (env () 0) := (physicalReceipt c actual).trace.sound.symm
theorem recovered_read : (recoveredReceipt c actual).value=wholeInverse c (physical (env () 0)) := (recoveredReceipt c actual).trace.sound.symm
theorem paired_read : (pairedReceipt c actual).value=dilation (wholeInverse c (physical (env () 0))) := (pairedReceipt c actual).trace.sound.symm
theorem b2_read : (b2Receipt c actual).value=OriginalPairedSecondBProgram.wholeB2 (dilation (wholeInverse c (physical (env () 0)))) := (b2Receipt c actual).trace.sound.symm
end Traced
end OriginalBoundaryGammaProgram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env=>Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalBoundaryGammaProgram"
