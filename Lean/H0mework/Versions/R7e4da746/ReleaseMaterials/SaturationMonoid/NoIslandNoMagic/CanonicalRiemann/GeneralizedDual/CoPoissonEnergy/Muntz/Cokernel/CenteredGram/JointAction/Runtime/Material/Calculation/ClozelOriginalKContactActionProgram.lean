import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKConstantFourierPriceProgram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ContactFeedback.PrimitiveSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalContactProgram
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution OriginalRieszSource
namespace P
export OriginalKPaNativePortSourceCalculation (Value Var E)
end P
namespace M
export OriginalConstantFourierPriceMath (scalarRead scalarLift scalar_lift embed)
end M
namespace Flux
export FiniteMobiusResolventFlux (M D Rplus Rplus_tate)
end Flux
namespace Contact
export OriginalContactFeedbackSource (primitiveScale original_primitive_gap_source generatedContactAction original_complete_contact_action)
end Contact
private def linear (op:BurnolL2 →L[ℂ] BurnolL2) (input:P.E) : P.E :=
  .linear op.toLinearMap.toAddMonoidHom input
private def scale (a:ℂ) (input:P.E) : P.E := linear (a • ContinuousLinearMap.id ℂ BurnolL2) input
private def sub (left right:P.E) : P.E := .add left (scale (-1) right)
private def fourier (input:P.E) : P.E := linear fourierL2.toContinuousLinearEquiv.toContinuousLinearMap input
private def tate (input:P.E) : P.E := linear burnolTateReciprocalL2 input
private def mobius (input:P.E) : P.E := linear Flux.M input
private def product (coefficient:BurnolL2) (input:P.E) : P.E :=
  .bilinear (s := ()) (t := ()) (r := ()) OriginalConstantFourierPriceProgram.scalarAction (.const coefficient) input

def defect (input:P.E) : P.E := sub (mobius (fourier input)) (tate (mobius input))
def edgeCode (c:BurnolCompletedMellinCoordinate) (gap:BurnolL2) : P.E :=
  scale (Contact.primitiveScale c) (.const gap)
def contactCode (alpha beta:BurnolL2) : P.E := sub (product alpha (.var 0)) (product beta (.var 1))
def returnCode (alpha beta:BurnolL2) : P.E := sub (product beta (.var 0)) (product alpha (.var 1))
def forcingCode (c:BurnolCompletedMellinCoordinate) (alpha beta gap:BurnolL2) : P.E :=
  sub (.add (scale (-1) (tate (mobius (fourier (contactCode alpha beta)))))
    (defect (returnCode alpha beta)))
    (scale (2*(star c.value-1/2)) (product beta (defect (fourier (edgeCode c gap)))))
/-- This is the actual J / R_bar / J action, with the complete finite means inside M. -/
def code (c:BurnolCompletedMellinCoordinate) (alpha beta gap:BurnolL2) : P.E :=
  tate (linear (burnolDirectRightResolventCLM (OriginalKBFiniteCalculation.conjugateCoordinate c))
    (tate (forcingCode c alpha beta gap)))
def environment (u v:BurnolL2) : Env P.Value P.Var := fun _ i => ![u,v] i

private theorem linear_eval (op:BurnolL2 →L[ℂ] BurnolL2) (input:P.E) (env:Env P.Value P.Var) :
    (linear op input).eval env=op (input.eval env) := rfl
private theorem scale_eval (a:ℂ) (input:P.E) (env:Env P.Value P.Var) :
    (scale a input).eval env=a • input.eval env := rfl
private theorem sub_eval (left right:P.E) (env:Env P.Value P.Var) :
    (sub left right).eval env=left.eval env-right.eval env := by
  change left.eval env+(-1:ℂ) • right.eval env=_
  rw [neg_one_smul,sub_eq_add_neg]
private theorem product_eval (a:BurnolL2) (input:P.E) (env:Env P.Value P.Var) :
    (product a input).eval env=M.scalarRead a • input.eval env := rfl
theorem defect_eval (input:P.E) (env:Env P.Value P.Var) :
    (defect input).eval env=Flux.D (input.eval env) := by
  rw [defect,sub_eval]
  rfl
theorem contact_eval (alpha beta:BurnolL2) (env:Env P.Value P.Var) :
    (contactCode alpha beta).eval env=M.scalarRead alpha • env () 0-M.scalarRead beta • env () 1 := by
  rw [contactCode,sub_eval,product_eval,product_eval]
  rfl
theorem return_eval (alpha beta:BurnolL2) (env:Env P.Value P.Var) :
    (returnCode alpha beta).eval env=M.scalarRead beta • env () 0-M.scalarRead alpha • env () 1 := by
  rw [returnCode,sub_eval,product_eval,product_eval]
  rfl
theorem edge_eval (c:BurnolCompletedMellinCoordinate) (gap:BurnolL2) (env:Env P.Value P.Var) :
    (edgeCode c gap).eval env=Contact.primitiveScale c • gap := rfl
theorem forcing_eval (c:BurnolCompletedMellinCoordinate) (alpha beta gap:BurnolL2) (env:Env P.Value P.Var) :
    (forcingCode c alpha beta gap).eval env=
      -burnolTateReciprocalL2 (Flux.M (fourierL2 ((contactCode alpha beta).eval env)))+
      Flux.D ((returnCode alpha beta).eval env)-
      (2*(star c.value-1/2)*M.scalarRead beta) • Flux.D (fourierL2 ((edgeCode c gap).eval env)) := by
  rw [forcingCode,sub_eval]
  change (-1:ℂ) • burnolTateReciprocalL2 (Flux.M (fourierL2 ((contactCode alpha beta).eval env)))+
    (defect (returnCode alpha beta)).eval env-
    (2*(star c.value-1/2)) • (product beta (defect (fourier (edgeCode c gap)))).eval env=_
  rw [neg_one_smul,defect_eval,product_eval,defect_eval,smul_smul]
  rfl
theorem code_eval (c:BurnolCompletedMellinCoordinate) (alpha beta gap:BurnolL2) (env:Env P.Value P.Var) :
    (code c alpha beta gap).eval env=Flux.Rplus (star c.value/2) ((forcingCode c alpha beta gap).eval env) := by
  have right : 1/4<(star c.value/2).re := by
    rw [Complex.div_re];norm_num [Complex.star_def];linarith [c.rightHalf]
  rw [Flux.Rplus_tate _ right]
  rfl

private theorem contact_original (c:BurnolCompletedMellinCoordinate) :
    (contactCode (M.scalarLift (Kernel.A c)) (M.scalarLift (Kernel.beta c))).eval
      (environment (M.embed Response.u) (M.embed Response.v))=OriginalColumnMomentSource.wholeContactResponse c := by
  rw [contact_eval,M.scalar_lift,M.scalar_lift]
  change Kernel.A c • burnolQuarterZeroExtension (Response.u:BurnolQuarterIntervalL2)-
    Kernel.beta c • burnolQuarterZeroExtension (Response.v:BurnolQuarterIntervalL2)=_
  unfold OriginalColumnMomentSource.wholeContactResponse OriginalColumnMomentSource.contactResponse
  rw [map_sub,map_smul,map_smul]
private theorem return_original (c:BurnolCompletedMellinCoordinate) :
    (returnCode (M.scalarLift (Kernel.A c)) (M.scalarLift (Kernel.beta c))).eval
      (environment (M.embed Response.u) (M.embed Response.v))=OriginalColumnMomentSource.wholeReturnResponse c := by
  rw [return_eval,M.scalar_lift,M.scalar_lift,OriginalReturnResponseSource.original_return_response_occurrence]
  unfold OriginalReturnResponseSource.wholeReturnResponse
  rw [OriginalReturnResponseSource.actual_return_response_coefficients,map_add,map_smul,map_smul]
  change Kernel.beta c • burnolQuarterZeroExtension (Response.u:BurnolQuarterIntervalL2)-
    Kernel.A c • burnolQuarterZeroExtension (Response.v:BurnolQuarterIntervalL2)=_
  module

/-- The existing Euler / resolvent source laws recognize the executed contact output. -/
theorem original_contact (c:BurnolCompletedMellinCoordinate) :
    (code c (M.scalarLift (Kernel.A c)) (M.scalarLift (Kernel.beta c)) (OriginalRieszSourceGreen.gapState c)).eval
      (environment (M.embed Response.u) (M.embed Response.v))=Contact.generatedContactAction c := by
  rw [code_eval,forcing_eval,contact_original,return_original,M.scalar_lift,edge_eval,
    ←Contact.original_primitive_gap_source]
  change Flux.Rplus (star c.value/2) (OriginalColumnMomentSource.etaRemainingSource c)=_
  rw [OriginalReturnResponseSource.original_eta_remaining_action,
    OriginalFourierMobiusReturnSource.original_eta_fourier_action,Contact.original_complete_contact_action]

theorem code_budget (c:BurnolCompletedMellinCoordinate) (alpha beta gap:BurnolL2) :
    remaining (code c alpha beta gap)=46 := by
  rfl
end OriginalContactProgram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
