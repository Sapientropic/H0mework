import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKContactActionProgram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ContactFeedback.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCompleteFeeProgram
open Complex MeasureTheory Set BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open scoped InnerProductSpace
namespace P
export OriginalKPaNativePortSourceCalculation (Value Var E)
end P
namespace M
export OriginalConstantFourierPriceMath (seed scalarLift scalarRead scalar_lift)
end M
namespace Flux
export FiniteMobiusResolventFlux (M D cutoff cutoff_read)
end Flux
open private linear scale sub sub_eval from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKContactActionProgram
def sampling : BurnolL2 →L[ℂ] BurnolL2 := Flux.cutoff 4-Flux.cutoff (1/4)
theorem sampling_actual (value:BurnolL2) : sampling value=burnolAnnulusSamplingL2 value 0 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (Flux.cutoff 4 value) (Flux.cutoff (1/4) value),
    Flux.cutoff_read 4 value,Flux.cutoff_read (1/4) value,burnolAnnulusSamplingL2_coeFn value 0]
    with x subtraction large small sampled
  change (Flux.cutoff 4 value-Flux.cutoff (1/4) value) x=_
  rw [subtraction,Pi.sub_apply,large,small,sampled]
  simp only [burnolAnnulusSamplingRaw,Nat.cast_zero,zero_add,one_mul]
  by_cases quarter : x∈symmetricInterval (1/4:ℝ)
  · have outer : x∈symmetricInterval (4:ℝ) := ⟨by linarith [quarter.1],by linarith [quarter.2]⟩
    have none : x∉burnolSamplingAnnulus := fun point=>not_lt_of_ge (abs_le.mpr quarter) point.1
    rw [indicator_of_mem quarter,indicator_of_mem outer,indicator_of_notMem none,sub_self]
  · by_cases outer : x∈symmetricInterval (4:ℝ)
    · have inside : x∈burnolSamplingAnnulus := ⟨lt_of_not_ge (fun h=>quarter (abs_le.mp h)),abs_le.mpr outer⟩
      rw [indicator_of_mem outer,indicator_of_notMem quarter,indicator_of_mem inside,sub_zero]
    · have none : x∉burnolSamplingAnnulus := fun point=>outer (abs_le.mp point.2)
      rw [indicator_of_notMem outer,indicator_of_notMem quarter,indicator_of_notMem none,sub_self]

def cotestAction : BurnolL2 →+ BurnolL2 →+ BurnolL2 where
  toFun := fun left=>
    { toFun := fun right=>inner ℂ left right • M.seed
      map_zero' := by simp
      map_add' := by intro right next;simp only [inner_add_right,add_smul] }
  map_zero' := by apply AddMonoidHom.ext;intro right;simp
  map_add' := by intro left next;apply AddMonoidHom.ext;intro right;simp only [inner_add_left,add_smul];rfl

def columnCode (c:BurnolCompletedMellinCoordinate) (h:ℝ) : P.E :=
  sub (scale (fullMellinTranslationCharacter (star c.value) h) (.var 1))
    (linear (burnolMultiplicativeDilation (-h)).toContinuousLinearEquiv.toContinuousLinearMap (.var 1))
def pairedCode (c:BurnolCompletedMellinCoordinate) (h:ℝ) : P.E :=
  .add (linear sampling (columnCode c h)) (linear sampling (columnCode c (-h)))
def defectCode : P.E := OriginalContactProgram.defect (.var 0)
def code (c:BurnolCompletedMellinCoordinate) (h:ℝ) : P.E :=
  .bilinear (s:=()) (t:=()) (r:=()) cotestAction (pairedCode c h) defectCode
def environment (kernel b:BurnolL2) : Env P.Value P.Var := fun _ i=>![kernel,b] i

theorem column_eval (c:BurnolCompletedMellinCoordinate) (h:ℝ) (env:Env P.Value P.Var) :
    (columnCode c h).eval env=fullMellinTranslationCharacter (star c.value) h • env () 1-
      burnolMultiplicativeDilation (-h) (env () 1) := by
  rw [columnCode,sub_eval]
  rfl
theorem paired_eval (c:BurnolCompletedMellinCoordinate) (h:ℝ) (env:Env P.Value P.Var) :
    (pairedCode c h).eval env=sampling ((columnCode c h).eval env)+sampling ((columnCode c (-h)).eval env) := rfl
theorem defect_eval (env:Env P.Value P.Var) : defectCode.eval env=Flux.D (env () 0) :=
  OriginalContactProgram.defect_eval (.var 0) env
theorem code_eval (c:BurnolCompletedMellinCoordinate) (h:ℝ) (env:Env P.Value P.Var) :
    (code c h).eval env=M.scalarLift (inner ℂ ((pairedCode c h).eval env) (Flux.D (env () 0))) := by
  change inner ℂ ((pairedCode c h).eval env) (defectCode.eval env) • M.seed=_
  rw [defect_eval]
  rfl
theorem paired_actual (c:BurnolCompletedMellinCoordinate) (h:ℝ) (kernel:BurnolL2) :
    (pairedCode c h).eval (environment kernel
      (burnolQuarterZeroExtension (burnolRieszSingleFourierSource c:BurnolQuarterIntervalL2)))=
      OriginalPrimitiveRankBalance.pairedColumn c h := by
  rw [paired_eval,column_eval,column_eval,sampling_actual,sampling_actual]
  change burnolAnnulusSamplingL2
      (fullMellinTranslationCharacter (star c.value) h •
        burnolQuarterZeroExtension (burnolRieszSingleFourierSource c:BurnolQuarterIntervalL2)-
        burnolMultiplicativeDilation (-h) (burnolQuarterZeroExtension (burnolRieszSingleFourierSource c:BurnolQuarterIntervalL2))) 0+
    burnolAnnulusSamplingL2
      (fullMellinTranslationCharacter (star c.value) (-h) •
        burnolQuarterZeroExtension (burnolRieszSingleFourierSource c:BurnolQuarterIntervalL2)-
        burnolMultiplicativeDilation (-(-h)) (burnolQuarterZeroExtension (burnolRieszSingleFourierSource c:BurnolQuarterIntervalL2))) 0=_
  rw [←OriginalRieszFinitePairing.fourierColumn_action,←OriginalRieszFinitePairing.fourierColumn_action]
  rfl
theorem code_budget (c:BurnolCompletedMellinCoordinate) (h:ℝ) : remaining (code c h)=24 := rfl

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c"=>OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
theorem complete_price (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) :
    inner ℂ (OriginalPrimitiveRankBalance.pairedColumn c h)
      (Flux.D (burnolCompletedMellinRieszVector c:BurnolL2))=
      OriginalContactFeedbackSource.completeContactPrice observation nontrivial half h := by
  rw [FiniteMobiusResolventFlux.defect_source_physical,
    FiniteMobiusResolventFlux.original_defect_ranked observation nontrivial half,
    OriginalPrimitiveRankBalance.original_defect_two_moments,
    OriginalColumnMomentSource.original_complete_source_price _ _ _ _ nonnegative bounded,
    OriginalReturnResponseSource.original_complete_return_price,
    OriginalFourierMobiusReturnSource.original_complete_fourier_return_price,
    OriginalContactFeedbackSource.original_complete_contact_price]

theorem code_actual (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) :
    (code c h).eval (environment (burnolCompletedMellinRieszVector c:BurnolL2)
      (burnolQuarterZeroExtension (burnolRieszSingleFourierSource c:BurnolQuarterIntervalL2)))=
      M.scalarLift (OriginalContactFeedbackSource.completeContactPrice observation nontrivial half h) := by
  rw [code_eval,paired_actual]
  change M.scalarLift (inner ℂ (OriginalPrimitiveRankBalance.pairedColumn c h)
    (Flux.D (burnolCompletedMellinRieszVector c:BurnolL2)))=_
  rw [complete_price observation nontrivial half h nonnegative bounded]

end OriginalCompleteFeeProgram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalCompleteFeeProgram"
