import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKForcedInverseSourceProgram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKContactClosureSourceCalculation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusForcedPriceConsumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKForcedInverseSourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalRieszSource OriginalRieszFiniteSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource
open OriginalKSourceResolventReconstruction OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalWholeDebtRPowerWaveDilationSource
open private conjugate_twice from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusWholeLoopRSource
namespace G
export OriginalWholeDebtRJointMobiusContactPsiPriceSource
  (contactDiagonal contactCross contactPayment psiPayment ordinaryMean powerUnitPrice endpointCharge nativeGamma)
end G
namespace N
export OriginalWholeDebtRJointMobiusForcedInverseSource (calculatedForcing forcingResponse forcingInput forcingNext)
end N
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "Eq" => burnolQuarterZeroExtension
local notation "q" => (1/4 : ℝ)
variable (c : BurnolCompletedMellinCoordinate) (originalPa originalUnit : BurnolL2)
local notation "env" => sourceEnvironment c originalPa originalUnit

theorem atCoordinate_opposite (side : Fin 2) : atCoordinate c (opposite side)=barC (atCoordinate c side) := by
  fin_cases side
  · rfl
  · exact (conjugate_twice c).symm

theorem opposite_kernel (side : Fin 2) : env () (opposite side,15)=generatedK (barC (atCoordinate c side)) := by
  change generatedK (atCoordinate c (opposite side))=_
  rw [atCoordinate_opposite]

theorem wholeS_faithful (value : M) : wholeS (Eq (value : Hq))=Eq (S value : Hq) := rfl

theorem matrix_read_faithful (d : BurnolCompletedMellinCoordinate) (value : M) :
    matrixRead d (Eq (value : Hq))=inner ℂ (SingularCounting.centeredPower (barC d)) value := by
  change inner ℂ (SingularCounting.centeredPower (barC d))
    (Constructor.zeroMean (burnolQuarterRestriction (Eq (value : Hq))))=_
  rw [burnolQuarterRestriction_zeroExtension]
  have fixed : Constructor.zeroMean (value : Hq)=value := by
    apply Subtype.ext
    exact Submodule.starProjection_eq_self_iff.mpr value.property
  rw [fixed]

theorem diagonal_eval (environment : Env Value Var) (input : E) (value : M)
    (read : input.eval environment=Eq (value : Hq)) :
    (diagonalCode input).eval environment=Eq (value+S (burnolMeanZeroBlockInverse (S value)) : Hq) := by
  change input.eval environment+wholeS (OriginalKBFiniteCalculation.wholeBInverse
    (wholeS (input.eval environment)))=_
  rw [read,wholeS_faithful,OriginalKBFiniteCalculation.wholeBInverse_faithful,wholeS_faithful]
  exact (map_add Eq (value : Hq) (S (burnolMeanZeroBlockInverse (S value)) : Hq)).symm

theorem cross_eval (environment : Env Value Var) (input : E) (value : M)
    (read : input.eval environment=Eq (value : Hq)) :
    (crossCode input).eval environment=Eq (S (burnolMeanZeroBlockInverse value) : Hq) := by
  change wholeS (OriginalKBFiniteCalculation.wholeBInverse (input.eval environment))=_
  rw [read,OriginalKBFiniteCalculation.wholeBInverse_faithful,wholeS_faithful]

theorem matrix_code_value (side : Fin 2) (input : E) (value : M)
    (read : input.eval env=Eq (value : Hq)) :
    (matrixCode c side input).eval env=
      inner ℂ (SingularCounting.centeredPower (barC (barC (atCoordinate c side)))) value •
        fourierL2 (generatedK (barC (atCoordinate c side))) := by
  change matrixRead (barC (atCoordinate c side)) (input.eval env) •
    fourierL2 (env () (opposite side,15))=_
  rw [read,matrix_read_faithful,opposite_kernel]

theorem actual_contact_payment_code (side : Fin 2) :
    (contactPaymentCode c side).eval env=G.contactPayment (atCoordinate c side)
      (barC (atCoordinate c side)) • fourierL2 (generatedK (barC (atCoordinate c side))) := by
  have dq : (diagonalCode (.var (side,3))).eval env=Eq (G.contactDiagonal q : Hq) :=
    diagonal_eval env (.var (side,3)) (TwoPieceFourierAction.eta q) rfl
  have dp : (diagonalCode (.var (side,4))).eval env=Eq (G.contactDiagonal junctionPoint : Hq) :=
    diagonal_eval env (.var (side,4)) (TwoPieceFourierAction.eta junctionPoint) rfl
  have cq : (crossCode (.var (side,3))).eval env=Eq (G.contactCross q : Hq) :=
    cross_eval env (.var (side,3)) (TwoPieceFourierAction.eta q) rfl
  have cp : (crossCode (.var (side,4))).eval env=Eq (G.contactCross junctionPoint : Hq) :=
    cross_eval env (.var (side,4)) (TwoPieceFourierAction.eta junctionPoint) rfl
  change ((sourceTrace (atCoordinate c side) 0 • (matrixCode c side (diagonalCode (.var (side,3)))).eval env+
    (-1 : ℂ) • ((((junctionPoint/q : ℝ) : ℂ)*sourceJump (atCoordinate c side) 0) •
      (matrixCode c side (diagonalCode (.var (side,4)))).eval env))+
    sourceTrace (atCoordinate c side) 1 • (matrixCode c side (crossCode (.var (side,3)))).eval env)+
    (-1 : ℂ) • ((((junctionPoint/q : ℝ) : ℂ)*sourceJump (atCoordinate c side) 1) •
      (matrixCode c side (crossCode (.var (side,4)))).eval env)=_
  rw [matrix_code_value c originalPa originalUnit side _ _ dq,
    matrix_code_value c originalPa originalUnit side _ _ dp,
    matrix_code_value c originalPa originalUnit side _ _ cq,
    matrix_code_value c originalPa originalUnit side _ _ cp]
  unfold OriginalWholeDebtRJointMobiusContactPsiPriceSource.contactPayment
  module

theorem actual_gamma_field_code (side : Fin 2) :
    (gammaFieldCode c side).eval env=G.nativeGamma (atCoordinate c side)
      (barC (atCoordinate c side)) • fourierL2 (generatedK (barC (atCoordinate c side))) := by
  have v := matrix_code_value c originalPa originalUnit side (.var (side,2)) PsiDrive.psiV rfl
  have u := matrix_code_value c originalPa originalUnit side (.var (side,1)) PsiDrive.psiU rfl
  change ((2 : ℂ) • (((-Kernel.A (atCoordinate c side)) •
    (matrixCode c side (.var (side,2))).eval env+
    (-Kernel.beta (atCoordinate c side)) • (matrixCode c side (.var (side,1))).eval env)+
    (-1 : ℂ) • (contactPaymentCode c side).eval env)+
    (-1 : ℂ) • ((2*(2*(q : ℂ)^(star (barC (atCoordinate c side)).value)*sourceTrace (atCoordinate c side) 1-
      2*(junctionPoint : ℂ)^(star (barC (atCoordinate c side)).value)*sourceJump (atCoordinate c side) 1)) •
      fourierL2 (env () (opposite side,15))))+
    (2*(sourceTrace (atCoordinate c side) 1-((junctionPoint/q : ℝ) : ℂ)*sourceJump (atCoordinate c side) 1)*
      (2*(q : ℂ)^(star (barC (atCoordinate c side)).value)/(star (barC (atCoordinate c side)).value))) •
      fourierL2 (env () (opposite side,15))=_
  rw [v,u,actual_contact_payment_code,opposite_kernel]
  unfold OriginalWholeDebtRJointMobiusContactPsiPriceSource.nativeGamma
    OriginalWholeDebtRJointMobiusContactPsiPriceSource.psiPayment
    OriginalWholeDebtRJointMobiusContactPsiPriceSource.ordinaryMean
    OriginalWholeDebtRJointMobiusContactPsiPriceSource.powerUnitPrice
    OriginalWholeDebtRJointMobiusContactPsiPriceSource.endpointCharge
  module

theorem actual_effect_code (side : Fin 2) :
    (effectCode c side).eval env=OriginalWholeDebtRAdjointContactSource.sourceEffect
      (atCoordinate c side) (barC (atCoordinate c side)) := by
  unfold effectCode
  rw [Expr.eval_subst]
  have binding : (fun sort index => (contactBinding side sort index).eval env)=
      OriginalKContactClosureSourceCalculation.sourceEnvironment (atCoordinate c side) := by
    funext sort index
    cases sort
    fin_cases index <;> rfl
  rw [binding]
  exact OriginalKContactClosureSourceCalculation.actual_effect_code _ _

theorem actual_correction_raw_code (side : Fin 2) :
    (correctionRawCode side).eval env=BandFullStockEuler.correctionRaw (atCoordinate c side) := rfl

theorem actual_paired_source_code (side : Fin 2) :
    (pairedSourceCode c side).eval env=pairedSource (atCoordinate c side) junctionShift := by
  change (1/2 : ℂ) •
    (fourierL2 (coupling1 (atCoordinate c side) •
      profileIntegral (barC (atCoordinate c side)) (-junctionShift)+
      coupling0 (atCoordinate c side) •
      fourierProfileIntegral (barC (atCoordinate c side)) (-junctionShift))+
    fourierL2 (coupling1 (atCoordinate c side) •
      profileIntegral (barC (atCoordinate c side)) junctionShift+
      coupling0 (atCoordinate c side) •
      fourierProfileIntegral (barC (atCoordinate c side)) junctionShift))=_
  simp only [pairedSource,singleSource,neg_neg]

variable (pa_source : originalPa=OriginalWholeDebtRJointMobiusSource.paWave c)
variable (unit_source : originalUnit=burnolUnitTailResponse c 4)
include pa_source unit_source

theorem actual_correction_code (side : Fin 2) :
    (correctionCode c side).eval env=OriginalWholeDebtRJointMobiusCoupledCayleySource.correctionInput
      (atCoordinate c side) := by
  fin_cases side
  · change originalPa+OriginalWholeDebtRJointMobiusUnitSource.unitCoefficient c • originalUnit=_
    rw [pa_source,unit_source]
    rfl
  · rfl

theorem actual_forcing_code (side : Fin 2) :
    (forcingCode c side).eval env=N.calculatedForcing (atCoordinate c side) := by
  have raw : (correctionRawCode (opposite side)).eval env=
      BandFullStockEuler.correctionRaw (barC (atCoordinate c side)) := by
    rw [actual_correction_raw_code,atCoordinate_opposite]
  have corr : (correctionCode c (opposite side)).eval env=
      OriginalWholeDebtRJointMobiusCoupledCayleySource.correctionInput (barC (atCoordinate c side)) := by
    rw [actual_correction_code c originalPa originalUnit pa_source unit_source,atCoordinate_opposite]
  change (((((sourceCoupling (atCoordinate c side)*
    (OriginalWholeDebtRJointMobiusSource.character (atCoordinate c side)-
      OriginalWholeDebtRJointMobiusSource.character (barC (atCoordinate c side)))) •
    fourierL2 (env () (opposite side,15))+
    (-1 : ℂ) • (sourceCoupling (atCoordinate c side) •
      fourierL2 ((correctionRawCode (opposite side)).eval env)))+
    (damping (atCoordinate c side) : ℂ) • (pairedSourceCode c side).eval env)+
    (1/2 : ℂ) • ((gammaFieldCode c side).eval env+
      OriginalKCombPhysicalAction.physicalRemainder ((effectCode c side).eval env)))+
    sourceCoupling (atCoordinate c side) • fourierL2 ((correctionCode c (opposite side)).eval env))+
    (-1 : ℂ) • ((sourceCayley (barC (atCoordinate c side))).adjoint
      ((correctionCode c side).eval env))=_
  rw [opposite_kernel,raw,actual_paired_source_code,actual_gamma_field_code,actual_effect_code,corr,
    actual_correction_code c originalPa originalUnit pa_source unit_source,sourceCayley_actual_adjoint]
  simp only [OriginalWholeDebtRJointMobiusForcedInverseSource.calculatedForcing,
    OriginalWholeDebtRJointMobiusCoupledCayleySource.coupling,sub_eq_add_neg,neg_one_smul]

theorem actual_response_code :
    (responseCode c).eval env=N.forcingResponse c := by
  change (((4*(sourceDamping c)^2*‖generatedK c‖^2*
    ‖hPowerPhysicalCorrection (barC c)‖^2 : ℝ) : ℂ)⁻¹) •
    (sourceCoupling c • fourierL2 ((forcingCode c 1).eval env)+
      sourceCayley (barC c) ((forcingCode c 0).eval env))=_
  rw [actual_forcing_code c originalPa originalUnit pa_source unit_source,
    actual_forcing_code c originalPa originalUnit pa_source unit_source]
  rfl

theorem actual_input_code : (inputCode c).eval env=N.forcingInput c := by
  change fourierL2 ((responseCode c).eval env)=_
  rw [actual_response_code c originalPa originalUnit pa_source unit_source]
  rfl

theorem actual_code : (code c).eval env=N.forcingNext c := by
  change burnolDirectRightResolventCLM c ((inputCode c).eval env)=_
  rw [actual_input_code c originalPa originalUnit pa_source unit_source]
  rfl

end OriginalKForcedInverseSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
