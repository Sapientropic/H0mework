import H0mework.Versions.R7e4da746.Arithmetic.RiemannRuntime.Calculation.ClozelOriginalKCombSourceCalculation
import H0mework.Versions.R7e4da746.Arithmetic.RieszSourceKernel.Core
import H0mework.Versions.R7e4da746.Arithmetic.RieszEuler.Scalar

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKBFiniteCalculation

open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalRieszSource
open scoped InnerProductSpace
noncomputable section

abbrev Value := OriginalKCombCalculation.Value
abbrev Var := OriginalKCombCalculation.Var
abbrev Base := CanonicalUnitArithmeticRoot.authoritativeRoot
abbrev Half := OriginalKCombCalculation.Half
abbrev E := Expr Value Var ()
local notation "q" => (1/4 : ℝ)
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

/-- Only the original quarter representation is changed; the source operation is B inverse. -/
def wholeBInverse : BurnolL2 →L[ℂ] BurnolL2 :=
  burnolQuarterZeroExtension.comp ((Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule).comp
    (burnolMeanZeroBlockInverse.comp (Constructor.zeroMean.comp burnolQuarterRestriction)))

def wholeZeroMean : BurnolL2 →L[ℂ] BurnolL2 :=
  burnolQuarterZeroExtension.comp ((Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule).comp
    (Constructor.zeroMean.comp burnolQuarterRestriction))

def wholeCut : BurnolL2 →L[ℂ] BurnolL2 := burnolQuarterZeroExtension.comp burnolQuarterRestriction

theorem wholeBInverse_faithful (value : M) :
    wholeBInverse (burnolQuarterZeroExtension (value : Hq)) =
      burnolQuarterZeroExtension (burnolMeanZeroBlockInverse value : Hq) := by
  change burnolQuarterZeroExtension
    (Constructor.zeroMean (burnolQuarterRestriction (burnolQuarterZeroExtension (value : Hq))) |>
      burnolMeanZeroBlockInverse |>.val) = _
  rw [burnolQuarterRestriction_zeroExtension]
  have fixed : Constructor.zeroMean (value : Hq) = value := by
    apply Subtype.ext
    exact Submodule.starProjection_eq_self_iff.mpr value.property
  rw [fixed]

theorem wholeZeroMean_faithful (value : M) :
    wholeZeroMean (burnolQuarterZeroExtension (value : Hq)) = burnolQuarterZeroExtension (value : Hq) := by
  change burnolQuarterZeroExtension (Constructor.zeroMean
    (burnolQuarterRestriction (burnolQuarterZeroExtension (value : Hq))) : Hq) = _
  rw [burnolQuarterRestriction_zeroExtension]
  congr 1
  exact Submodule.starProjection_eq_self_iff.mpr value.property

private def linear (action : BurnolL2 →L[ℂ] BurnolL2) (input : E) : E :=
  .linear action.toLinearMap.toAddMonoidHom input
private def scale (scalar : ℂ) (input : E) : E := linear (scalar • ContinuousLinearMap.id ℂ BurnolL2) input
private def sub (left right : E) : E := .add left (scale (-1) right)
private def fourier (input : E) : E := linear fourierL2.toContinuousLinearEquiv.toContinuousLinearMap input
private def dilation (h : ℝ) (input : E) : E :=
  linear (burnolMultiplicativeDilation h).toContinuousLinearEquiv.toContinuousLinearMap input
private def zeroMean (input : E) : E := linear wholeZeroMean input
private def bInverse (input : E) : E := linear wholeBInverse input
private def sAction (input : E) : E := zeroMean (fourier input)
private def hAction (h : ℝ) (input : E) : E := zeroMean (dilation h input)

def sourceRate (c : BurnolCompletedMellinCoordinate) : ℂ := star c.value - 1/2
def conjugateCoordinate (c : BurnolCompletedMellinCoordinate) : BurnolCompletedMellinCoordinate :=
  ⟨star c.value, by simpa using c.rightHalf, by simpa using c.belowOne⟩

/-- The environment contains eta; C and the elementary Mellin source are primitive source data. -/
def sourceEnvironment : Env Value Var := fun _ _ => burnolQuarterZeroExtension (Response.eta : Hq)
def etaCode : E := .var ()
def constantCode : E := .const (burnolQuarterZeroExtension (intervalConstant q))
def elementaryCode (c : BurnolCompletedMellinCoordinate) : E := .const (burnolAmbientCompletedMellinKernelFormula c)
def uCode : E := bInverse etaCode
def vCode : E := sAction uCode

def commutatorCode (h : ℝ) (input : E) : E := sub (hAction h (sAction input)) (hAction (-h) (sAction input))
def driveUCode (h : ℝ) : E := .add (.add (hAction h etaCode) (commutatorCode h vCode)) (sAction (commutatorCode h uCode))
def driveVCode (h : ℝ) : E := .add (.add (hAction h (sAction etaCode))
  (commutatorCode h (sub uCode etaCode))) (sAction (commutatorCode h vCode))
def firstUCode (h : ℝ) : E := bInverse (driveUCode h)
def secondUCode (h : ℝ) : E := sAction (firstUCode h)
def firstVCode (h : ℝ) : E := bInverse (driveVCode h)
def secondVCode (h : ℝ) : E := sAction (firstVCode h)

def exteriorCode (h : ℝ) (input : E) : E := sub (dilation (-h) input) (linear wholeCut (dilation (-h) input))
def centeringCode (h : ℝ) (input : E) : E := sub (linear wholeCut (dilation (-h) input)) (hAction (-h) input)
def lossCode (h : ℝ) (input : E) : E := .add (exteriorCode h input) (centeringCode h input)

def f0Code (c : BurnolCompletedMellinCoordinate) : E :=
  .add (sub (fourier uCode) vCode) (scale (1/2-sourceRate c) constantCode)
def f0MinusCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  .add (sub (sub (fourier (firstUCode h)) (secondUCode h)) (lossCode h vCode))
    (scale (1/2-sourceRate c) (dilation (-h) constantCode))
def f0PlusCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  .add (.add (sub (fourier (.add (secondVCode h) (hAction (-h) etaCode))) (firstVCode h))
    (fourier (lossCode h uCode))) (scale (1/2-sourceRate c) (dilation h constantCode))

def forcingCode (c : BurnolCompletedMellinCoordinate) : Fin 2 → E :=
  ![f0Code c, .add (fourier (f0Code c)) (scale (2*sourceRate c) (fourier constantCode))]
def forcingPlusCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : Fin 2 → E :=
  ![f0PlusCode c h, .add (fourier (f0MinusCode c h))
    (scale (2*sourceRate c) (dilation h (fourier constantCode)))]
def forcingMinusCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : Fin 2 → E :=
  ![f0MinusCode c h, .add (fourier (f0PlusCode c h))
    (scale (2*sourceRate c) (dilation (-h) (fourier constantCode)))]

def sourceInputCode (c : BurnolCompletedMellinCoordinate) (forcing : E) : E :=
  .add (scale (-(1/2 : ℂ)) forcing) (scale ((1/4 : ℂ)*(c.value-star c.value))
    (linear (burnolDirectRightResolventCLM (conjugateCoordinate c)) forcing))

def inputColumnCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : E :=
  sub (scale (pairedMellinTranslationCharacter c.value h) (sourceInputCode c (forcingCode c i)))
    (scale (1/2 : ℂ) (.add (sourceInputCode c (forcingPlusCode c h i))
      (sourceInputCode c (forcingMinusCode c h i))))

/-- The original single B source is generated before its two endpoint coefficient reads. -/
def coefficientSourceCode (c : BurnolCompletedMellinCoordinate) : E :=
  bInverse (zeroMean (fourier (linear ((1/2 : ℂ) • (ContinuousLinearMap.id ℂ BurnolL2 +
    reflectL2.toContinuousLinearMap)) (elementaryCode c))))

def endpointRead : BurnolL2 →L[ℂ] ℂ :=
  (4 : ℂ) • innerSL ℂ (burnolQuarterZeroExtension (Constructor.endpointColumn (-q) : Hq))

def endpointAction : BurnolL2 →+ BurnolL2 →+ BurnolL2 where
  toFun := fun left => (endpointRead left • ContinuousLinearMap.id ℂ BurnolL2).toLinearMap.toAddMonoidHom
  map_zero' := by ext right; simp
  map_add' := by intro left right; ext value; simp [add_smul]

def coefficientAActionCode (c : BurnolCompletedMellinCoordinate) (input : E) : E :=
  .add (scale (star c.value * GapEuler.gapMean q c) input)
    (.bilinear endpointAction (coefficientSourceCode c) input)
def coefficientBetaActionCode (c : BurnolCompletedMellinCoordinate) (input : E) : E :=
  .add (scale (burnolRieszFourierForcingRaw c q) input)
    (.bilinear endpointAction (sAction (coefficientSourceCode c)) input)

def boundaryInputCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  .add (coefficientAActionCode c (inputColumnCode c h 0))
    (coefficientBetaActionCode c (inputColumnCode c h 1))
def boundaryActionCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) (input : E) : E :=
  sub (scale (pairedMellinTranslationCharacter c.value h) input)
    (scale (1/2 : ℂ) (.add (dilation h input) (dilation (-h) input)))
def jumpCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  .add (coefficientAActionCode c (boundaryActionCode c h constantCode))
    (coefficientBetaActionCode c (boundaryActionCode c h (scale (-1) (fourier constantCode))))

/-- The completed normal is absent from every primitive leaf. -/
def code (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  .add (linear (burnolDirectRightResolventCLM c) (boundaryInputCode c h)) (jumpCode c h)

private theorem linear_eval (action : BurnolL2 →L[ℂ] BurnolL2) (input : E) (environment : Env Value Var) :
    (linear action input).eval environment = action (input.eval environment) := rfl
private theorem scale_eval (scalar : ℂ) (input : E) (environment : Env Value Var) :
    (scale scalar input).eval environment = scalar • input.eval environment := rfl
private theorem sub_eval (left right : E) (environment : Env Value Var) :
    (sub left right).eval environment = left.eval environment-right.eval environment := by
  change left.eval environment + (-1 : ℂ) • right.eval environment = _
  simp only [neg_one_smul, sub_eq_add_neg]

theorem source_input_code_eval (c : BurnolCompletedMellinCoordinate) (forcing : E)
    (environment : Env Value Var) :
    (sourceInputCode c forcing).eval environment = -(1/2 : ℂ) • forcing.eval environment +
      ((1/4 : ℂ)*(c.value-star c.value)) •
        burnolDirectRightResolvent (star c.value/2) (forcing.eval environment) := rfl

theorem loss_code_eval (h : ℝ) (input : E) (environment : Env Value Var) :
    (lossCode h input).eval environment =
      (burnolMultiplicativeDilation (-h) (input.eval environment) -
        wholeCut (burnolMultiplicativeDilation (-h) (input.eval environment))) +
      (wholeCut (burnolMultiplicativeDilation (-h) (input.eval environment)) -
        wholeZeroMean (burnolMultiplicativeDilation (-h) (input.eval environment))) := by
  change (burnolMultiplicativeDilation (-h) (input.eval environment) +
      (-1 : ℂ) • wholeCut (burnolMultiplicativeDilation (-h) (input.eval environment))) +
    (wholeCut (burnolMultiplicativeDilation (-h) (input.eval environment)) +
      (-1 : ℂ) • wholeZeroMean (burnolMultiplicativeDilation (-h) (input.eval environment))) = _
  simp only [neg_one_smul, sub_eq_add_neg]

theorem coefficient_A_code_eval (c : BurnolCompletedMellinCoordinate) (input : E)
    (environment : Env Value Var) :
    (coefficientAActionCode c input).eval environment =
      (star c.value * GapEuler.gapMean q c + endpointRead ((coefficientSourceCode c).eval environment)) •
        input.eval environment := by
  change _ + _ = _
  rw [add_smul]
  rfl

theorem coefficient_beta_code_eval (c : BurnolCompletedMellinCoordinate) (input : E)
    (environment : Env Value Var) :
    (coefficientBetaActionCode c input).eval environment =
      (burnolRieszFourierForcingRaw c q + endpointRead
        (wholeZeroMean (fourierL2 ((coefficientSourceCode c).eval environment)))) • input.eval environment := by
  rw [add_smul]
  rfl

theorem normal_code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ) (environment : Env Value Var) :
    (code c h).eval environment =
      burnolDirectRightResolvent (c.value/2) ((boundaryInputCode c h).eval environment) +
        (jumpCode c h).eval environment := rfl

theorem original_B_source_eval : uCode.eval sourceEnvironment = burnolQuarterZeroExtension (Response.u : Hq) :=
  wholeBInverse_faithful Response.eta

theorem original_S_source_eval : vCode.eval sourceEnvironment = burnolQuarterZeroExtension (Response.v : Hq) := by
  change wholeZeroMean (fourierL2 (uCode.eval sourceEnvironment)) = _
  rw [original_B_source_eval]
  rfl

theorem code_operation_budget (c : BurnolCompletedMellinCoordinate) (h : ℝ) : 2 ≤ remaining (code c h) := by
  change 2 ≤ remaining (linear (burnolDirectRightResolventCLM c) (boundaryInputCode c h)) +
    remaining (jumpCode c h) + 1
  change 2 ≤ (remaining (boundaryInputCode c h)+1) + remaining (jumpCode c h)+1
  omega

def fixedShift : ℝ := Real.log stageZeroSonineQ
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))

def coordinate (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) : BurnolCompletedMellinCoordinate :=
  let face := (runtimeEffectAt observation nontrivial occurrence).originalK
  originalKCoordinate face.coordinate face.belowOne (by change 1/2 < observation.coordinate.re; exact half.down)

def reader (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value) (Var:=Var) (sort:=()) :=
  { environment := sourceEnvironment
    expression := code (coordinate observation nontrivial half occurrence) fixedShift }

def component : SourceNativeProjectionLaw Base.toLedgerRoot.source where
  Projection := Half observation
  ActiveAt := fun half {_current} occurrence =>
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw Base
      (reader observation nontrivial half)).ActiveAt PUnit.unit occurrence
  InactiveAt := fun half {_current} occurrence =>
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw Base
      (reader observation nontrivial half)).InactiveAt PUnit.unit occurrence
  classify := fun half {_current} occurrence =>
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw Base
      (reader observation nontrivial half)).classify PUnit.unit occurrence
  PayloadAt := fun half {_current} occurrence active =>
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw Base
      (reader observation nontrivial half)).PayloadAt PUnit.unit occurrence active
  project := fun half {_current} occurrence active =>
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw Base
      (reader observation nontrivial half)).project PUnit.unit occurrence active

def result (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt Base
    (reader observation nontrivial half) occurrence

theorem reader_source (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (reader observation nontrivial half occurrence).environment () () =
      burnolQuarterZeroExtension (Response.eta : Hq) ∧
    (coordinate observation nontrivial half occurrence).value = observation.coordinate ∧
    (reader observation nontrivial half occurrence).expression =
      code (coordinate observation nontrivial half occurrence) fixedShift := ⟨rfl,rfl,rfl⟩

theorem result_value (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (result observation nontrivial half occurrence).2.2.1 =
      burnolDirectRightResolvent ((coordinate observation nontrivial half occurrence).value/2)
        ((boundaryInputCode (coordinate observation nontrivial half occurrence) fixedShift).eval sourceEnvironment) +
      (jumpCode (coordinate observation nontrivial half occurrence) fixedShift).eval sourceEnvironment :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value Base
    (reader observation nontrivial half) occurrence).trans (normal_code_eval _ _ _)

theorem result_history (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (result observation nontrivial half occurrence).2.1.2.length =
      remaining (code (coordinate observation nontrivial half occurrence) fixedShift) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history Base
    (reader observation nontrivial half) occurrence

theorem result_history_nonempty (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    0 < (result observation nontrivial half occurrence).2.1.2.length := by
  rw [result_history]
  exact lt_of_lt_of_le (by norm_num : 0 < 2) (code_operation_budget _ _)

end
end OriginalKBFiniteCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
