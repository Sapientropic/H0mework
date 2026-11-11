import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKBFiniteSourceCalculation

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCoefficientBSelfCalculation

open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open scoped InnerProductSpace

abbrev Value := OriginalKBFiniteCalculation.Value
abbrev Var := OriginalKBFiniteCalculation.Var
abbrev Base := OriginalKBFiniteCalculation.Base
abbrev Half := OriginalKBFiniteCalculation.Half
abbrev E := Expr Value Var ()
abbrev sourceEnvironment := OriginalKBFiniteCalculation.sourceEnvironment
abbrev fixedShift := OriginalKBFiniteCalculation.fixedShift
abbrev coordinate := OriginalKBFiniteCalculation.coordinate

private def linear (action : BurnolL2 →L[ℂ] BurnolL2) (input : E) : E :=
  .linear action.toLinearMap.toAddMonoidHom input
private def scale (scalar : ℂ) (input : E) : E :=
  linear (scalar • ContinuousLinearMap.id ℂ BurnolL2) input
private def sub (left right : E) : E := .add left (scale (-1) right)
private def fourier (input : E) : E :=
  linear fourierL2.toContinuousLinearEquiv.toContinuousLinearMap input

def elementaryEvenCode (c : BurnolCompletedMellinCoordinate) : E :=
  linear ((1/2 : ℂ) • (ContinuousLinearMap.id ℂ BurnolL2 + reflectL2.toContinuousLinearMap))
    (OriginalKBFiniteCalculation.elementaryCode c)

def coefficientSCode (c : BurnolCompletedMellinCoordinate) : E :=
  linear OriginalKBFiniteCalculation.wholeZeroMean
    (fourier (OriginalKBFiniteCalculation.coefficientSourceCode c))

/-- The original elementary source and its two calculated B corrections remain separate nodes. -/
def sourceKernelCode (c : BurnolCompletedMellinCoordinate) : E :=
  sub (.add (elementaryEvenCode c) (coefficientSCode c))
    (fourier (OriginalKBFiniteCalculation.coefficientSourceCode c))

def sourceCoreCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  sub (OriginalKBFiniteCalculation.boundaryActionCode c h (elementaryEvenCode c))
    (scale (1/2 : ℂ)
      (sub (OriginalKBFiniteCalculation.lossCode h (coefficientSCode c))
        (fourier (OriginalKBFiniteCalculation.lossCode h
          (OriginalKBFiniteCalculation.coefficientSourceCode c)))))

/-- The left inner-product slot is additive; no complex linearity of that slot is asserted. -/
def cotestAction : BurnolL2 →+ BurnolL2 →+ BurnolL2 where
  toFun := fun left =>
    { toFun := fun right => inner ℂ left right •
        (OriginalKBFiniteCalculation.constantCode.eval sourceEnvironment)
      map_zero' := by simp
      map_add' := by intro right next; simp only [inner_add_right, add_smul] }
  map_zero' := by
    apply AddMonoidHom.ext
    intro right
    change inner ℂ (0 : BurnolL2) right •
      (OriginalKBFiniteCalculation.constantCode.eval sourceEnvironment) = (0 : BurnolL2)
    simp
  map_add' := by
    intro left next
    apply AddMonoidHom.ext
    intro right
    change inner ℂ (left + next) right • (OriginalKBFiniteCalculation.constantCode.eval sourceEnvironment) =
      inner ℂ left right • (OriginalKBFiniteCalculation.constantCode.eval sourceEnvironment) +
        inner ℂ next right • (OriginalKBFiniteCalculation.constantCode.eval sourceEnvironment)
    rw [inner_add_left, add_smul]

def cotestCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  .bilinear cotestAction (sourceKernelCode c) (sourceCoreCode c h)

theorem elementary_even_code_eval (c : BurnolCompletedMellinCoordinate)
    (environment : Env Value Var) :
    (elementaryEvenCode c).eval environment =
      burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula c) := rfl

theorem coefficient_S_code_eval (c : BurnolCompletedMellinCoordinate)
    (environment : Env Value Var) :
    (coefficientSCode c).eval environment = OriginalKBFiniteCalculation.wholeZeroMean
      (fourierL2 ((OriginalKBFiniteCalculation.coefficientSourceCode c).eval environment)) := rfl

theorem source_kernel_code_eval (c : BurnolCompletedMellinCoordinate)
    (environment : Env Value Var) :
    (sourceKernelCode c).eval environment =
      (elementaryEvenCode c).eval environment + (coefficientSCode c).eval environment -
        fourierL2 ((OriginalKBFiniteCalculation.coefficientSourceCode c).eval environment) := by
  change (elementaryEvenCode c).eval environment + (coefficientSCode c).eval environment +
    (-1 : ℂ) • fourierL2 ((OriginalKBFiniteCalculation.coefficientSourceCode c).eval environment) = _
  simp only [neg_one_smul, sub_eq_add_neg]

theorem source_core_code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment : Env Value Var) :
    (sourceCoreCode c h).eval environment =
      (OriginalKBFiniteCalculation.boundaryActionCode c h (elementaryEvenCode c)).eval environment -
        (1/2 : ℂ) •
          ((OriginalKBFiniteCalculation.lossCode h (coefficientSCode c)).eval environment -
            fourierL2 ((OriginalKBFiniteCalculation.lossCode h
              (OriginalKBFiniteCalculation.coefficientSourceCode c)).eval environment)) := by
  change (OriginalKBFiniteCalculation.boundaryActionCode c h (elementaryEvenCode c)).eval environment +
    (-1 : ℂ) • ((1/2 : ℂ) •
      ((OriginalKBFiniteCalculation.lossCode h (coefficientSCode c)).eval environment +
        (-1 : ℂ) • fourierL2 ((OriginalKBFiniteCalculation.lossCode h
          (OriginalKBFiniteCalculation.coefficientSourceCode c)).eval environment))) = _
  simp only [neg_one_smul, sub_eq_add_neg]

theorem cotest_code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment : Env Value Var) :
    (cotestCode c h).eval environment =
      inner ℂ ((sourceKernelCode c).eval environment) ((sourceCoreCode c h).eval environment) •
        (OriginalKBFiniteCalculation.constantCode.eval environment) := rfl

theorem cotest_operation_budget (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    1 ≤ remaining (cotestCode c h) := by
  change 1 ≤ remaining (sourceKernelCode c) + remaining (sourceCoreCode c h) + 1
  omega

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))

def reader (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value) (Var:=Var) (sort:=()) :=
  { environment := sourceEnvironment
    expression := cotestCode (coordinate observation nontrivial half occurrence) fixedShift }

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
    (reader observation nontrivial half occurrence).environment = sourceEnvironment ∧
    (coordinate observation nontrivial half occurrence).value = observation.coordinate ∧
    (reader observation nontrivial half occurrence).expression =
      cotestCode (coordinate observation nontrivial half occurrence) fixedShift := ⟨rfl,rfl,rfl⟩

theorem result_value (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (result observation nontrivial half occurrence).2.2.1 =
      inner ℂ ((sourceKernelCode (coordinate observation nontrivial half occurrence)).eval sourceEnvironment)
        ((sourceCoreCode (coordinate observation nontrivial half occurrence) fixedShift).eval sourceEnvironment) •
          (OriginalKBFiniteCalculation.constantCode.eval sourceEnvironment) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value Base
    (reader observation nontrivial half) occurrence).trans (cotest_code_eval _ _ _)

theorem result_history (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (result observation nontrivial half occurrence).2.1.2.length =
      remaining (cotestCode (coordinate observation nontrivial half occurrence) fixedShift) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history Base
    (reader observation nontrivial half) occurrence

theorem result_history_nonempty (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    0 < (result observation nontrivial half occurrence).2.1.2.length := by
  rw [result_history]
  exact lt_of_lt_of_le (by norm_num : 0 < 1) (cotest_operation_budget _ _)

end OriginalKCoefficientBSelfCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
