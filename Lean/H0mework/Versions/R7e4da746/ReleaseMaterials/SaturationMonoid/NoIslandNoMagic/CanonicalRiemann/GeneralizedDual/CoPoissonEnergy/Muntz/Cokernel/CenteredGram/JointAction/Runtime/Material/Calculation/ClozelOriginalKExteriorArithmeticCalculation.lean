import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKCoefficientBSelfCalculation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingDual

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKExteriorArithmeticCalculation

open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalRieszFinitePairing.CoPoisson.Ward

abbrev Value := OriginalKBFiniteCalculation.Value
abbrev Var := OriginalKBFiniteCalculation.Var
abbrev Base := OriginalKBFiniteCalculation.Base
abbrev Half := OriginalKBFiniteCalculation.Half
abbrev E := Expr Value Var ()
abbrev sourceEnvironment := OriginalKBFiniteCalculation.sourceEnvironment
abbrev fixedShift := OriginalKBFiniteCalculation.fixedShift
abbrev coordinate := OriginalKBFiniteCalculation.coordinate

def columnCode (c : BurnolCompletedMellinCoordinate) : Fin 2 → E :=
  ![OriginalKBFiniteCalculation.coefficientSourceCode c,
    OriginalKCoefficientBSelfCalculation.coefficientSCode c]

/-- The whole exterior and centering subtrees remain the arithmetic input. -/
def fullSourceCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) (column : Fin 2) : E :=
  OriginalKBFiniteCalculation.lossCode h (columnCode c column)

/-- The third source is the complete existing core subtree, before any arithmetic action. -/
def inputCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : Fin 3 → E :=
  ![fullSourceCode c h 0, fullSourceCode c h 1,
    OriginalKCoefficientBSelfCalculation.sourceCoreCode c h]

/-- Side zero is the original finite integer programme with its continuous compensation;
side one is its independently constructed adjoint programme. -/
def sourceAction (cutoff : ℕ) : Fin 2 → BurnolL2 →L[ℂ] BurnolL2 :=
  ![CountingDual.sourceCLM cutoff, (CountingDual.sourceCLM cutoff).adjoint]

def code (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (sourceKind : Fin 3) (side : Fin 2) (cutoff : ℕ) : E :=
  .linear (sourceAction cutoff side).toLinearMap.toAddMonoidHom
    (inputCode c h sourceKind)

theorem code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (sourceKind : Fin 3) (side : Fin 2) (cutoff : ℕ) (environment : Env Value Var) :
    (code c h sourceKind side cutoff).eval environment =
      sourceAction cutoff side ((inputCode c h sourceKind).eval environment) := rfl

theorem code_operation_budget (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (sourceKind : Fin 3) (side : Fin 2) (cutoff : ℕ) :
    remaining (code c h sourceKind side cutoff) = remaining (inputCode c h sourceKind) + 1 := rfl

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2 * (n + 1))

/-- Half-plane face, actual source kind, arithmetic side, and finite cutoff. -/
abbrev Projection := Half observation × Fin 3 × Fin 2 × ℕ

def reader (half : Half observation) (sourceKind : Fin 3) (side : Fin 2) (cutoff : ℕ)
    {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()) :=
  { environment := sourceEnvironment
    expression := code (coordinate observation nontrivial half occurrence) fixedShift sourceKind side cutoff }

def component : SourceNativeProjectionLaw Base.toLedgerRoot.source where
  Projection := Projection observation
  ActiveAt := fun selected {_current} occurrence =>
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw Base
      (reader observation nontrivial selected.1 selected.2.1 selected.2.2.1 selected.2.2.2)).ActiveAt
        PUnit.unit occurrence
  InactiveAt := fun selected {_current} occurrence =>
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw Base
      (reader observation nontrivial selected.1 selected.2.1 selected.2.2.1 selected.2.2.2)).InactiveAt
        PUnit.unit occurrence
  classify := fun selected {_current} occurrence =>
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw Base
      (reader observation nontrivial selected.1 selected.2.1 selected.2.2.1 selected.2.2.2)).classify
        PUnit.unit occurrence
  PayloadAt := fun selected {_current} occurrence active =>
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw Base
      (reader observation nontrivial selected.1 selected.2.1 selected.2.2.1 selected.2.2.2)).PayloadAt
        PUnit.unit occurrence active
  project := fun selected {_current} occurrence active =>
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw Base
      (reader observation nontrivial selected.1 selected.2.1 selected.2.2.1 selected.2.2.2)).project
        PUnit.unit occurrence active

def result (half : Half observation) (sourceKind : Fin 3) (side : Fin 2) (cutoff : ℕ)
    {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt Base
    (reader observation nontrivial half sourceKind side cutoff) occurrence

theorem reader_source (half : Half observation) (sourceKind : Fin 3) (side : Fin 2) (cutoff : ℕ)
    {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (reader observation nontrivial half sourceKind side cutoff occurrence).environment = sourceEnvironment ∧
    (coordinate observation nontrivial half occurrence).value = observation.coordinate ∧
    (reader observation nontrivial half sourceKind side cutoff occurrence).expression =
      code (coordinate observation nontrivial half occurrence) fixedShift sourceKind side cutoff := ⟨rfl, rfl, rfl⟩

theorem result_value (half : Half observation) (sourceKind : Fin 3) (side : Fin 2) (cutoff : ℕ)
    {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (result observation nontrivial half sourceKind side cutoff occurrence).2.2.1 =
      (code (coordinate observation nontrivial half occurrence) fixedShift sourceKind side cutoff).eval
        sourceEnvironment :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value Base
    (reader observation nontrivial half sourceKind side cutoff) occurrence

theorem result_history (half : Half observation) (sourceKind : Fin 3) (side : Fin 2) (cutoff : ℕ)
    {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (result observation nontrivial half sourceKind side cutoff occurrence).2.1.2.length =
      remaining (code (coordinate observation nontrivial half occurrence) fixedShift sourceKind side cutoff) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history Base
    (reader observation nontrivial half sourceKind side cutoff) occurrence

theorem result_history_nonempty (half : Half observation) (sourceKind : Fin 3) (side : Fin 2) (cutoff : ℕ)
    {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    0 < (result observation nontrivial half sourceKind side cutoff occurrence).2.1.2.length := by
  rw [result_history, code_operation_budget]
  omega

def paidTrace (half : Half observation) (sourceKind : Fin 3) (side : Fin 2) (cutoff : ℕ)
    {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    Trace sourceEnvironment
      (code (coordinate observation nontrivial half occurrence) fixedShift sourceKind side cutoff)
      (result observation nontrivial half sourceKind side cutoff occurrence).2.1.1 :=
  (result observation nontrivial half sourceKind side cutoff occurrence).2.1.2

theorem result_endpoint_value (half : Half observation) (sourceKind : Fin 3) (side : Fin 2) (cutoff : ℕ)
    {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    ((result observation nontrivial half sourceKind side cutoff occurrence).2.1.1).eval sourceEnvironment =
      (result observation nontrivial half sourceKind side cutoff occurrence).2.2.1 :=
  (paidTrace observation nontrivial half sourceKind side cutoff occurrence).sound.symm.trans
    (result_value observation nontrivial half sourceKind side cutoff occurrence).symm

theorem result_source_material (half : Half observation) (sourceKind : Fin 3) (side : Fin 2) (cutoff : ℕ)
    {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (result observation nontrivial half sourceKind side cutoff occurrence).2.2.2 =
      RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt Base occurrence := rfl

end OriginalKExteriorArithmeticCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
