import H0mework.Versions.V2.Arithmetic.RiemannRuntime.PairedOmegaEffectRowMaterial
import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Approximation
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Installation.Source

/-! The original occurrence fixes q₀, the R operation and exact Xi order before
emission. Its completed source executor supplies the coface; AST fees do not
replace the original physical update. -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCombCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
noncomputable section

abbrev Value (_ : Unit) := BurnolL2
abbrev Var (_ : Unit) := Unit

def code (action : BurnolL2 →L[ℂ] BurnolL2) : Nat → Expr Value Var ()
  | 0 => .var ()
  | count + 1 => .linear action.toLinearMap.toAddMonoidHom (code action count)

theorem code_eval (action : BurnolL2 →L[ℂ] BurnolL2) (count : Nat)
    (environment : Env Value Var) :
    (code action count).eval environment = (action ^ count) (environment () ()) := by
  induction count with
  | zero => rfl
  | succ count previous =>
      simp only [code, Expr.eval, previous, pow_succ', mul_apply_eq_comp]
      rfl

theorem code_budget (action : BurnolL2 →L[ℂ] BurnolL2) (count : Nat) :
    remaining (code action count) = count + 1 := by
  induction count with
  | zero => rfl
  | succ count previous => simp only [code, remaining, previous]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))

abbrev Base := CanonicalUnitArithmeticRoot.authoritativeRoot
abbrev Half := PLift (1/2 < observation.coordinate.re)

def reader (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()) :=
  let face := (runtimeEffectAt observation nontrivial occurrence).originalK
  let coordinate := originalKCoordinate face.coordinate face.belowOne
    (by change 1/2 < observation.coordinate.re; exact half.down)
  { environment := fun _ _ => (burnolPaCombApproximation 0 : BurnolL2)
    expression := code (burnolDirectRightResolventCLM coordinate)
      (generatedRiemannXiZeroOrder ActualAnalyticOwner face.coordinate) }

/-- The projection index is the original right-half proof fibre. Every field
is delegated to the existing complete-result source law for that fibre. -/
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

theorem result_value (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (result observation nontrivial half occurrence).2.2.1 =
      (burnolDirectRightResolventCLM (originalKCoordinate observation.coordinate
        (observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial).2 half.down) ^
        generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate)
          (burnolPaCombApproximation 0 : BurnolL2) := by
  have source := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value Base
    (reader observation nontrivial half) occurrence
  exact source.trans ((code_eval _ _ _).trans rfl)

theorem result_trace (half : Half observation) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (result observation nontrivial half occurrence).2.1.2.length =
      generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate + 1 := by
  have source := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history Base
    (reader observation nontrivial half) occurrence
  exact source.trans (code_budget _ _)

end
end OriginalKCombCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
