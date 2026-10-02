import H0mework.Versions.R2.Physics.MotherProgrammesFormation.FullAuxiliaryConsumer
import H0mework.Versions.R2.Realization.Completion.HistoryInstallation

set_option autoImplicit false
set_option synthInstance.maxSize 4096

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ActualFormation

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open CofinalHistorySettlement CofinalHistorySettlementFace
open Stage9C.Revision StageNineHolonomicField StageNineEnrichedProofFreeSource
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction
open StageNineDiracDualFormNativeMotherAction
open SU7MotherLieAlgebra StageNineDynamicBreakingVacuum DiracExteriorMatterAction

noncomputable section

abbrev WholeCoordinates :=
  (BasePoint → LorentzianCoframe) × LorentzConnectionField ×
  (BasePoint → PhysicalBivector) × (BasePoint → PhysicalBivector) ×
  P286ConnectionField × (BasePoint → Fin 6 → P286LieBlockData) ×
  (BasePoint → ScalarCoordinateCarrier) × (BasePoint → DiracExteriorMatterCarrier) ×
  (BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)

def wholeCoordinates : StageNineHolonomicConfiguration ≃ WholeCoordinates where
  toFun field := ⟨field.coframe, field.gravityConnection, field.gravityAuxiliary,
    field.gravitySimplicityMultiplier, field.gaugeConnection, field.gaugeAuxiliary,
    field.scalar, field.matter, field.conjugateMatter⟩
  invFun data :=
    let ⟨coframe, gravityConnection, gravityAuxiliary, gravitySimplicityMultiplier,
      gaugeConnection, gaugeAuxiliary, scalar, matter, conjugateMatter⟩ := data
    ⟨coframe, gravityConnection, gravityAuxiliary, gravitySimplicityMultiplier,
      gaugeConnection, gaugeAuxiliary, scalar, matter, conjugateMatter⟩
  left_inv field := by cases field; rfl
  right_inv data := by
    rcases data with ⟨_, _, _, _, _, _, _, _, _⟩
    rfl

abbrev ActualCoordinates := WholeCoordinates × (StageNineChart → BasePoint → ℝ)

def actualCoordinates (current : SpinPair.Current) : ActualCoordinates :=
  let field := Recognition.wholeField current
  ⟨wholeCoordinates field, fun chart point =>
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity ClockBF.motherSource chart point
      (toContinuumPointField field point)⟩

abbrev Generator := ℕ × SpinPair.Current

def nextGenerator (generator : Generator) : Generator :=
  (generator.1 + 1, SpinPair.next generator.2)

def continuation : PresentedRelationEventAt Generator →
    RootedAccountedUnfolding (PresentedRelationEventAt Generator)
  | .generator value => .zero (.generator (nextGenerator value))
  | .relation value => .zero (.relation (Finsupp.mapDomain nextGenerator value))

def historyLaw : SourceNativeCofinalHistoryMaterialLaw
    SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot.source :=
  SourceNativeCofinalHistoryMaterialLaw.create Generator
    (fun occurrence => .zero occurrence) (fun _ => rfl)
    (fun {current} _ => .zero (.generator (0, current)))
    (fun _ => .zero continuation)

def generated : SpinPair.Current → ℕ → SpinPair.Current
  | current, 0 => current
  | current, step + 1 => SpinPair.next (generated current step)

theorem frontier_generated {current : SpinPair.Current}
    (occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt current) (step : ℕ) :
    ((historyLaw.historyAt occurrence).observation step).frontier =
      [.generator (step, generated current step)] := by
  induction step with
  | zero => rfl
  | succ step ih =>
    rw [RootGeneratedCofinalHistoryAt.observation_succ,
      RootedAccountedUnfolding.frontier_advance, ih]
    rfl

theorem generated_native_family (prepared : MaterialState) (step : ℕ) :
    generated (.running prepared) step = .running (NativeFamily.stateAt prepared step) := by
  induction step with
  | zero => rfl
  | succ step ih => rw [generated, ih]; rfl


end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ActualFormation
