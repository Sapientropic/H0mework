import Mathlib.Tactic
import H0mework.Foundation.Relations.ConsumerFace
import H0mework.Chemistry.LAlanineForce.BoundForceUpdate

/-! # Native material next and a strict graph/energy kernel escape

This occurrence consists of the actual current and the model-generated next.
The coordinate face is computed from the current force. Independent readers
consume the recorded target coordinates, SCF energy, graph and inventory.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Force.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Force.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Force.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation

noncomputable section

theorem normalizer_exact : normalizer updateReadout.gradient = 182483873335 := by
  have maximum : maximumSquaredNorm updateReadout.gradient = 33300364027197513653877 := by
    decide
  have squareRoot : Nat.sqrt 33300364027197513653877 = 182483873334 := by
    symm
    apply Nat.eq_sqrt.mpr
    constructor <;> decide
  simp only [normalizer, ceilingSqrt, maximum, squareRoot]
  decide

theorem recordedTarget_eq_generated :
    updateReadout.recordedTargetPositions =
      generatedTarget updateReadout.sourcePositions updateReadout.gradient := by
  unfold generatedTarget generatedDisplacement
  rw [normalizer_exact]
  funext atom axis
  fin_cases atom <;> fin_cases axis <;> decide

theorem generatedStep_budget :
    ∀ atom, rowSquaredNorm (generatedDisplacement updateReadout.gradient) atom ≤
      stepBudgetPicobohr ^ 2 := by
  unfold generatedDisplacement
  rw [normalizer_exact]
  intro atom
  fin_cases atom <;> decide

theorem generatedStep_direction :
    ∀ atom axis, updateReadout.gradient atom axis *
      generatedDisplacement updateReadout.gradient atom axis ≤ 0 := by
  unfold generatedDisplacement
  rw [normalizer_exact]
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> decide

def gradientComponentSum (atom : Atom) (axis : Axis) : Int :=
  (updateReadout.gradientComponents.toList.map fun rows => (rows[atom.val]!)[axis.val]!).sum

theorem gradientWholeLedger : ∀ atom axis,
    gradientComponentSum atom axis + updateReadout.gradientRoundingResidual atom axis =
      updateReadout.gradient atom axis := by
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> decide

theorem sameNuclearInventory : updateReadout.sourceNuclei = updateReadout.targetNuclei := by
  decide

theorem actualEnergyDecreased :
    updateReadout.targetEnergyNanohartree < updateReadout.currentEnergyNanohartree ∧
    updateReadout.targetEnergyNanohartree - updateReadout.currentEnergyNanohartree = -5803054 := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem targetEnergyRows_exact : updateReadout.targetEnergyLedger.rowToIntegralExact := by
  intro component
  cases component <;> decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem targetWholeEnergyClosure :
    updateReadout.targetEnergyLedger.grandRowSum + updateReadout.targetEnergyLedger.rowResidualSum +
      updateReadout.targetEnergyLedger.componentRoundingResidual +
      updateReadout.targetEnergyLedger.scfRecomputationResidual =
        updateReadout.targetEnergyNanohartree := by
  decide

def recordedCoordinates : Configuration → NuclearCoordinates
  | .current => updateReadout.sourcePositions
  | .generatedNext => updateReadout.recordedTargetPositions

def energyRead : Configuration → Int
  | .current => updateReadout.currentEnergyNanohartree
  | .generatedNext => updateReadout.targetEnergyNanohartree

def heavyGraphRead : Configuration → Array (List String × Nat)
  | .current => updateReadout.currentHeavyGraph
  | .generatedNext => updateReadout.targetHeavyGraph

def nuclearInventoryRead : Configuration → Array (String × Nat)
  | .current => updateReadout.sourceNuclei
  | .generatedNext => updateReadout.targetNuclei

def electronicLedgerRead : Configuration → Energy.Interface.MolecularEnergyLedger
  | .current => LAlanine40K2025.Energy.Source.energyLedger
  | .generatedNext => updateReadout.targetEnergyLedger

inductive MolecularConsumer where
  | recordedCoordinates | energy | registeredHeavyGraph | nuclearInventory | electronicLedger
  deriving DecidableEq, Repr

def registeredConsumers : IndependentConsumerSystem Configuration where
  Consumer := MolecularConsumer
  Output
    | .recordedCoordinates => NuclearCoordinates
    | .energy => Int
    | .registeredHeavyGraph => Array (List String × Nat)
    | .nuclearInventory => Array (String × Nat)
    | .electronicLedger => Energy.Interface.MolecularEnergyLedger
  read
    | .recordedCoordinates => recordedCoordinates
    | .energy => energyRead
    | .registeredHeavyGraph => heavyGraphRead
    | .nuclearInventory => nuclearInventoryRead
    | .electronicLedger => electronicLedgerRead
  positive := ⟨.energy⟩

/-- This face computes the next, rather than accepting its recorded value. -/
def nativeFaceRead : Configuration → NuclearCoordinates
  | .current => updateReadout.sourcePositions
  | .generatedNext => generatedTarget updateReadout.sourcePositions updateReadout.gradient

theorem nativeFace_commutes (configuration : Configuration) :
    nativeFaceRead configuration = recordedCoordinates configuration := by
  cases configuration with
  | current => rfl
  | generatedNext => exact recordedTarget_eq_generated.symm

theorem nativeFace_separates : Function.Injective nativeFaceRead := by
  have different : nativeFaceRead .current ≠ nativeFaceRead .generatedNext := by
    intro same
    rw [nativeFace_commutes .current, nativeFace_commutes .generatedNext] at same
    have coordinate := congrArg (fun value : NuclearCoordinates => value 0 0) same
    exact (by decide : recordedCoordinates .current 0 0 ≠
      recordedCoordinates .generatedNext 0 0) coordinate
  intro left right same
  cases left <;> cases right
  · rfl
  · exact False.elim (different same)
  · exact False.elim (different same.symm)
  · rfl

theorem consumerEnergy_separates {left right : Configuration}
    (same : registeredConsumers.Indistinguishable left right) : left = right := by
  have energy := same .energy
  have different : energyRead .current ≠ energyRead .generatedNext := by decide
  cases left <;> cases right
  · rfl
  · exact False.elim (different energy)
  · exact False.elim (different energy.symm)
  · rfl

theorem nativeFaceKernelExact : FaceKernelExactAt registeredConsumers nativeFaceRead := by
  intro left right
  constructor
  · intro same
    have equal := nativeFace_separates same
    subst right
    exact registeredConsumers.indistinguishable_refl left
  · intro same
    exact congrArg nativeFaceRead (consumerEnergy_separates same)

def nativeQuotientEquivRange : registeredConsumers.Quotient ≃ Set.range nativeFaceRead :=
  nativeFaceKernelExact.quotientEquivRange

theorem everyConsumer_uniqueFactorization (consumer : MolecularConsumer) :
    ∃! factor : Set.range nativeFaceRead → registeredConsumers.Output consumer,
      ∀ configuration, factor ⟨nativeFaceRead configuration, configuration, rfl⟩ =
        registeredConsumers.read consumer configuration :=
  nativeFaceKernelExact.everyConsumer_unique_factorization consumer

theorem sameRootCompleteCarrier_uniqueIso {Alternate : Type}
    (alternate : Configuration → Alternate)
    (alternateExact : FaceKernelExactAt registeredConsumers alternate) :
    ∃! equivalence : Set.range nativeFaceRead ≃ Set.range alternate,
      ∀ configuration, equivalence ⟨nativeFaceRead configuration, configuration, rfl⟩ =
        ⟨alternate configuration, configuration, rfl⟩ :=
  ⟨nativeFaceKernelExact.completeCarrierEquiv alternateExact,
    nativeFaceKernelExact.completeCarrierEquiv_commutes alternateExact,
    fun candidate commutes => nativeFaceKernelExact.completeCarrierEquiv_unique
      alternateExact candidate commutes⟩

def independentEnergy : IndependentReadout Configuration := ⟨Int, energyRead⟩

theorem energyEscapesRegisteredHeavyGraph :
    FaceKernelEscapeAt heavyGraphRead independentEnergy := by
  refine ⟨.current, .generatedNext, ?_, ?_⟩
  · decide
  · change energyRead .current ≠ energyRead .generatedNext
    decide

theorem heavyGraphCannotMintEnergy : ¬ Function.FactorsThrough energyRead heavyGraphRead :=
  energyEscapesRegisteredHeavyGraph.not_factorsThrough

structure SourceGeneratedLAlanineForceUpdateCrown : Prop where
  nativeTarget : updateReadout.recordedTargetPositions =
    generatedTarget updateReadout.sourcePositions updateReadout.gradient
  forceLedger : type_of% gradientWholeLedger
  stepBudget : type_of% generatedStep_budget
  stepDirection : type_of% generatedStep_direction
  inventory : updateReadout.sourceNuclei = updateReadout.targetNuclei
  actualDescent : type_of% actualEnergyDecreased
  completeTargetRows : updateReadout.targetEnergyLedger.rowToIntegralExact
  completeTargetEnergy : type_of% targetWholeEnergyClosure
  sourceFaceCommutes : ∀ configuration, nativeFaceRead configuration = recordedCoordinates configuration
  exactKernel : FaceKernelExactAt registeredConsumers nativeFaceRead
  quotientRange : Nonempty (registeredConsumers.Quotient ≃ Set.range nativeFaceRead)
  graphEscape : ¬ Function.FactorsThrough energyRead heavyGraphRead
  uniqueConsumers : ∀ consumer : MolecularConsumer,
    ∃! factor : Set.range nativeFaceRead → registeredConsumers.Output consumer,
      ∀ configuration, factor ⟨nativeFaceRead configuration, configuration, rfl⟩ =
        registeredConsumers.read consumer configuration

theorem sourceGeneratedLAlanineForceUpdate_crown : SourceGeneratedLAlanineForceUpdateCrown where
  nativeTarget := recordedTarget_eq_generated
  forceLedger := gradientWholeLedger
  stepBudget := generatedStep_budget
  stepDirection := generatedStep_direction
  inventory := sameNuclearInventory
  actualDescent := actualEnergyDecreased
  completeTargetRows := targetEnergyRows_exact
  completeTargetEnergy := targetWholeEnergyClosure
  sourceFaceCommutes := nativeFace_commutes
  exactKernel := nativeFaceKernelExact
  quotientRange := ⟨nativeQuotientEquivRange⟩
  graphEscape := heavyGraphCannotMintEnergy
  uniqueConsumers := everyConsumer_uniqueFactorization

end

end LAlanine40K2025.Force.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
