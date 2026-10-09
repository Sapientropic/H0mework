import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BodyEnsemble.Measurement
import H0mework.Chemistry.LAlanineEntropy.ClassicalJointEntropy
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble.ValueCoarsening

open MeasureTheory ProbabilityTheory InformationTheory SourceGeneratedWorkInformation
open scoped ENNReal
noncomputable section

local instance : MeasurableSpace PointerIndex := ⊤
local instance : MeasurableSingletonClass PointerIndex := ⟨fun _ => trivial⟩
local instance : MeasurableSpace Value := ⊤
local instance : MeasurableSingletonClass Value := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Fin 2) := ⊤
local instance : MeasurableSingletonClass (Fin 2) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace Current.FullIndex := ⊤
local instance : MeasurableSingletonClass Current.FullIndex := ⟨fun _ => trivial⟩

def branchIndex : PointerIndex → Fin 2 × Current.FullIndex
  | .inl index => (0, index)
  | .inr index => (1, index)

def indexedJoint : PMF (Fin 2 × Current.FullIndex) := sourcePMF.map branchIndex

def indexValue (index : Current.FullIndex) : Value := valueRead (Sum.inl index)

def toValue : Fin 2 × Current.FullIndex → Fin 2 × Value :=
  fun sample => (sample.1, indexValue sample.2)

theorem original_joint_coarsens_index : joint = indexedJoint.map toValue := by
  rw [indexedJoint, joint, PMF.map_comp]
  congr 1
  funext atom
  cases atom with
  | inl index => rfl
  | inr index =>
    apply Prod.ext
    · rfl
    · exact Subtype.ext rfl

private theorem product_map_second {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (p : PMF A) (q : PMF B) (f : B → C) :
    (Quantum.productPMF p q).map (fun sample => (sample.1, f sample.2)) =
      Quantum.productPMF p (q.map f) := by
  unfold Quantum.productPMF
  rw [PMF.map_bind]
  congr 1
  funext i
  rw [PMF.map_comp, PMF.map_comp]
  rfl

theorem indexed_pointer : Quantum.fstMarginal indexedJoint = pointerPMF := by
  unfold Quantum.fstMarginal indexedJoint pointerPMF
  rw [PMF.map_comp]
  congr 1
  funext atom
  cases atom <;> rfl

theorem indexed_value :
    (Quantum.sndMarginal indexedJoint).map indexValue = valuePMF := by
  unfold Quantum.sndMarginal indexedJoint valuePMF
  rw [PMF.map_comp, PMF.map_comp]
  congr 1
  funext atom
  cases atom with
  | inl index => rfl
  | inr index => exact Subtype.ext rfl

theorem product_value :
    (Quantum.productPMF (Quantum.fstMarginal indexedJoint)
      (Quantum.sndMarginal indexedJoint)).map toValue =
      Quantum.productPMF pointerPMF valuePMF := by
  rw [show toValue = (fun sample => (sample.1, indexValue sample.2)) from rfl,
    product_map_second, indexed_pointer, indexed_value]

def indexedInformation : ℝ :=
  Population.realKL indexedJoint (Quantum.productPMF
    (Quantum.fstMarginal indexedJoint) (Quantum.sndMarginal indexedJoint))

theorem value_information_le_index : sourceMutualInformation ≤ indexedInformation := by
  let reference := Quantum.productPMF
    (Quantum.fstMarginal indexedJoint) (Quantum.sndMarginal indexedJoint)
  have mapped := InformationTheory.klDiv_map_le indexedJoint.toMeasure reference.toMeasure
    (measurable_of_countable toValue)
  rw [PMF.toMeasure_map toValue indexedJoint (measurable_of_countable toValue),
    PMF.toMeasure_map toValue reference (measurable_of_countable toValue),
    ← original_joint_coarsens_index, product_value] at mapped
  have finite : klDiv indexedJoint.toMeasure reference.toMeasure ≠ ∞ :=
    Quantum.joint_product_KL_finite indexedJoint
  have realBound := ENNReal.toReal_mono finite mapped
  unfold sourceMutualInformation indexedInformation
  rw [joint_first, joint_second]
  exact realBound

def valueInformationLoss : ℝ := indexedInformation - sourceMutualInformation

theorem valueInformationLoss_nonnegative : 0 ≤ valueInformationLoss :=
  sub_nonneg.mpr value_information_le_index

theorem indexedInformation_eq_value_add_loss :
    indexedInformation = sourceMutualInformation + valueInformationLoss := by
  unfold valueInformationLoss
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble.ValueCoarsening
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
