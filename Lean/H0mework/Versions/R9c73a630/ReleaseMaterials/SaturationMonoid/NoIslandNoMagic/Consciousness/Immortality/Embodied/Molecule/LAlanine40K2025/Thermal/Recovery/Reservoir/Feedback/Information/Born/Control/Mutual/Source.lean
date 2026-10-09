import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.Control.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.Control.Information
import H0mework.Chemistry.LAlanineEntropy.ClassicalJointEntropy
import H0mework.Probability.Source.Conditional
import Mathlib.Data.Set.Finite.Range

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedWorkInformation

open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedConditionalWork Collision
open scoped ENNReal

noncomputable section
open scoped Classical

private theorem support_sum {A : Type*} [Fintype A] (source : PMF A) (read : A → ℝ) :
    ∑ atom : source.support, (source atom).toReal * read atom =
      ∑ atom : A, (source atom).toReal * read atom := by
  have split := Fintype.sum_subtype_add_sum_subtype (fun atom => atom ∈ source.support)
    (fun atom => (source atom).toReal * read atom)
  have vanished : (∑ atom : {atom : A // atom ∉ source.support},
      (source atom).toReal * read atom) = 0 := by
    apply Finset.sum_eq_zero
    intro atom _
    have zero : source atom = 0 := Classical.not_not.mp atom.property
    rw [zero, ENNReal.toReal_zero, zero_mul]
  rw [vanished, add_zero] at split
  exact split

private theorem conditional_mean {A V : Type*} [Fintype A]
    (source : PMF A) (read : A → V) (value : V) (supported : value ∈ (source.map read).support)
    (task : A → ℝ) :
    (source.map read value).toReal *
        (∑ atom : A, (SourceConditionalHistory.conditional source read value supported atom).toReal * task atom) =
      ∑ atom : A, (source atom).toReal * (if read atom = value then task atom else 0) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro atom _
  have original := congrArg ENNReal.toReal
    (SourceConditionalHistory.weighted_conditional source read value supported atom)
  rw [ENNReal.toReal_mul] at original
  by_cases same : read atom = value
  · rw [if_pos same] at original ⊢
    exact (mul_assoc _ _ _).symm.trans (congrArg (· * task atom) original)
  · rw [if_neg same, ENNReal.toReal_zero] at original
    rw [if_neg same, mul_zero, ← mul_assoc, original, zero_mul]

private theorem conditional_sum {A V : Type*} [Fintype A] [Fintype V]
    (source : PMF A) (read : A → V) (task : V → A → ℝ) :
    (∑ value : (source.map read).support, (source.map read value).toReal *
      ∑ atom : A, (SourceConditionalHistory.conditional source read value value.property atom).toReal *
        task value atom) =
      ∑ atom : A, (source atom).toReal * task (read atom) atom := by
  calc
    _ = ∑ value : (source.map read).support,
        ∑ atom : A, (source atom).toReal * (if read atom = value.val then task value atom else 0) := by
      apply Finset.sum_congr rfl
      intro value _
      exact conditional_mean source read value value.property (task value)
    _ = ∑ atom : A, ∑ value : (source.map read).support,
        (source atom).toReal * (if read atom = value.val then task value atom else 0) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro atom _
      by_cases zero : source atom = 0
      · simp only [zero, ENNReal.toReal_zero, zero_mul, Finset.sum_const_zero]
      · let value : (source.map read).support :=
          ⟨read atom, (PMF.mem_support_map_iff read source (read atom)).mpr ⟨atom, zero, rfl⟩⟩
        rw [Finset.sum_eq_single value]
        · simp only [value, ite_true]
        · intro other _ different
          have unequal : read atom ≠ other.val := by
            intro same
            exact different (Subtype.ext same.symm)
          rw [if_neg unequal, mul_zero]
        · exact fun absent => (absent (Finset.mem_univ value)).elim

private theorem probability_mean {A : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (source : PMF A) (read : A → Fin 2) (value : ℝ) :
    ∑ atom : A, (source atom).toReal * (if read atom = 0 then value else 0) =
      (source.map read 0).toReal * value := by
  have original := Quantum.sum_map_read source read (fun branch => if branch = 0 then value else 0)
  simpa only [Fin.sum_univ_two, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false,
    mul_zero, add_zero] using original.symm

private theorem event_probability {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B] [MeasurableSingletonClass B]
    (source : PMF A) (read : A → B) (value : B) :
    (source.map read value).toReal =
      ∑ atom : A, (source atom).toReal * (if read atom = value then 1 else 0) := by
  have original := Quantum.sum_map_read source read (fun other => if other = value then 1 else 0)
  simpa [mul_ite] using original

private theorem joint_cell {A V : Type*} [Fintype A] [Fintype V]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace V] [MeasurableSingletonClass V]
    (source : PMF A) (pointer : A → Fin 2) (read : A → V) (value : V)
    (supported : value ∈ (source.map read).support) (branch : Fin 2) :
    (source.map (fun atom => (pointer atom, read atom)) (branch, value)).toReal =
      (source.map read value).toReal *
        ((SourceConditionalHistory.conditional source read value supported).map pointer branch).toReal := by
  have conditional := conditional_mean source read value supported
    (fun atom => if pointer atom = branch then 1 else 0)
  have collapsed := (congrArg ((source.map read value).toReal * ·)
    (event_probability (SourceConditionalHistory.conditional source read value supported) pointer branch)).trans conditional
  apply (event_probability source (fun atom => (pointer atom, read atom)) (branch, value)).trans
  apply Eq.trans ?_ collapsed.symm
  apply Finset.sum_congr rfl
  intro atom _
  by_cases first : pointer atom = branch <;> by_cases second : read atom = value <;> simp [first, second]

private theorem real_loss {A B : Type*} [Fintype A]
    (source : PMF A) (observer : A → B) (task : A → ℝ) (center : ℝ) :
    SourceWeightedRecovery.error source observer (fun atom => (task atom : ℂ)) (fun _ => (center : ℂ)) =
      ∑ atom : A, (source atom).toReal * (task atom - center) ^ 2 := by
  simp only [SourceWeightedRecovery.error, Complex.sq_norm, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_self,
    ← pow_two, zero_pow (by decide : 2 ≠ 0), add_zero]

private theorem centered_sum {A : Type*} [Fintype A] (weight probability value : A → ℝ) (p center : ℝ) :
    (∑ atom : A, weight atom * (probability atom - p) * (value atom - center)) =
      (∑ atom : A, weight atom * probability atom * value atom) -
        center * (∑ atom : A, weight atom * probability atom) -
        p * (∑ atom : A, weight atom * value atom) + p * center * (∑ atom : A, weight atom) := by
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro atom _
  ring

def sourcePMF : PMF PointerIndex := Born.distribution contrast contrast_hermitian receivedState
abbrev Value := Set.range (Born.outcome contrast contrast_hermitian)
local instance : MeasurableSpace PointerIndex := ⊤
local instance : MeasurableSingletonClass PointerIndex := ⟨fun _ => trivial⟩
local instance : MeasurableSpace Value := ⊤
local instance : MeasurableSingletonClass Value := ⟨fun _ => trivial⟩

def valueRead (atom : PointerIndex) : Value := ⟨Born.outcome contrast contrast_hermitian atom, ⟨atom, rfl⟩⟩
def valuePMF : PMF Value := sourcePMF.map valueRead
def joint : PMF (Fin 2 × Value) := sourcePMF.map (fun atom => (Born.pointer atom, valueRead atom))
def pointerPMF : PMF (Fin 2) := sourcePMF.map Born.pointer
abbrev SupportedValue := valuePMF.support
def weight (value : SupportedValue) : ℝ := (valuePMF value).toReal
def posterior (value : SupportedValue) : PMF PointerIndex :=
  SourceConditionalHistory.conditional sourcePMF valueRead value value.property
def conditionalProbability (value : SupportedValue) : ℝ := ((posterior value).map Born.pointer 0).toReal
def sourceMean : ℝ := energy contrast (bodyRead receivedState.joint)
def sourceVariance : ℝ := Born.loss contrast contrast_hermitian receivedState
  (fun _ => Information.mean contrast receivedState)
def sourceMutualInformation : ℝ :=
  Population.realKL joint (Quantum.productPMF (Quantum.fstMarginal joint) (Quantum.sndMarginal joint))

theorem joint_first : Quantum.fstMarginal joint = pointerPMF := by
  rw [Quantum.fstMarginal, joint, PMF.map_comp]
  rfl

theorem joint_second : Quantum.sndMarginal joint = valuePMF := by
  rw [Quantum.sndMarginal, joint, PMF.map_comp]
  rfl

theorem source_information_finite :
    InformationTheory.klDiv joint.toMeasure
      (Quantum.productPMF (Quantum.fstMarginal joint) (Quantum.sndMarginal joint)).toMeasure ≠ ∞ :=
  Quantum.joint_product_KL_finite joint

theorem source_information_entropy : sourceMutualInformation =
    Population.entropy pointerPMF + Population.entropy valuePMF - Population.entropy joint :=
  (Quantum.jointKL_entropy_commutes joint).trans
    (congrArg₂ (fun left right => Population.entropy left + Population.entropy right - Population.entropy joint)
      joint_first joint_second)

theorem posterior_support (value : SupportedValue) :
    (posterior value).support = {atom | valueRead atom = value.val} ∩ sourcePMF.support :=
  SourceConditionalHistory.conditional_support sourcePMF valueRead value value.property

theorem weight_positive (value : SupportedValue) : 0 < weight value :=
  ENNReal.toReal_pos value.property (valuePMF.apply_ne_top value)

theorem conditional_range (value : SupportedValue) :
    0 ≤ conditionalProbability value ∧ conditionalProbability value ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal (by norm_num)
    (by simpa only [ENNReal.ofReal_one] using ((posterior value).map Born.pointer).coe_le_one 0)⟩

theorem joint_probability (branch : Fin 2) (value : SupportedValue) :
    (joint (branch, value.val)).toReal = weight value * ((posterior value).map Born.pointer branch).toReal :=
  joint_cell sourcePMF Born.pointer valueRead value value.property branch

theorem conditional_complement (value : SupportedValue) :
    ((posterior value).map Born.pointer 1).toReal = 1 - conditionalProbability value := by
  have total := Population.pmf_sum_toReal ((posterior value).map Born.pointer)
  rw [Fin.sum_univ_two] at total
  change conditionalProbability value + _ = 1 at total
  linarith

theorem pointer_zero_probability : (pointerPMF 0).toReal = zeroRead receivedState.joint :=
  Born.pointer_zero_read contrast contrast_hermitian receivedState

theorem pointer_one_probability : (pointerPMF 1).toReal = 1 - zeroRead receivedState.joint := by
  rw [show (pointerPMF 1).toReal = oneRead receivedState.joint from
    Born.pointer_one_read contrast contrast_hermitian receivedState]
  linarith [SourceGeneratedConditionalWork.weights_sum receivedState]

theorem value_expectation (read : Value → ℝ) :
    ∑ value : SupportedValue, weight value * read value =
      ∑ atom : PointerIndex, (sourcePMF atom).toReal * read (valueRead atom) :=
  (support_sum valuePMF read).trans (Quantum.sum_map_read sourcePMF valueRead read)

theorem weights_sum : ∑ value : SupportedValue, weight value = 1 := by
  have original := value_expectation (fun _ => 1)
  simpa only [mul_one, Population.pmf_sum_toReal] using original

theorem conditional_expectation (read : Value → ℝ) :
    ∑ value : SupportedValue, weight value * conditionalProbability value * read value =
      ∑ atom : PointerIndex, (sourcePMF atom).toReal *
        (if Born.pointer atom = 0 then read (valueRead atom) else 0) := by
  have original := conditional_sum sourcePMF valueRead
    (fun value atom => if Born.pointer atom = 0 then read value else 0)
  have reduced : (∑ value : SupportedValue, weight value * conditionalProbability value * read value) =
      ∑ value : SupportedValue, weight value *
        ∑ atom : PointerIndex, (posterior value atom).toReal *
          (if Born.pointer atom = 0 then read value else 0) := by
    apply Finset.sum_congr rfl
    intro value _
    rw [probability_mean]
    exact mul_assoc _ _ _
  exact reduced.trans original

theorem conditional_probability_mean :
    ∑ value : SupportedValue, weight value * conditionalProbability value = zeroRead receivedState.joint := by
  have original := conditional_expectation (fun _ => 1)
  simp only [mul_one] at original
  exact original.trans ((probability_mean sourcePMF Born.pointer 1).trans
    ((mul_one _).trans (Born.pointer_zero_read contrast contrast_hermitian receivedState)))

theorem value_mean :
    ∑ value : SupportedValue, weight value * value.val.val = sourceMean :=
  (value_expectation (fun value => value.val)).trans
    (Born.first_moment contrast contrast_hermitian receivedState)

theorem conditional_value_mean :
    ∑ value : SupportedValue, weight value * conditionalProbability value * value.val.val =
      energy contrast receivedState.joint.toBlocks₁₁ := by
  have original := Born.decoder_weighted contrast contrast_hermitian receivedState 0
  rw [Born.pointer_zero_read] at original
  exact (conditional_expectation (fun value => value.val)).trans
    (original.symm.trans (Born.zero_weighted_mean contrast contrast_hermitian receivedState))

theorem covariance_formula :
    signedDefect receivedState =
      ∑ value : SupportedValue, weight value * (conditionalProbability value - zeroRead receivedState.joint) *
        (value.val.val - sourceMean) := by
  rw [centered_sum, conditional_value_mean, conditional_probability_mean, value_mean, weights_sum]
  have total := SourceGeneratedConditionalWork.weights_sum receivedState
  have meanSource : sourceMean =
      energy contrast receivedState.joint.toBlocks₁₁ + energy contrast receivedState.joint.toBlocks₂₂ :=
    Load.Producer.HeatProbability.energy_add_right contrast _ _
  rw [signed_defect_blocks]
  rw [meanSource]
  have other : oneRead receivedState.joint = 1 - zeroRead receivedState.joint := by linarith
  rw [other]
  ring

theorem variance_formula :
    sourceVariance = ∑ value : SupportedValue, weight value * (value.val.val - sourceMean) ^ 2 :=
  (real_loss sourcePMF Born.pointer (Born.outcome contrast contrast_hermitian) sourceMean).trans
    (value_expectation (fun value => (value.val - sourceMean) ^ 2)).symm

private theorem joint_empty (branch : Fin 2) (value : Value) (absent : value ∉ valuePMF.support) :
    joint (branch, value) = 0 := by
  by_contra present
  have supported := (PMF.mem_support_map_iff Prod.snd joint value).mpr ⟨(branch, value), present, rfl⟩
  rw [show joint.map Prod.snd = valuePMF from joint_second] at supported
  exact absent supported

private theorem conditional_KL_term (value : SupportedValue) (branch : Fin 2) :
    (joint (branch, value.val)).toReal *
        Real.log ((joint (branch, value.val)).toReal / ((pointerPMF branch).toReal * weight value)) =
      weight value * (((posterior value).map Born.pointer) branch).toReal *
        Real.log ((((posterior value).map Born.pointer) branch).toReal / (pointerPMF branch).toReal) := by
  rw [joint_probability]
  have cancel (w a p : ℝ) (nonzero : w ≠ 0) : w * a / (p * w) = a / p := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    calc
      w * a * (w⁻¹ * p⁻¹) = (w * w⁻¹) * (a * p⁻¹) := by ring
      _ = a * p⁻¹ := by rw [mul_inv_cancel₀ nonzero, one_mul]
  rw [cancel _ _ _ (weight_positive value).ne']

theorem information_conditional : sourceMutualInformation =
    ∑ value : SupportedValue, weight value *
      (conditionalProbability value * Real.log (conditionalProbability value / zeroRead receivedState.joint) +
        (1 - conditionalProbability value) *
          Real.log ((1 - conditionalProbability value) / (1 - zeroRead receivedState.joint))) := by
  let term (value : Value) :=
    (joint (0, value)).toReal * Real.log ((joint (0, value)).toReal / ((pointerPMF 0).toReal * (valuePMF value).toReal)) +
      (joint (1, value)).toReal * Real.log ((joint (1, value)).toReal / ((pointerPMF 1).toReal * (valuePMF value).toReal))
  have original := Population.realKL_eq_sum_of_ac joint
    (Quantum.productPMF (Quantum.fstMarginal joint) (Quantum.sndMarginal joint))
    (Quantum.joint_product_absolutelyContinuous joint)
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Quantum.productPMF_apply, ENNReal.toReal_mul,
    joint_first, joint_second] at original
  have sourceRead : sourceMutualInformation = Population.realKL joint (Quantum.productPMF pointerPMF valuePMF) := by
    unfold sourceMutualInformation
    rw [joint_first, joint_second]
  have full : sourceMutualInformation = ∑ value : Value, term value :=
    sourceRead.trans (original.trans (Finset.sum_add_distrib).symm)
  have supported : (∑ value : SupportedValue, term value) = ∑ value : Value, term value := by
    have split := Fintype.sum_subtype_add_sum_subtype (fun value => value ∈ valuePMF.support) term
    have zero : (∑ value : {value : Value // value ∉ valuePMF.support}, term value) = 0 := by
      apply Finset.sum_eq_zero
      intro value _
      dsimp only [term]
      rw [joint_empty 0 value value.property, joint_empty 1 value value.property]
      simp only [ENNReal.toReal_zero, zero_mul, add_zero]
    rw [zero, add_zero] at split
    exact split
  apply (full.trans supported.symm).trans
  apply Finset.sum_congr rfl
  intro value _
  change (joint (0, value.val)).toReal *
      Real.log ((joint (0, value.val)).toReal / ((pointerPMF 0).toReal * weight value)) +
    (joint (1, value.val)).toReal *
      Real.log ((joint (1, value.val)).toReal / ((pointerPMF 1).toReal * weight value)) = _
  rw [conditional_KL_term, conditional_KL_term, conditional_complement,
    pointer_zero_probability, pointer_one_probability]
  change weight value * conditionalProbability value * Real.log (conditionalProbability value / zeroRead receivedState.joint) + _ = _
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedWorkInformation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
