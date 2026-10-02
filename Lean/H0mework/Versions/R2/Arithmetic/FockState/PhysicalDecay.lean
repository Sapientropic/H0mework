import Mathlib.Data.Sym.Sym2
import H0mework.Versions.R2.Arithmetic.FockState.FactorDecay
import H0mework.Versions.R2.Arithmetic.FockState.IndistinguishablePairs

/-!
# Physical factor-decay kernel on indistinguishable pairs

This is the dependency-low physical layer shared by the atomic source and its
debt consumer.  Ordered arithmetic splits are projected to the exchange
coinvariants, and every existing repair/emission channel receives its exact
target-minus-source action there.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFock

open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticOperationalFactorDecayProducer
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedIntegralIndistinguishableParticlePair

noncomputable section

/-! ## Physical pure-split carrier -/

/-- A generated positive split read in the physical parent carrier. -/
def physicalSplitParticleState {index : Nat}
    (state : EffectiveSplitAt index) : PhysicalParentCarrier :=
  physicalParentProjection (splitParticleState state)

@[simp] theorem physicalSplitParticleState_eq_pairState {index : Nat}
    (state : EffectiveSplitAt index) :
    physicalSplitParticleState state =
      physicalPairState (delta (splitLeftUnit state))
        (delta (splitRightUnit state)) :=
  rfl

private theorem splitLeftUnit_eq_splitRightUnit_of_eq
    {index : Nat} {left right : EffectiveSplitAt index}
    (equality : splitLeft left = splitRight right) :
    splitLeftUnit left = splitRightUnit right := by
  apply Units.ext
  apply NNReal.eq
  rw [splitLeftUnit_value, splitRightUnit_value]
  exact_mod_cast equality

private theorem splitRightUnit_eq_splitLeftUnit_of_eq
    {index : Nat} {left right : EffectiveSplitAt index}
    (equality : splitRight left = splitLeft right) :
    splitRightUnit left = splitLeftUnit right := by
  apply Units.ext
  apply NNReal.eq
  rw [splitRightUnit_value, splitLeftUnit_value]
  exact_mod_cast equality

private theorem splitLeftUnit_eq_splitLeftUnit_of_eq
    {index : Nat} {left right : EffectiveSplitAt index}
    (equality : splitLeft left = splitLeft right) :
    splitLeftUnit left = splitLeftUnit right := by
  apply Units.ext
  apply NNReal.eq
  rw [splitLeftUnit_value, splitLeftUnit_value]
  exact_mod_cast equality

private theorem splitRightUnit_eq_splitRightUnit_of_eq
    {index : Nat} {left right : EffectiveSplitAt index}
    (equality : splitRight left = splitRight right) :
    splitRightUnit left = splitRightUnit right := by
  apply Units.ext
  apply NNReal.eq
  rw [splitRightUnit_value, splitRightUnit_value]
  exact_mod_cast equality

private theorem splitLeft_eq_splitLeft_of_unit_eq
    {index : Nat} {left right : EffectiveSplitAt index}
    (equality : splitLeftUnit left = splitLeftUnit right) :
    splitLeft left = splitLeft right := by
  have valueEq := congrArg
    (fun unit : Units NNReal => (((unit : NNReal) : ℝ))) equality
  rw [splitLeftUnit_value, splitLeftUnit_value] at valueEq
  exact_mod_cast valueEq

private theorem splitRight_eq_splitRight_of_unit_eq
    {index : Nat} {left right : EffectiveSplitAt index}
    (equality : splitRightUnit left = splitRightUnit right) :
    splitRight left = splitRight right := by
  have valueEq := congrArg
    (fun unit : Units NNReal => (((unit : NNReal) : ℝ))) equality
  rw [splitRightUnit_value, splitRightUnit_value] at valueEq
  exact_mod_cast valueEq

private theorem splitLeft_eq_splitRight_of_unit_eq
    {index : Nat} {left right : EffectiveSplitAt index}
    (equality : splitLeftUnit left = splitRightUnit right) :
    splitLeft left = splitRight right := by
  have valueEq := congrArg
    (fun unit : Units NNReal => (((unit : NNReal) : ℝ))) equality
  rw [splitLeftUnit_value, splitRightUnit_value] at valueEq
  exact_mod_cast valueEq

private theorem splitRight_eq_splitLeft_of_unit_eq
    {index : Nat} {left right : EffectiveSplitAt index}
    (equality : splitRightUnit left = splitLeftUnit right) :
    splitRight left = splitLeft right := by
  have valueEq := congrArg
    (fun unit : Units NNReal => (((unit : NNReal) : ℝ))) equality
  rw [splitRightUnit_value, splitLeftUnit_value] at valueEq
  exact_mod_cast valueEq

/-- Swapping the two arithmetic endpoint labels is physical identity. -/
theorem physicalSplitParticleState_eq_of_swap
    {index : Nat} (left right : EffectiveSplitAt index)
    (left_eq : splitLeft left = splitRight right)
    (right_eq : splitRight left = splitLeft right) :
    physicalSplitParticleState left = physicalSplitParticleState right := by
  rw [physicalSplitParticleState_eq_pairState,
    physicalSplitParticleState_eq_pairState,
    splitLeftUnit_eq_splitRightUnit_of_eq left_eq,
    splitRightUnit_eq_splitLeftUnit_of_eq right_eq]
  exact physicalPairState_swap _ _

/-! ## Faithful unordered occupation detector -/

abbrev UnorderedParticleIdentityCarrier :=
  Sym2 (Units NNReal) →₀ ℤ

def unorderedParticleBasis (left right : Units NNReal) :
    UnorderedParticleIdentityCarrier :=
  Finsupp.single s(left, right) 1

@[simp] theorem unorderedParticleBasis_swap (left right : Units NNReal) :
    unorderedParticleBasis left right = unorderedParticleBasis right left := by
  rw [unorderedParticleBasis, unorderedParticleBasis, Sym2.eq_swap]

def unorderedParticleBilinear :
    IntegralOneParticle →ₗ[ℤ] IntegralOneParticle →ₗ[ℤ]
      UnorderedParticleIdentityCarrier :=
  canonicalBasis.constr ℤ fun left =>
    canonicalBasis.constr ℤ (unorderedParticleBasis left)

def unorderedPairMeasurement :
    OrderedParticleTwo →ₗ[ℤ] UnorderedParticleIdentityCarrier :=
  TensorProduct.lift unorderedParticleBilinear

@[simp] theorem unorderedPairMeasurement_delta_pair
    (left right : Units NNReal) :
    unorderedPairMeasurement (delta left ⊗ₜ[ℤ] delta right) =
      unorderedParticleBasis left right := by
  change unorderedParticleBilinear (delta left) (delta right) = _
  unfold unorderedParticleBilinear
  change (canonicalBasis.constr ℤ fun left =>
      canonicalBasis.constr ℤ (unorderedParticleBasis left))
    (canonicalBasis left) (canonicalBasis right) = _
  rw [canonicalBasis.constr_basis, canonicalBasis.constr_basis]

theorem unorderedParticleBilinear_flip :
    unorderedParticleBilinear.flip = unorderedParticleBilinear := by
  apply canonicalBasis.ext
  intro left
  apply canonicalBasis.ext
  intro right
  rw [LinearMap.flip_apply]
  simp only [unorderedParticleBilinear, canonicalBasis.constr_basis]
  exact unorderedParticleBasis_swap right left

theorem unorderedPairMeasurement_swap (particles : OrderedParticleTwo) :
    unorderedPairMeasurement (swap IntegralOneParticle particles) =
      unorderedPairMeasurement particles := by
  have mapEquality :
      unorderedPairMeasurement.comp (swap IntegralOneParticle) =
        unorderedPairMeasurement := by
    apply TensorProduct.ext'
    intro left right
    change unorderedParticleBilinear right left =
      unorderedParticleBilinear left right
    have outer := LinearMap.congr_fun unorderedParticleBilinear_flip right
    have inner := LinearMap.congr_fun outer left
    exact inner.symm
  exact LinearMap.congr_fun mapEquality particles

def physicalUnorderedPairMeasurement :
    PhysicalParticleTwo →ₗ[ℤ] UnorderedParticleIdentityCarrier :=
  descend unorderedPairMeasurement unorderedPairMeasurement_swap

@[simp] theorem physicalUnorderedPairMeasurement_projection
    (particles : OrderedParticleTwo) :
    physicalUnorderedPairMeasurement (physicalPairProjection particles) =
      unorderedPairMeasurement particles :=
  rfl

def physicalUnorderedParticleMeasurement :
    PhysicalParentCarrier →ₗ[ℤ] UnorderedParticleIdentityCarrier :=
  physicalUnorderedPairMeasurement.comp
    (LinearMap.snd ℤ ColoredWaveOne PhysicalParticleTwo)

def physicalSplitKey {index : Nat} (state : EffectiveSplitAt index) :
    Sym2 (Units NNReal) :=
  s(splitLeftUnit state, splitRightUnit state)

@[simp] theorem physicalUnorderedParticleMeasurement_split
    {index : Nat} (state : EffectiveSplitAt index) :
    physicalUnorderedParticleMeasurement (physicalSplitParticleState state) =
      Finsupp.single (physicalSplitKey state) 1 := by
  change physicalUnorderedPairMeasurement
      (physicalPairProjection
        (delta (splitLeftUnit state) ⊗ₜ[ℤ] delta (splitRightUnit state))) =
    Finsupp.single s(splitLeftUnit state, splitRightUnit state) 1
  rw [physicalUnorderedPairMeasurement_projection,
    unorderedPairMeasurement_delta_pair]
  rfl

theorem physicalSplitParticleState_eq_iff_key_eq
    {index : Nat} (left right : EffectiveSplitAt index) :
    physicalSplitParticleState left = physicalSplitParticleState right ↔
      physicalSplitKey left = physicalSplitKey right := by
  constructor
  · intro stateEq
    have measurementEq :=
      congrArg physicalUnorderedParticleMeasurement stateEq
    rw [physicalUnorderedParticleMeasurement_split,
      physicalUnorderedParticleMeasurement_split] at measurementEq
    exact (Finsupp.single_left_inj (by norm_num : (1 : ℤ) ≠ 0)).mp
      measurementEq
  · intro keyEq
    rw [physicalSplitKey, physicalSplitKey, Sym2.eq_iff] at keyEq
    rcases keyEq with ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩
    · rw [physicalSplitParticleState_eq_pairState,
        physicalSplitParticleState_eq_pairState, leftEq, rightEq]
    · rw [physicalSplitParticleState_eq_pairState,
        physicalSplitParticleState_eq_pairState, leftEq, rightEq]
      exact physicalPairState_swap _ _

theorem physicalSplitKey_eq_iff_unorderedSplitKey_eq
    {index : Nat} (left right : EffectiveSplitAt index) :
    physicalSplitKey left = physicalSplitKey right ↔
      unorderedSplitKey left = unorderedSplitKey right := by
  rw [physicalSplitKey, physicalSplitKey, unorderedSplitKey,
    unorderedSplitKey, Sym2.eq_iff, Sym2.eq_iff]
  constructor
  · rintro (⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩)
    · exact .inl
        ⟨splitLeft_eq_splitLeft_of_unit_eq leftEq,
          splitRight_eq_splitRight_of_unit_eq rightEq⟩
    · exact .inr
        ⟨splitLeft_eq_splitRight_of_unit_eq leftEq,
          splitRight_eq_splitLeft_of_unit_eq rightEq⟩
  · rintro (⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩)
    · exact .inl
        ⟨splitLeftUnit_eq_splitLeftUnit_of_eq leftEq,
          splitRightUnit_eq_splitRightUnit_of_eq rightEq⟩
    · exact .inr
        ⟨splitLeftUnit_eq_splitRightUnit_of_eq leftEq,
          splitRightUnit_eq_splitLeftUnit_of_eq rightEq⟩

/-! ## Physical factor actions -/

def physicalFactorDecaySource {index : Nat}
    {source : EffectiveSplitAt index}
    (_channel : FactorDecayChannelAt source) : PhysicalParentCarrier :=
  physicalSplitParticleState source

def physicalFactorDecayTarget {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) : PhysicalParentCarrier :=
  physicalSplitParticleState channel.target

def physicalFactorDecayAction {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) : PhysicalParentCarrier :=
  physicalFactorDecayTarget channel - physicalFactorDecaySource channel

theorem physicalFactorDecayAction_eq_projected_update {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    physicalFactorDecayAction channel =
      physicalParentProjection
        (splitParticleState channel.target - splitParticleState source) := by
  simp [physicalFactorDecayAction, physicalFactorDecayTarget,
    physicalFactorDecaySource, physicalSplitParticleState, map_sub]

theorem physicalFactorDecay_source_add_action {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    physicalFactorDecaySource channel + physicalFactorDecayAction channel =
      physicalFactorDecayTarget channel := by
  unfold physicalFactorDecayAction
  abel

theorem physicalFactorDecayAction_eq_zero_iff {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    physicalFactorDecayAction channel = 0 ↔
      physicalFactorDecayTarget channel = physicalFactorDecaySource channel := by
  unfold physicalFactorDecayAction
  exact sub_eq_zero

theorem physicalFactorDecayAction_ne_zero_iff_key_ne {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    physicalFactorDecayAction channel ≠ 0 ↔
      physicalSplitKey channel.target ≠ physicalSplitKey source := by
  constructor
  · intro actionNe keyEq
    apply actionNe
    apply (physicalFactorDecayAction_eq_zero_iff channel).2
    exact (physicalSplitParticleState_eq_iff_key_eq _ _).2 keyEq
  · intro keyNe actionZero
    apply keyNe
    have endpointEq :=
      (physicalFactorDecayAction_eq_zero_iff channel).1 actionZero
    exact (physicalSplitParticleState_eq_iff_key_eq _ _).1 endpointEq

/-- The arithmetic selector and the Fock quotient classify exactly the same
channels as physical progress. -/
theorem physicalFactorDecayAction_ne_zero_iff_arithmeticProgress
    {index : Nat} {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    physicalFactorDecayAction channel ≠ 0 ↔ channel.IsPhysicalProgress := by
  rw [physicalFactorDecayAction_ne_zero_iff_key_ne]
  constructor
  · intro unitKeyNe arithmeticKeyEq
    exact unitKeyNe
      ((physicalSplitKey_eq_iff_unorderedSplitKey_eq _ _).2 arithmeticKeyEq)
  · intro arithmeticKeyNe unitKeyEq
    exact arithmeticKeyNe
      ((physicalSplitKey_eq_iff_unorderedSplitKey_eq _ _).1 unitKeyEq)

theorem physicalFactorDecay_charge_conserved {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    physicalParticleMeasurement (physicalFactorDecayTarget channel) =
      physicalParticleMeasurement (physicalFactorDecaySource channel) := by
  change particleMeasurement (splitParticleState channel.target) =
    particleMeasurement (splitParticleState source)
  rw [particleMeasurement_splitParticleState,
    particleMeasurement_splitParticleState]

abbrev PhysicalFactorDecayProgressAt {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) : Prop :=
  physicalFactorDecayAction channel ≠ 0

structure SwapOnlyAt {index : Nat} {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) : Prop where
  ordered_ne : channel.target ≠ source
  left_eq : splitLeft channel.target = splitRight source
  right_eq : splitRight channel.target = splitLeft source

theorem SwapOnlyAt.physical_identity {index : Nat}
    {source : EffectiveSplitAt index}
    {channel : FactorDecayChannelAt source}
    (swapOnly : SwapOnlyAt channel) :
    physicalFactorDecayAction channel = 0 := by
  apply (physicalFactorDecayAction_eq_zero_iff channel).2
  exact physicalSplitParticleState_eq_of_swap _ _
    swapOnly.left_eq swapOnly.right_eq

theorem SwapOnlyAt.not_progress {index : Nat}
    {source : EffectiveSplitAt index}
    {channel : FactorDecayChannelAt source}
    (swapOnly : SwapOnlyAt channel) :
    ¬ PhysicalFactorDecayProgressAt channel :=
  fun progress => progress swapOnly.physical_identity

inductive PhysicalFactorDecayDispositionAt {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) : Type
  | presentationIdentity
      (action_eq : physicalFactorDecayAction channel = 0)
  | physicalChange
      (action_ne : PhysicalFactorDecayProgressAt channel)

def generatePhysicalFactorDecayDisposition {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    PhysicalFactorDecayDispositionAt channel := by
  by_cases actionZero : physicalFactorDecayAction channel = 0
  · exact .presentationIdentity actionZero
  · exact .physicalChange actionZero

structure GeneratedPhysicalFactorDecayAt {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source)
    (receipt : OperationalFactorDecayChannelReceiptAt channel) : Type where
  private mk ::
  sourceEndpoint : PhysicalParentCarrier
  sourceEndpoint_eq : sourceEndpoint = physicalFactorDecaySource channel
  targetEndpoint : PhysicalParentCarrier
  targetEndpoint_eq : targetEndpoint = physicalFactorDecayTarget channel
  action : PhysicalParentCarrier
  action_eq : action = physicalFactorDecayAction channel
  source_add_action : sourceEndpoint + action = targetEndpoint
  disposition : PhysicalFactorDecayDispositionAt channel
  lifecycleProgress : receipt.lifecycleEdge.lifecycleEvent.kind.IsProgress

def generatePhysicalFactorDecay {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source)
    (receipt : OperationalFactorDecayChannelReceiptAt channel) :
    GeneratedPhysicalFactorDecayAt channel receipt :=
  { sourceEndpoint := physicalFactorDecaySource channel
    sourceEndpoint_eq := rfl
    targetEndpoint := physicalFactorDecayTarget channel
    targetEndpoint_eq := rfl
    action := physicalFactorDecayAction channel
    action_eq := rfl
    source_add_action := physicalFactorDecay_source_add_action channel
    disposition := generatePhysicalFactorDecayDisposition channel
    lifecycleProgress := receipt.lifecycleProgress }

end

end ParticleWaveFock
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
