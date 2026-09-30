import H0mework.Chemistry.LAlanineChargeIdentity.CalculationIntegerRecovery
import H0mework.Foundation.Relations.ConsumerFace
import Mathlib.Logic.Equiv.Sum

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ChargeIdentity.Consumers

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open LAlanine40K2025.Force.Interface
noncomputable section

/-- This consumer computes from the unit fields and old total attraction field, not from nuclear labels. -/
def elementConsumers : IndependentConsumerSystem Atom where
  Consumer := PUnit
  Output := fun _ => Int
  read := fun _ => Source.decodedCharge
  positive := ⟨PUnit.unit⟩

def elementFace : Atom → Int := SourceData.parentCharge

theorem elementFace_kernelExact : FaceKernelExactAt elementConsumers elementFace := by
  intro left right
  constructor
  · intro same consumer
    change Source.decodedCharge left = Source.decodedCharge right
    rw [Recovery.decoded_eq_original, Recovery.decoded_eq_original]
    exact same
  · intro same
    have decoded := same PUnit.unit
    change Source.decodedCharge left = Source.decodedCharge right at decoded
    rw [Recovery.decoded_eq_original, Recovery.decoded_eq_original] at decoded
    exact decoded

def elementQuotientEquivRange : elementConsumers.Quotient ≃ Set.range elementFace :=
  elementFace_kernelExact.quotientEquivRange

theorem everyConsumer_uniqueFactorization (consumer : elementConsumers.Consumer) :
    ∃! factor : Set.range elementFace → elementConsumers.Output consumer,
      ∀ atom, factor ⟨elementFace atom, atom, rfl⟩ = elementConsumers.read consumer atom :=
  elementFace_kernelExact.everyConsumer_unique_factorization consumer

theorem completeCarrier_uniqueIso {Alternate : Type} (alternate : Atom → Alternate)
    (alternateExact : FaceKernelExactAt elementConsumers alternate) :
    ∃! equivalence : Set.range elementFace ≃ Set.range alternate,
      ∀ atom, equivalence ⟨elementFace atom, atom, rfl⟩ = ⟨alternate atom, atom, rfl⟩ :=
  ⟨elementFace_kernelExact.completeCarrierEquiv alternateExact,
    elementFace_kernelExact.completeCarrierEquiv_commutes alternateExact,
    fun candidate commutes => elementFace_kernelExact.completeCarrierEquiv_unique alternateExact candidate commutes⟩

theorem noHiddenElementDirection {left right : Atom} (different : elementFace left ≠ elementFace right) :
    ¬ elementConsumers.Indistinguishable left right :=
  elementFace_kernelExact.noHiddenDirection different

/-- The element quotient does not erase its original addressed occurrence fibre. -/
abbrev ElementResidual (charge : Int) := {atom : Atom // elementFace atom = charge}

def atomEquivElementResidual : Atom ≃ Σ charge : Int, ElementResidual charge :=
  (Equiv.sigmaFiberEquiv elementFace).symm

theorem atomEquivElementResidual_commutes (atom : Atom) :
    (atomEquivElementResidual atom).1 = elementFace atom ∧
    (atomEquivElementResidual atom).2.val = atom := ⟨rfl, rfl⟩

theorem atomEquivElementResidual_reconstructs (atom : Atom) :
    atomEquivElementResidual.symm (atomEquivElementResidual atom) = atom :=
  atomEquivElementResidual.symm_apply_apply atom

def attractionRead : IndependentReadout Atom where
  Output := Int
  read := SourceData.parentAttraction

theorem sameElement_differentActualAttraction : FaceKernelEscapeAt elementFace attractionRead := by
  refine ⟨(0 : Atom), (1 : Atom), ?_, ?_⟩
  · change (8 : Int) = 8
    rfl
  · change (-250504932396 : Int) ≠ -253374739253
    decide +kernel

theorem element_cannotMint_attraction :
    ¬ Function.FactorsThrough SourceData.parentAttraction elementFace :=
  sameElement_differentActualAttraction.not_factorsThrough

theorem elementFace_not_injective : ¬ Function.Injective elementFace := by
  intro injective
  have same : elementFace (0 : Atom) = elementFace (1 : Atom) := rfl
  have different : (0 : Atom) ≠ 1 := by decide +kernel
  exact different (injective same)

end
end LAlanine40K2025.ChargeIdentity.Consumers
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
