import H0mework.Versions.AB.Chemistry.LAlanineBasinPartition.CalculationBasinIntegrals
import H0mework.Foundation.Relations.ConsumerFace

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinPartition.Consumers

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open LAlanine40K2025.Force.Interface SourceData
noncomputable section

attribute [local irreducible] Calculation.basinIntegral Calculation.basinCount

inductive BasinConsumer
  | address | nuclearIdentity | count | field (channel : Field)

def independentConsumers : IndependentConsumerSystem Atom where
  Consumer := BasinConsumer
  Output
    | .address => Atom
    | .nuclearIdentity => Int
    | .count => Nat
    | .field _ => Int
  read
    | .address => id
    | .nuclearIdentity => Runtime.basinParentCharge
    | .count => fun atom => Calculation.basinCount (atomicBucket atom)
    | .field channel => fun atom => Calculation.basinIntegral (atomicBucket atom) channel
  positive := ⟨.field 0⟩

abbrev BasinFace := Atom × Int × Nat × (Field → Int)

def basinFaceRead (atom : Atom) : BasinFace :=
  (atom, Runtime.basinParentCharge atom, Calculation.basinCount (atomicBucket atom),
    Calculation.basinIntegral (atomicBucket atom))

theorem basinFace_kernelExact : FaceKernelExactAt independentConsumers basinFaceRead := by
  intro left right
  constructor
  · intro same consumer
    cases consumer with
    | address => exact congrArg Prod.fst same
    | nuclearIdentity => exact congrArg (fun face : BasinFace => face.2.1) same
    | count => exact congrArg (fun face : BasinFace => face.2.2.1) same
    | field channel => exact congrArg (fun face : BasinFace => face.2.2.2 channel) same
  · intro same
    exact Prod.ext (same .address) (Prod.ext (same .nuclearIdentity)
      (Prod.ext (same .count) (funext (fun channel => same (.field channel)))))

def basinQuotientEquivRange : independentConsumers.Quotient ≃ Set.range basinFaceRead :=
  basinFace_kernelExact.quotientEquivRange

theorem everyConsumer_uniqueFactorization (consumer : independentConsumers.Consumer) :
    ∃! factor : Set.range basinFaceRead → independentConsumers.Output consumer,
      ∀ atom, factor ⟨basinFaceRead atom, atom, rfl⟩ = independentConsumers.read consumer atom :=
  basinFace_kernelExact.everyConsumer_unique_factorization consumer

theorem completeCarrier_uniqueIso {Alternate : Type} (alternate : Atom → Alternate)
    (alternateExact : FaceKernelExactAt independentConsumers alternate) :
    ∃! equivalence : Set.range basinFaceRead ≃ Set.range alternate,
      ∀ atom, equivalence ⟨basinFaceRead atom, atom, rfl⟩ = ⟨alternate atom, atom, rfl⟩ :=
  ⟨basinFace_kernelExact.completeCarrierEquiv alternateExact,
    basinFace_kernelExact.completeCarrierEquiv_commutes alternateExact,
    fun candidate commutes => basinFace_kernelExact.completeCarrierEquiv_unique alternateExact candidate commutes⟩

theorem noHiddenBasinDirection {left right : Atom} (different : basinFaceRead left ≠ basinFaceRead right) :
    ¬ independentConsumers.Indistinguishable left right :=
  basinFace_kernelExact.noHiddenDirection different

def population (atom : Atom) : Int := Calculation.basinIntegral (atomicBucket atom) 0

def netChargePico (atom : Atom) : Int :=
  1000000000000 * Runtime.basinParentCharge atom - population atom

theorem population_and_netCharge_settle (atom : Atom) :
    population atom + netChargePico atom = 1000000000000 * Runtime.basinParentCharge atom := by
  unfold netChargePico
  omega

def populationRead : IndependentReadout Atom where
  Output := Int
  read := population

theorem elementFace_populationEscape :
    FaceKernelEscapeAt ChargeIdentity.Consumers.elementFace populationRead := by
  refine ⟨(0 : Atom), (1 : Atom), rfl, ?_⟩
  change Calculation.basinIntegral (atomicBucket 0) 0 ≠ Calculation.basinIntegral (atomicBucket 1) 0
  rw [Calculation.basinIntegral_eq_reported, Calculation.basinIntegral_eq_reported]
  change (9172651879713 : Int) ≠ 9230505025560
  decide +kernel

theorem element_cannotMint_population :
    ¬ Function.FactorsThrough population ChargeIdentity.Consumers.elementFace :=
  elementFace_populationEscape.not_factorsThrough

theorem sameElement_differentNetCharge : netChargePico (0 : Atom) ≠ netChargePico 1 := by
  change 1000000000000 * ChargeIdentity.Source.decodedCharge 0 - population 0 ≠
    1000000000000 * ChargeIdentity.Source.decodedCharge 1 - population 1
  rw [ChargeIdentity.Recovery.decoded_eq_original, ChargeIdentity.Recovery.decoded_eq_original]
  unfold population
  rw [Calculation.basinIntegral_eq_reported, Calculation.basinIntegral_eq_reported]
  change (-1172651879713 : Int) ≠ -1230505025560
  decide +kernel

end
end LAlanine40K2025.BasinPartition.Consumers
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
