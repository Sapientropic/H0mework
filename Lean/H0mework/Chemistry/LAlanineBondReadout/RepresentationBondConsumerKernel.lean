import H0mework.Chemistry.LAlanineBondReadout.SourceIdentity
import H0mework.Foundation.Relations.ConsumerFace

/-! The independent reads of the fixed M3 occurrence precede its concrete bond face. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BondReadout.Consumers

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open LAlanine40K2025.Interface

noncomputable section

def bcpIncidence (pair : ASUHeavyPair) : Bool := (Source.pairReadoutAt pair).bcpFound

def deformationReadout (pair : ASUHeavyPair) : Int × Int × Int :=
  let readout := Source.pairReadoutAt pair
  (readout.midpointDensityDeltaNano, readout.bcpDensityDeltaNano,
    readout.lineIntegralDensityDeltaNanoAngstrom)

def physicalReads : IndependentConsumerSystem ASUHeavyPair where
  Consumer := LAlanine40K2025.Calculation.PhysicalPairConsumer
  Output
    | .address => HeavyAtom × HeavyAtom
    | .topology => Bool
    | .field => PairPhysicalReadout
    | .deformation => Int × Int × Int
  read
    | .address => pairEndpoints
    | .topology => bcpIncidence
    | .field => Source.pairReadoutAt
    | .deformation => deformationReadout
  positive := ⟨.field⟩

def sourceReceiptRead : IndependentReadout ASUHeavyPair where
  Output := String
  read := Source.pairReceiptText

def physicalConsumers := physicalReads.adjoin sourceReceiptRead

abbrev BondFace := (HeavyAtom × HeavyAtom) × PairPhysicalReadout × String

def bondFaceRead (pair : ASUHeavyPair) : BondFace :=
  (pairEndpoints pair, Source.pairReadoutAt pair, Source.pairReceiptText pair)

theorem bondFace_kernelExact_at_installedPhysicalConsumers :
    FaceKernelExactAt physicalConsumers bondFaceRead := by
  intro left right
  constructor
  · intro same consumer
    have address := congrArg Prod.fst same
    have field := congrArg (fun face : BondFace => face.2.1) same
    cases consumer with
    | inl consumer =>
      cases consumer with
      | address => exact address
      | topology => exact congrArg PairPhysicalReadout.bcpFound field
      | field => exact field
      | deformation => exact congrArg (fun r : PairPhysicalReadout =>
          (r.midpointDensityDeltaNano, r.bcpDensityDeltaNano,
            r.lineIntegralDensityDeltaNanoAngstrom)) field
    | inr _ => exact congrArg (fun face : BondFace => face.2.2) same
  · intro same
    exact Prod.ext (same (.inl .address))
      (Prod.ext (same (.inl .field)) (same (.inr PUnit.unit)))

theorem bondFaceRead_injective : Function.Injective bondFaceRead := by
  intro left right same
  exact pairEndpoints_injective (congrArg Prod.fst same)

noncomputable def bondQuotientEquivRange :
    physicalConsumers.Quotient ≃ Set.range bondFaceRead :=
  bondFace_kernelExact_at_installedPhysicalConsumers.quotientEquivRange

theorem everyConsumer_uniqueFactorization (consumer : physicalConsumers.Consumer) :
    ∃! factor : Set.range bondFaceRead → physicalConsumers.Output consumer,
      ∀ pair, factor ⟨bondFaceRead pair, pair, rfl⟩ = physicalConsumers.read consumer pair :=
  bondFace_kernelExact_at_installedPhysicalConsumers.everyConsumer_unique_factorization consumer

theorem completeCarrier_uniqueIso {Alternate : Type} (alternate : ASUHeavyPair → Alternate)
    (alternateExact : FaceKernelExactAt physicalConsumers alternate) :
    ∃! equivalence : Set.range bondFaceRead ≃ Set.range alternate,
      ∀ pair, equivalence ⟨bondFaceRead pair, pair, rfl⟩ = ⟨alternate pair, pair, rfl⟩ :=
  ⟨bondFace_kernelExact_at_installedPhysicalConsumers.completeCarrierEquiv alternateExact,
    bondFace_kernelExact_at_installedPhysicalConsumers.completeCarrierEquiv_commutes alternateExact,
    fun candidate commutes =>
      bondFace_kernelExact_at_installedPhysicalConsumers.completeCarrierEquiv_unique
        alternateExact candidate commutes⟩

theorem noHiddenFieldDirection {left right : ASUHeavyPair}
    (different : bondFaceRead left ≠ bondFaceRead right) :
    ¬ physicalConsumers.Indistinguishable left right :=
  bondFace_kernelExact_at_installedPhysicalConsumers.noHiddenDirection different

end
end LAlanine40K2025.BondReadout.Consumers
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
