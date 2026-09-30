import H0mework.Chemistry.LAlanineAtomicMass.SourceMassNumber
import H0mework.Chemistry.LAlanineChargeIdentity.RepresentationElementConsumerKernel

/-!
# Same-occurrence isotope identity and retained atomic fibres

The nuclear-field decoder and the original inertial mass are independent consumers.
Their exact quotient is the source-scoped (Z,A) signature. The original atom address
remains in its dependent fibre, preserving all M3 environment readouts.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.AtomicMass

open Force.Interface Inertia.SourceParsing
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
noncomputable section

inductive AtomicConsumer
  | nuclearField | inertialMass

/-- Consumers read the existing field decoder and actual dynamical mass. -/
def atomicConsumers : IndependentConsumerSystem Atom where
  Consumer := AtomicConsumer
  Output := fun consumer => match consumer with
    | .nuclearField => Int
    | .inertialMass => ℚ
  read := fun consumer => match consumer with
    | .nuclearField => ChargeIdentity.Source.decodedCharge
    | .inertialMass => Source.actualMass
  positive := ⟨.inertialMass⟩

/-- A model isotope signature; the source does not specify nuclear energy states. -/
def isotopeFace (atom : Atom) : Int × Int :=
  (ChargeIdentity.Source.decodedCharge atom, Source.massNumber atom)

theorem massNumber_eq_iff_actualMass_eq (left right : Atom) :
    Source.massNumber left = Source.massNumber right ↔
      Source.actualMass left = Source.actualMass right := by
  rw [Source.massNumber_eq_recorded, Source.massNumber_eq_recorded]
  change Source.integerRead _ left = Source.integerRead _ right ↔
    massRead _ left = massRead _ right
  fin_cases left <;> fin_cases right <;>
    norm_num [Source.integerRead, massRead, rationalRead]

theorem isotopeFace_kernelExact : FaceKernelExactAt atomicConsumers isotopeFace := by
  intro left right
  constructor
  · intro same consumer
    cases consumer with
    | nuclearField => exact congrArg Prod.fst same
    | inertialMass => exact (massNumber_eq_iff_actualMass_eq left right).mp (congrArg Prod.snd same)
  · intro same
    apply Prod.ext
    · exact same .nuclearField
    · exact (massNumber_eq_iff_actualMass_eq left right).mpr (same .inertialMass)

def isotopeQuotientEquivRange : atomicConsumers.Quotient ≃ Set.range isotopeFace :=
  isotopeFace_kernelExact.quotientEquivRange

theorem everyAtomicConsumer_uniqueFactorization (consumer : atomicConsumers.Consumer) :
    ∃! factor : Set.range isotopeFace → atomicConsumers.Output consumer,
      ∀ atom, factor ⟨isotopeFace atom, atom, rfl⟩ = atomicConsumers.read consumer atom :=
  isotopeFace_kernelExact.everyConsumer_unique_factorization consumer

/-- All identity and environment distinctions survive in the original atom fibre. -/
abbrev AtomicResidual (charge massNumber : Int) :=
  {atom : Atom // isotopeFace atom = (charge, massNumber)}

def atomEquivIsotopeResidual : Atom ≃ Σ charge : Int, Σ massNumber : Int,
    AtomicResidual charge massNumber where
  toFun := fun atom => ⟨(isotopeFace atom).1, (isotopeFace atom).2, atom, rfl⟩
  invFun := fun atom => atom.2.2.val
  left_inv := fun _ => rfl
  right_inv := by
    rintro ⟨charge, number, atom, same⟩
    cases same
    rfl

theorem atomicResidual_reconstructs (atom : Atom) :
    atomEquivIsotopeResidual.symm (atomEquivIsotopeResidual atom) = atom := rfl

theorem source_isotope_assignment (atom : Atom) :
    isotopeFace atom =
      (ChargeIdentity.Consumers.elementFace atom, Source.preparation.defaultMassNumber atom) := by
  exact Prod.ext (ChargeIdentity.Recovery.decoded_eq_original atom)
    (Source.massNumber_eq_recorded atom)

theorem nitrogen_isotope : isotopeFace 2 = (7, 14) := by
  rw [source_isotope_assignment]
  rfl

theorem source_isotope_census (atom : Atom) :
    isotopeFace atom = (1, 1) ∨ isotopeFace atom = (6, 12) ∨
      isotopeFace atom = (7, 14) ∨ isotopeFace atom = (8, 16) := by
  rw [source_isotope_assignment]
  change (ChargeIdentity.SourceData.parentCharge atom, Source.integerRead _ atom) = (1, 1) ∨
    (ChargeIdentity.SourceData.parentCharge atom, Source.integerRead _ atom) = (6, 12) ∨
    (ChargeIdentity.SourceData.parentCharge atom, Source.integerRead _ atom) = (7, 14) ∨
    (ChargeIdentity.SourceData.parentCharge atom, Source.integerRead _ atom) = (8, 16)
  fin_cases atom <;> decide +kernel

end
end LAlanine40K2025.AtomicMass
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
