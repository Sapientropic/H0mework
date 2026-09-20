import H0mework.Physics.LowEnergyMatterSpace.SpatialCARAlgebra
import H0mework.Physics.LowEnergyMatterSpace.PreparationState
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Finite spatial tests and the actual prepared vector generate their common CAR carrier. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.SpatialCAR
open QuantizationCheck.Fermion Fermion
open scoped InnerProductSpace Matrix
noncomputable section
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]

def family (prepared : E) (tests : ι → E) : Option ι → E
  | none => prepared
  | some i => tests i

def carrier (prepared : E) (tests : ι → E) : Submodule ℂ E :=
  Submodule.span ℂ (Set.range (family prepared tests))

instance carrier_finite (prepared : E) (tests : ι → E) : FiniteDimensional ℂ (carrier prepared tests) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

def member (prepared : E) (tests : ι → E) (i : Option ι) : carrier prepared tests :=
  ⟨family prepared tests i,Submodule.subset_span (Set.mem_range_self i)⟩

abbrev Modes (prepared : E) (tests : ι → E) := Fin (Module.finrank ℂ (carrier prepared tests))

def coordinates (prepared : E) (tests : ι → E) (i : Option ι) :
    EuclideanSpace ℂ (Modes prepared tests) :=
  (stdOrthonormalBasis ℂ (carrier prepared tests)).repr (member prepared tests i)

theorem coordinates_pair (prepared : E) (tests : ι → E) (i j : Option ι) :
    modePair (coordinates prepared tests i) (coordinates prepared tests j)=
      inner ℂ (family prepared tests i) (family prepared tests j) := by
  have isometry := (stdOrthonormalBasis ℂ (carrier prepared tests)).repr.inner_map_map
    (member prepared tests i) (member prepared tests j)
  change inner ℂ (coordinates prepared tests i) (coordinates prepared tests j)=
    inner ℂ (family prepared tests i) (family prepared tests j) at isometry
  rw [EuclideanSpace.inner_eq_star_dotProduct] at isometry
  rw [← isometry]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

def preparedFock (prepared : E) (tests : ι → E) : Fock (Modes prepared tests) :=
  oneParticle (coordinates prepared tests none)

def createTest (prepared : E) (tests : ι → E) (i : Option ι) : Module.End ℂ (Fock (Modes prepared tests)) :=
  waveCreation (coordinates prepared tests i)

def annihilateTest (prepared : E) (tests : ι → E) (i : Option ι) : Module.End ℂ (Fock (Modes prepared tests)) :=
  annihilator (coordinates prepared tests i)

theorem spatial_car (prepared : E) (tests : ι → E) (i j : Option ι) :
    annihilateTest prepared tests i * createTest prepared tests j+
      createTest prepared tests j * annihilateTest prepared tests i=
      inner ℂ (family prepared tests i) (family prepared tests j) •
        (1 : Module.End ℂ (Fock (Modes prepared tests))) := by
  rw [← coordinates_pair]
  exact wave_car _ _

theorem spatial_annihilation_car (prepared : E) (tests : ι → E) (i j : Option ι) :
    annihilateTest prepared tests i * annihilateTest prepared tests j+
      annihilateTest prepared tests j * annihilateTest prepared tests i=0 :=
  wave_annihilation_car _ _

theorem spatial_creation_car (prepared : E) (tests : ι → E) (i j : Option ι) :
    createTest prepared tests i * createTest prepared tests j+
      createTest prepared tests j * createTest prepared tests i=0 :=
  wave_creation_car _ _

theorem preparedFock_pairing (prepared : E) (tests : ι → E) :
    pairing (preparedFock prepared tests) (preparedFock prepared tests)=inner ℂ prepared prepared := by
  rw [preparedFock,pairing_oneParticle]
  exact coordinates_pair prepared tests none none

theorem spatial_twoPoint (prepared : E) (tests : ι → E) (i j : Option ι) :
    pairing (preparedFock prepared tests)
      ((createTest prepared tests i * annihilateTest prepared tests j) (preparedFock prepared tests))=
      inner ℂ (family prepared tests j) prepared*inner ℂ prepared (family prepared tests i) := by
  rw [createTest,annihilateTest,preparedFock,occupation_twoPoint,coordinates_pair,coordinates_pair]
  rfl

theorem spatial_fourPoint (prepared : E) (tests : ι → E) (i j k l : Option ι) :
    pairing (preparedFock prepared tests)
      ((createTest prepared tests i * annihilateTest prepared tests j *
        createTest prepared tests k * annihilateTest prepared tests l) (preparedFock prepared tests))=
      inner ℂ (family prepared tests j) (family prepared tests k)*
        inner ℂ (family prepared tests l) prepared*inner ℂ prepared (family prepared tests i) := by
  rw [createTest,annihilateTest,createTest,annihilateTest,preparedFock,
    occupation_fourPoint,coordinates_pair,coordinates_pair,coordinates_pair]
  rfl

theorem source_preparedFock_unit (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (tests : ι → MatterL2)
    (nonzero : spatialPreparation force continuousForce t≠0) :
    pairing (preparedFock (normalizedPreparation force continuousForce t) tests)
      (preparedFock (normalizedPreparation force continuousForce t) tests)=1 := by
  rw [preparedFock_pairing,inner_self_eq_norm_sq_to_K,
    normalizedPreparation_norm force continuousForce t nonzero]
  norm_num

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.SpatialCAR
