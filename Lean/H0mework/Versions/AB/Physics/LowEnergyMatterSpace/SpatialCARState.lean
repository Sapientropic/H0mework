import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.SpatialCARSpan
import H0mework.Physics.LowEnergyMatterSpace.SpatialCARWords
import H0mework.Physics.LowEnergyMatterSpace.SpatialCARAdjoint

/-! Source-prepared spatial moments, with arbitrary finite-word compatibility under adding tests. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.SpatialCAR
open QuantizationCheck.Fermion Fermion
open scoped InnerProductSpace ComplexOrder
noncomputable section
variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι] [Fintype κ]

def Letter.map {α β : Type*} (embedding : α → β) : Letter α → Letter β
  | .create i => .create (embedding i)
  | .annihilate i => .annihilate (embedding i)

theorem wordOperator_map {α β m : Type*} [Fintype m] [LinearOrder m]
    (coordinates : β → m → ℂ) (embedding : α → β) (word : List (Letter α)) :
    wordOperator coordinates (word.map (Letter.map embedding))=
      wordOperator (fun i => coordinates (embedding i)) word := by
  induction word with
  | nil => rfl
  | cons letter rest ih =>
    cases letter <;> simp only [List.map_cons,wordOperator,ih,Letter.map,letterOperator]

def spatialMoment (prepared : E) (tests : ι → E) (word : List (Letter (Option ι))) : ℂ :=
  pairing (preparedFock prepared tests)
    (wordOperator (fun i => coordinates prepared tests i) word (preparedFock prepared tests))

theorem spatialMoment_nil (prepared : E) (tests : ι → E) :
    spatialMoment prepared tests []=inner ℂ prepared prepared :=
  preparedFock_pairing prepared tests

theorem spatialMoment_positive {α : Type*} (prepared : E) (tests : ι → E)
    (words : α → List (Letter (Option ι))) :
    Matrix.PosSemidef (fun i j => spatialMoment prepared tests (wordAdjoint (words i)++words j)) :=
  allWord_positive (fun i => coordinates prepared tests i) none words

theorem spatialMoment_gram (prepared : E) (tests : ι → E) (word : List (Letter (Option ι))) :
    spatialMoment prepared tests word=
      expressionEvaluation (fun i j => inner ℂ (family prepared tests i) (family prepared tests j)) none
        (wordExpression (fun i j => inner ℂ (family prepared tests i) (family prepared tests j)) none word) :=
  allWord_gram_evaluation (fun i => coordinates prepared tests i) _ (coordinates_pair prepared tests) none word

theorem spatialMoment_embedding (prepared : E) (tests : ι → E) (larger : κ → E)
    (embedding : ι → κ) (sameTests : ∀ i, larger (embedding i)=tests i)
    (word : List (Letter (Option ι))) :
    spatialMoment prepared tests word=
      spatialMoment prepared larger (word.map (Letter.map (Option.map embedding))) := by
  have familySame (i : Option ι) : family prepared larger (Option.map embedding i)=family prepared tests i := by
    cases i with
    | none => rfl
    | some i => exact sameTests i
  have gramSame (i j : Option ι) :
      modePair (coordinates prepared tests i) (coordinates prepared tests j)=
      modePair (coordinates prepared larger (Option.map embedding i))
        (coordinates prepared larger (Option.map embedding j)) := by
    rw [coordinates_pair,coordinates_pair,familySame,familySame]
  unfold spatialMoment preparedFock
  rw [wordOperator_map]
  exact allWord_embedding_invariant (fun i => coordinates prepared tests i)
    (fun i => coordinates prepared larger (Option.map embedding i)) gramSame none word

theorem spatialMoment_twoPoint (prepared : E) (tests : ι → E) (i j : Option ι) :
    spatialMoment prepared tests [.create i,.annihilate j]=
      inner ℂ (family prepared tests j) prepared*inner ℂ prepared (family prepared tests i) := by
  simpa only [spatialMoment,wordOperator,letterOperator,mul_one,createTest,annihilateTest] using
    spatial_twoPoint prepared tests i j

theorem spatialMoment_fourPoint (prepared : E) (tests : ι → E) (i j k l : Option ι) :
    spatialMoment prepared tests [.create i,.annihilate j,.create k,.annihilate l]=
      inner ℂ (family prepared tests j) (family prepared tests k)*
        inner ℂ (family prepared tests l) prepared*inner ℂ prepared (family prepared tests i) := by
  simpa only [spatialMoment,wordOperator,letterOperator,mul_one,mul_assoc,createTest,annihilateTest] using
    spatial_fourPoint prepared tests i j k l

theorem source_twoPoint_occupation (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (tests : ι → MatterL2) (i j : ι) :
    spatialMoment (normalizedPreparation force continuousForce t) tests [.create (some i),.annihilate (some j)]=
      inner ℂ (tests j) (preparedOccupation force continuousForce t (tests i)) := by
  rw [spatialMoment_twoPoint]
  change inner ℂ (tests j) (normalizedPreparation force continuousForce t)*
      inner ℂ (normalizedPreparation force continuousForce t) (tests i)=
    inner ℂ (tests j) (inner ℂ (normalizedPreparation force continuousForce t) (tests i) •
      normalizedPreparation force continuousForce t)
  rw [inner_smul_right,mul_comm]

theorem source_spatialMoment_unit (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (tests : ι → MatterL2)
    (nonzero : spatialPreparation force continuousForce t≠0) :
    spatialMoment (normalizedPreparation force continuousForce t) tests []=1 :=
  source_preparedFock_unit force continuousForce t tests nonzero

theorem source_connected_fourPoint (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (tests : ι → MatterL2) (i j k l : ι) :
    spatialMoment (normalizedPreparation force continuousForce t) tests
        [.create (some i),.annihilate (some j),.create (some k),.annihilate (some l)]-
      spatialMoment (normalizedPreparation force continuousForce t) tests [.create (some i),.annihilate (some j)]*
        spatialMoment (normalizedPreparation force continuousForce t) tests [.create (some k),.annihilate (some l)]=
      inner ℂ (tests l) (preparedOccupation force continuousForce t (tests i))*
        inner ℂ (tests j) ((1-preparedOccupation force continuousForce t) (tests k)) := by
  rw [spatialMoment_fourPoint,spatialMoment_twoPoint,spatialMoment_twoPoint]
  change inner ℂ (tests j) (tests k)*
      inner ℂ (tests l) (normalizedPreparation force continuousForce t)*
      inner ℂ (normalizedPreparation force continuousForce t) (tests i)-
    (inner ℂ (tests j) (normalizedPreparation force continuousForce t)*
      inner ℂ (normalizedPreparation force continuousForce t) (tests i))*
    (inner ℂ (tests l) (normalizedPreparation force continuousForce t)*
      inner ℂ (normalizedPreparation force continuousForce t) (tests k))=_
  change _=inner ℂ (tests l)
      (inner ℂ (normalizedPreparation force continuousForce t) (tests i) •
        normalizedPreparation force continuousForce t)*
    inner ℂ (tests j) (tests k-inner ℂ (normalizedPreparation force continuousForce t) (tests k) •
        normalizedPreparation force continuousForce t)
  rw [inner_smul_right,inner_sub_right,inner_smul_right]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.SpatialCAR
