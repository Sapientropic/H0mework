import H0mework.Physics.LowEnergyMatterSpace.PerturbedPhysical
import H0mework.Physics.LowEnergyMatterSpace.SpatialResponseSource

/-! Finite source developments preserve the complete CAR words and enter the original quantum readout. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
open Fermion SU7MotherLieAlgebra DiracCliffordRepresentation Stage9DEF
noncomputable section
attribute [local instance] instLinearOrderSourceIndex

def localPerturbedDevelopment (profile : ℝ → BoundedProfile) (continuousProfile : Continuous profile)
    (data : LorentzianIndex → P286LieBlockData) :
    PerturbedDevelopment (fun t => localGaugeHamiltonian (profile t) data) :=
  perturbedDevelopment _ (localGaugeHistory_continuous profile continuousProfile data)

private theorem sourceOperator_smul (r : ℝ) (A : SourceMatrix) (v : MatterFiber) :
    hamiltonianOperator ((r : ℂ) • A) v=(r : ℂ) • hamiltonianOperator A v := by
  unfold hamiltonianOperator
  rw [map_smul]
  rfl

theorem local_perturbed_force_native (profile : ℝ → BoundedProfile)
    (realProfile : ∀ t, ∀ᵐ x ∂volume, star (profile t x)=profile t x)
    (data : LorentzianIndex → P286LieBlockData) (time epsilon : ℝ) (state : MatterL2) :
    ((-Complex.I*(epsilon : ℂ)) • localGaugeHamiltonian (profile time) data state)=ᵐ[volume]
      fun x => gaugeForceOperator ((epsilon*(profile time x).re) • data) (state x) := by
  filter_upwards [Lp.coeFn_smul (-Complex.I*(epsilon : ℂ))
      (localGaugeHamiltonian (profile time) data state),
    localGaugeHamiltonian_native_ae (profile time) (realProfile time) data state]
    with x scaled original
  rw [scaled]
  change (-Complex.I*(epsilon : ℂ)) • ((localGaugeHamiltonian (profile time) data state) x)=_
  rw [original]
  change (-Complex.I*(epsilon : ℂ)) • hamiltonianOperator
    (gaugeHamiltonianMatrix ((profile time x).re • data)) (state x)=_
  simp only [gaugeForceOperator,gaugeHamiltonianMatrix_real_smul,sourceOperator_smul,smul_apply,smul_smul]
  congr 1
  push_cast
  ring

namespace PerturbedDevelopment
variable {perturbation : ℝ → MatterL2 →L[ℂ] MatterL2}
    (development : PerturbedDevelopment perturbation)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t))
    (epsilon : ℝ) (coupling : |epsilon|≤1) (start time : ℝ)
    (atStart : start ∈ Set.Ioo (-development.radius) development.radius)
    (atTime : time ∈ Set.Ioo (-development.radius) development.radius)

def physicalOperator : MatterL2 →L[ℂ] MatterL2 :=
  (development.physicalUnitary symmetric epsilon coupling start time atStart atTime).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem physicalOperator_apply (initial : MatterL2) :
    development.physicalOperator symmetric epsilon coupling start time atStart atTime initial=
      development.physicalCurve epsilon start initial time := rfl

def finiteObservable (observable : MatterL2 →L[ℂ] MatterL2) : MatterL2 →L[ℂ] MatterL2 :=
  (development.physicalOperator symmetric epsilon coupling start time atStart atTime).adjoint.comp
    (observable.comp (development.physicalOperator symmetric epsilon coupling start time atStart atTime))

theorem finiteObservable_pair (observable : MatterL2 →L[ℂ] MatterL2) (initial : MatterL2) :
    inner ℂ initial (development.finiteObservable symmetric epsilon coupling start time atStart atTime observable initial)=
      inner ℂ (development.physicalCurve epsilon start initial time)
        (observable (development.physicalCurve epsilon start initial time)) := by
  change inner ℂ initial ((development.physicalOperator symmetric epsilon coupling start time atStart atTime).adjoint
    (observable (development.physicalOperator symmetric epsilon coupling start time atStart atTime initial)))=_
  rw [ContinuousLinearMap.adjoint_inner_right,physicalOperator_apply]

theorem finiteObservable_selfAdjoint (observable : MatterL2 →L[ℂ] MatterL2)
    (hermitian : IsSelfAdjoint observable) :
    IsSelfAdjoint (development.finiteObservable symmetric epsilon coupling start time atStart atTime observable) := by
  change star (star (development.physicalOperator symmetric epsilon coupling start time atStart atTime)*observable*
    development.physicalOperator symmetric epsilon coupling start time atStart atTime)=
      star (development.physicalOperator symmetric epsilon coupling start time atStart atTime)*
        (observable*development.physicalOperator symmetric epsilon coupling start time atStart atTime)
  simp only [star_mul,star_star,hermitian.star_eq,mul_assoc]

theorem finiteObservable_source (preparation : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousPreparation : Continuous preparation) (preparedAt : ℝ) (observable : MatterL2 →L[ℂ] MatterL2) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1
        (normalizedPreparationNative preparation continuousPreparation preparedAt
          (development.finiteObservable symmetric epsilon coupling start time atStart atTime observable))))=
      inner ℂ (development.physicalCurve epsilon start
        (normalizedPreparation preparation continuousPreparation preparedAt) time)
        (observable (development.physicalCurve epsilon start
          (normalizedPreparation preparation continuousPreparation preparedAt) time)) := by
  rw [normalizedPreparationNative_sourceResponse]
  exact development.finiteObservable_pair symmetric epsilon coupling start time atStart atTime observable _

theorem finite_current_source (preparation : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousPreparation : Continuous preparation) (preparedAt : ℝ)
    (detector : BoundedProfile) (realDetector : ∀ᵐ x ∂volume, star (detector x)=detector x)
    (data : LorentzianIndex → P286LieBlockData) :
    measuredCurrent detector data (development.physicalCurve epsilon start
      (normalizedPreparation preparation continuousPreparation preparedAt) time)=
    (State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1
        (normalizedPreparationNative preparation continuousPreparation preparedAt
          (development.finiteObservable symmetric epsilon coupling start time atStart atTime
            (localCurrentOperator detector data)))))).re := by
  rw [measuredCurrent_pair detector realDetector,
    development.finiteObservable_source symmetric epsilon coupling start time atStart atTime]

include symmetric coupling atStart atTime in
theorem finite_spatial_CAR {ι : Type*} [Fintype ι] (prepared : MatterL2)
    (tests : ι → MatterL2) (word : List (SpatialCAR.Letter (Option ι))) :
    SpatialCAR.spatialMoment (development.physicalCurve epsilon start prepared time)
      (fun i => development.physicalCurve epsilon start (tests i) time) word=
      SpatialCAR.spatialMoment prepared tests word := by
  have familyImage (i : Option ι) :
      SpatialCAR.family (development.physicalCurve epsilon start prepared time)
        (fun j => development.physicalCurve epsilon start (tests j) time) i=
      development.physicalUnitary symmetric epsilon coupling start time atStart atTime
        (SpatialCAR.family prepared tests i) := by cases i <;> rfl
  rw [SpatialCAR.spatialMoment_gram,SpatialCAR.spatialMoment_gram]
  simp_rw [familyImage,(development.physicalUnitary symmetric epsilon coupling start time atStart atTime).inner_map_map]

end PerturbedDevelopment
end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
