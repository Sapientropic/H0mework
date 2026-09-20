import H0mework.Physics.LowEnergyMatterSpace.SpatialCARState
import H0mework.Physics.LowEnergyMatterSpace.PreparationNative

/-! Complete spatial CAR words return through the original full-matter Stage10 consumer. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.SpatialCAR
open QuantizationCheck.Fermion Fermion Stage9DEF
open scoped InnerProductSpace
noncomputable section

abbrev FockHilbert (m : Type*) := EuclideanSpace ℂ (Finset m)

def oneParticleHilbert {m : Type*} [Fintype m] [LinearOrder m] :
    EuclideanSpace ℂ m →ₗ[ℂ] FockHilbert m where
  toFun u := WithLp.toLp 2 (oneParticle u)
  map_add' u v := by
    ext occupied
    exact congrFun (oneParticleLinear.map_add (fun i => u i) (fun i => v i)) occupied
  map_smul' c u := by
    ext occupied
    exact congrFun (oneParticleLinear.map_smul c (fun i => u i)) occupied

def fockOperator {m : Type*} [Fintype m] (action : Module.End ℂ (Fock m)) : FockHilbert m →L[ℂ] FockHilbert m :=
  (((WithLp.linearEquiv 2 ℂ (Fock m)).symm.toLinearMap).comp
    (action.comp (WithLp.linearEquiv 2 ℂ (Fock m)).toLinearMap)).toContinuousLinearMap

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Fintype ι]

def testFockRead (prepared : E) (tests : ι → E) : E →L[ℂ] FockHilbert (Modes prepared tests) :=
  oneParticleHilbert.toContinuousLinearMap.comp
    ((stdOrthonormalBasis ℂ (carrier prepared tests)).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (carrier prepared tests).orthogonalProjectionOnto)

omit [CompleteSpace E] in
theorem testFockRead_family (prepared : E) (tests : ι → E) (i : Option ι) :
    testFockRead prepared tests (family prepared tests i)=
      WithLp.toLp 2 (oneParticle (coordinates prepared tests i)) := by
  have fixed := (carrier prepared tests).orthogonalProjectionOnto_mem_subspace_eq_self (member prepared tests i)
  change (carrier prepared tests).orthogonalProjectionOnto (family prepared tests i)=member prepared tests i at fixed
  change oneParticleHilbert
    ((stdOrthonormalBasis ℂ (carrier prepared tests)).repr
      ((carrier prepared tests).orthogonalProjectionOnto (family prepared tests i)))=_
  rw [fixed]
  rfl

def wordObservable (prepared : E) (tests : ι → E) (word : List (Letter (Option ι))) : E →L[ℂ] E :=
  (testFockRead prepared tests).adjoint.comp
    ((fockOperator (wordOperator (fun i => coordinates prepared tests i) word)).comp (testFockRead prepared tests))

theorem wordObservable_response (prepared : E) (tests : ι → E) (word : List (Letter (Option ι))) :
    inner ℂ prepared (wordObservable prepared tests word prepared)=spatialMoment prepared tests word := by
  change inner ℂ prepared ((testFockRead prepared tests).adjoint
    ((fockOperator (wordOperator (fun i => coordinates prepared tests i) word))
      (testFockRead prepared tests prepared)))=_
  rw [ContinuousLinearMap.adjoint_inner_right]
  have preparedRead := testFockRead_family prepared tests none
  change testFockRead prepared tests prepared=WithLp.toLp 2 (preparedFock prepared tests) at preparedRead
  rw [preparedRead]
  change inner ℂ (WithLp.toLp 2 (preparedFock prepared tests))
    (WithLp.toLp 2 (wordOperator (fun i => coordinates prepared tests i) word (preparedFock prepared tests)))=_
  exact (pairing_euclidean _ _).symm

theorem source_native_allWord (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (tests : ι → MatterL2) (word : List (Letter (Option ι))) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1
        (normalizedPreparationNative force continuousForce t
          (wordObservable (normalizedPreparation force continuousForce t) tests word))))=
      spatialMoment (normalizedPreparation force continuousForce t) tests word := by
  rw [normalizedPreparationNative_sourceResponse]
  exact wordObservable_response (normalizedPreparation force continuousForce t) tests word

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.SpatialCAR
