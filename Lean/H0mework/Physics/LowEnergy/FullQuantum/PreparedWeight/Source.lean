import H0mework.Physics.LowEnergy.FullQuantum.PreparedWeight.Compression
import H0mework.Physics.LowEnergy.FullQuantum.PreparedWeight.Time
import H0mework.Physics.LowEnergyMatterSpace.SpatialCARNative

/-! The original prepared state supplies the determinant boundary weight and its full-word consumer. -/
set_option autoImplicit false
open scoped Matrix InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedWeight
open QuantizationCheck.Fermion ProofFreeRicherAnholonomicSource StageNineHolonomicField
noncomputable section
attribute [local instance] Fermion.fullIndexOrder
local instance : Fintype (Finset Quantum.Index) := Fintype.ofFinite _

theorem source_fock_boundary (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t angle : ℝ) :
    boundaryDeterminant (Quantum.coordinates (Quantum.preparedSpinor (1/2) angle)) (primalMatrix C p k t)=
      pairing (oneParticle (Quantum.coordinates (Quantum.preparedSpinor (1/2) angle)))
        (fockEvolution C p k t (oneParticle (Quantum.coordinates (Quantum.preparedSpinor (1/2) angle)))) := by
  have unit : Fermion.modePair (Quantum.coordinates (Quantum.preparedSpinor (1/2) angle))
      (Quantum.coordinates (Quantum.preparedSpinor (1/2) angle))=1 := Quantum.prepared_unit angle
  rw [boundaryDeterminant_pair _ _ unit,fockEvolution_oneParticle,pairing_oneParticle]
  rw [primalMatrix,Quantum.matrix_action]
  rfl

theorem source_original_pair (density amplitude angle : ℝ) (action : Mother) :
    Stage9C.Material.SpinPair.spinPairDual
        ((density : ℂ)*(amplitude : ℂ)*Quantum.phase angle)
        ((density : ℂ)*(amplitude : ℂ)*Quantum.phase (-angle))
        (action (Quantum.preparedSpinor amplitude angle))=
      ((4*density*amplitude^2 : ℝ) : ℂ)*
        boundaryDeterminant (Quantum.coordinates (Quantum.preparedSpinor (1/2) angle))
          (Quantum.operatorMatrix (Quantum.spinExchange.comp action)) := by
  rw [Quantum.prepared_response,boundaryDeterminant_pair _ _ (Quantum.prepared_unit angle)]
  rfl

open MatterSpace MatterSpace.SpatialCAR
variable {ι : Type*} [Fintype ι]

theorem spatial_word_boundary (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (tests : ι → MatterL2)
    (nonzero : spatialPreparation force continuousForce t≠0) (word : List (Letter (Option ι))) :
    boundaryDeterminant (coordinates (normalizedPreparation force continuousForce t) tests none)
      (wholeCompression (wordOperator (fun i => coordinates (normalizedPreparation force continuousForce t) tests i) word))=
      spatialMoment (normalizedPreparation force continuousForce t) tests word := by
  have unit := source_preparedFock_unit force continuousForce t tests nonzero
  rw [preparedFock,pairing_oneParticle] at unit
  exact boundaryDeterminant_whole_word _ _ unit

theorem original_Stage10_boundary (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (tests : ι → MatterL2)
    (nonzero : spatialPreparation force continuousForce t≠0) (word : List (Letter (Option ι))) :
    Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Stage9DEF.Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1
        (normalizedPreparationNative force continuousForce t
          (wordObservable (normalizedPreparation force continuousForce t) tests word))))=
      boundaryDeterminant (coordinates (normalizedPreparation force continuousForce t) tests none)
        (wholeCompression (wordOperator (fun i => coordinates (normalizedPreparation force continuousForce t) tests i) word)) := by
  rw [source_native_allWord,spatial_word_boundary force continuousForce t tests nonzero word]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedWeight
