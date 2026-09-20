import H0mework.Physics.LowEnergyMatterSpace.PreparationState
import H0mework.Physics.LowEnergyMatterSpace.DualPairing
import H0mework.Physics.YangMillsFlatQuantum.PairingResponse

/-! A source-generated spatial response is evaluated by the original Stage10 quantum consumer.
The complete matter operator is formed before the original eight-coordinate readout. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open DiracCliffordRepresentation DiracExteriorMatterAction ActiveSector
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open Stage9C.Material.SpinPair Stage9DEF
noncomputable section

def tripletBasisRead : DiracExteriorMatterCarrier →ₗ[ℂ] (SourceIndex → ℂ) where
  toFun matter index :=
    (su7ExteriorBasis 2).coord (colorTripletIndex index.2) (matter index.1).2.1
  map_add' first second := by
    funext index
    exact map_add _ _ _
  map_smul' scalar matter := by
    funext index
    exact map_smul _ _ _

def tripletFiberLift : MatterFiber →ₗ[ℂ] DiracExteriorMatterCarrier :=
  tripletLift.comp (WithLp.linearEquiv 2 ℂ (SourceIndex → ℂ)).toLinearMap

def tripletFiberRead : DiracExteriorMatterCarrier →ₗ[ℂ] MatterFiber :=
  (WithLp.linearEquiv 2 ℂ (SourceIndex → ℂ)).symm.toLinearMap.comp tripletBasisRead

theorem tripletFiberRead_lift (u : MatterFiber) :
    tripletFiberRead (tripletFiberLift u)=u := by
  ext index
  exact tripletLift_coordinate u index.1 index.2

def nativeMother (action : MatterFiber →L[ℂ] MatterFiber) : YangMills.FullPairing.Mother :=
  tripletFiberLift.comp (action.toLinearMap.comp tripletFiberRead)

theorem nativeMother_lift (action : MatterFiber →L[ℂ] MatterFiber) (u : MatterFiber) :
    nativeMother action (tripletFiberLift u)=tripletFiberLift (action u) := by
  change tripletFiberLift (action (tripletFiberRead (tripletFiberLift u)))=_
  rw [tripletFiberRead_lift]

theorem tripletFiberLift_pair (u v : MatterFiber) :
    inner ℂ (YangMills.FullPairing.naturalCoordinates (tripletFiberLift u))
      (YangMills.FullPairing.naturalCoordinates (tripletFiberLift v))=inner ℂ u v := by
  rw [YangMills.FullPairing.natural_inner,← Quantum.coordinatePair_full]
  exact triplet_euclidean_pair u v

theorem original_prepared_triplet :
    YangMills.FullPairing.prepared 0=
      YangMills.FullPairing.naturalCoordinates (tripletFiberLift sourcePrepared) := by
  have same := YangMills.FullPairing.actual_eq_twice_prepared 0
  rw [sourcePrepared_actual_origin,map_smul] at same
  change (2 : ℂ) • YangMills.FullPairing.naturalCoordinates (tripletFiberLift sourcePrepared)=
    (2 : ℂ) • YangMills.FullPairing.prepared 0 at same
  have cancel := congrArg (fun v : YangMills.FullPairing.Hilbert => ((2 : ℂ)⁻¹) • v) same
  simpa only [smul_smul,inv_mul_cancel₀ (by norm_num : (2 : ℂ)≠0),one_smul] using cancel.symm

theorem nativeMother_source_gram (action : MatterFiber →L[ℂ] MatterFiber) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1 (nativeMother action)))=
        inner ℂ sourcePrepared (action sourcePrepared) := by
  rw [YangMills.FullPairing.source_gram,original_prepared_triplet,
    YangMills.FullPairing.operator_coordinates,YangMills.FullPairing.operator_coordinates]
  change inner ℂ (YangMills.FullPairing.naturalCoordinates (tripletFiberLift sourcePrepared))
    (YangMills.FullPairing.naturalCoordinates (nativeMother action (tripletFiberLift sourcePrepared)))=_
  rw [nativeMother_lift,tripletFiberLift_pair]

def preparationPullback (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (action : MatterL2 →L[ℂ] MatterL2) :
    MatterFiber →L[ℂ] MatterFiber :=
  (preparationMap force continuousForce t).adjoint.comp
    (action.comp (preparationMap force continuousForce t))

def preparationNative (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (action : MatterL2 →L[ℂ] MatterL2) :
    YangMills.FullPairing.Mother :=
  nativeMother (preparationPullback force continuousForce t action)

theorem preparationNative_lift (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (action : MatterL2 →L[ℂ] MatterL2) (u : MatterFiber) :
    preparationNative force continuousForce t action (tripletFiberLift u)=
      tripletFiberLift ((preparationMap force continuousForce t).adjoint
        (action (preparationMap force continuousForce t u))) :=
  nativeMother_lift _ u

theorem preparationNative_sourceResponse (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (action : MatterL2 →L[ℂ] MatterL2) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1
        (preparationNative force continuousForce t action)))=
      spatialResponse force continuousForce t action := by
  rw [preparationNative,nativeMother_source_gram,spatialResponse_source_pullback]
  rfl

theorem preparationNative_original_dual (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (action : MatterL2 →L[ℂ] MatterL2) :
    actual.conjugateMatter 0 (YangMills.FullPairing.pairedMother 1
      (preparationNative force continuousForce t action) (actual.matter 0))=
      4*(spinScale : ℂ)*spatialResponse force continuousForce t action := by
  rw [YangMills.FullPairing.dual_gram,← YangMills.FullPairing.source_gram,
    preparationNative_sourceResponse]

def normalizedPreparationNative (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (action : MatterL2 →L[ℂ] MatterL2) :
    YangMills.FullPairing.Mother :=
  preparationNative force continuousForce t
    ((((‖spatialPreparation force continuousForce t‖⁻¹ : ℝ) : ℂ)^2) • action)

theorem normalizedPreparationNative_sourceResponse (force : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousForce : Continuous force) (t : ℝ) (action : MatterL2 →L[ℂ] MatterL2) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1
        (normalizedPreparationNative force continuousForce t action)))=
      normalizedFunctional force continuousForce t action := by
  have scaled (v : MatterL2) (c : ℝ) :
      inner ℂ v (((c : ℂ)^2 • action) v)=inner ℂ ((c : ℂ) • v) (action ((c : ℂ) • v)) := by
    change inner ℂ v ((c : ℂ)^2 • action v)=_
    rw [inner_smul_right,map_smul,inner_smul_left,inner_smul_right]
    simp only [Complex.conj_ofReal]
    ring
  rw [normalizedPreparationNative,preparationNative_sourceResponse]
  change inner ℂ (spatialPreparation force continuousForce t)
    (((((‖spatialPreparation force continuousForce t‖⁻¹ : ℝ) : ℂ)^2) • action)
      (spatialPreparation force continuousForce t))=
    inner ℂ (((‖spatialPreparation force continuousForce t‖⁻¹ : ℝ) : ℂ) •
      spatialPreparation force continuousForce t)
      (action (((‖spatialPreparation force continuousForce t‖⁻¹ : ℝ) : ℂ) •
        spatialPreparation force continuousForce t))
  exact scaled _ _

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
