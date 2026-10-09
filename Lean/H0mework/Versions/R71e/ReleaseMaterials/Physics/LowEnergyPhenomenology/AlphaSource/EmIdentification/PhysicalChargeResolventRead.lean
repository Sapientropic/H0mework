import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalChargeResolvent
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ChargeResolventRead

/-! The increment vertex between physical resolvents at independent momenta.
The created composite legs carry increment charge -1, the proven field
increment of the original preparation; the Ward identity returns exactly
the two physical propagators' difference plus the complete torque. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalCharge
open GaussCoreHilbert GaussCoreDifferential SourceFamilyOperator CanonicalGradedCharge
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates CanonicalGradedSpatialSource
open CanonicalPhysicalSpatial CanonicalPhysicalResolvent
open GaussUnitaryHistory (HistorySpace Index sourceFilter reader inclusion)
open scoped InnerProductSpace Topology
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

/-- The increment vertex is the charge vertex of Q+1 between the two
physical resolvents: it subtracts the proven prepared charge -1. -/
def incrementVertex (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    HistorySpace →L[ℂ] HistorySpace :=
  vertex (Q+1) p k z w hz hw

private theorem one_vertex (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    vertex (1 : H →L[ℂ] H) p k z w hz hw=sourceResolvent (p+k) z hz*sourceResolvent p w hw := by
  simp only [vertex_return,GaussUnitaryHistory.reader_one,mul_one]

theorem increment_vertex_add (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) :
    incrementVertex Q p k z w hz hw=vertex Q p k z w hz hw+
      sourceResolvent (p+k) z hz*sourceResolvent p w hw := by
  calc incrementVertex Q p k z w hz hw=
        vertex Q p k z w hz hw+vertex (1 : H →L[ℂ] H) p k z w hz hw :=
      vertex_add Q 1 p k z w hz hw
    _ = vertex Q p k z w hz hw+sourceResolvent (p+k) z hz*sourceResolvent p w hw :=
      congrArg (vertex Q p k z w hz hw+·) (one_vertex p k z w hz hw)

theorem increment_vertex_original (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    incrementVertex (chargeReader nativeY) 0 0 z w hz hw=ChargeResolvent.incrementVertex z w hz hw := by
  rw [increment_vertex_add,vertex_original_ward]
  simp only [add_zero,resolvent_original]
  rfl

theorem increment_ward (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) :
    (z-w) • incrementVertex Q p k z w hz hw=
      sourceResolvent (p+k) z hz*reader (Q+1)-reader (Q+1)*sourceResolvent p w hw+
        torque (Q+1) p k z w hz hw :=
  physical_charge_ward (Q+1) p k z w hz hw

/-- The increment torque splits as the charge torque plus the actual
momentum-transfer difference of the two physical compressions. -/
theorem increment_torque_split (Q : H →L[ℂ] H) (p k : PhysicalMomentum) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) :
    torque (Q+1) p k z w hz hw=torque Q p k z w hz hw+torque (1 : H →L[ℂ] H) p k z w hz hw :=
  torque_add Q 1 p k z w hz hw

theorem increment_torque_original (a : NativeLie) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    torque (chargeReader a+1) 0 0 z w hz hw=ChargeResolvent.torque a z w hz hw := by
  rw [increment_torque_split,torque_original]
  have unit : torque (1 : H →L[ℂ] H) 0 0 z w hz hw=0 := by
    have e : torque (1 : H →L[ℂ] H) 0 0 z w hz hw=
        lift sourceFilter (constant (0 : H →L[ℂ] H)) :=
      lift_congr sourceFilter _ _ fun F => by
        show finiteTorque (1 : H →L[ℂ] H) 0 0 z w F=0
        simp only [finiteTorque,add_zero,mul_one,one_mul,sub_self,mul_zero,zero_mul]
    rw [e,lift_zero]
  rw [unit,add_zero]

/-- The proven field increment: on an actual created leg the increment
charge Q_Y+1 returns -1 at every physical momentum. -/
theorem created_increment_charge (channel spin : Fin 2) (f : QuantumTest)
    (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) :
    reader (chargeReader nativeY+1) (inclusion (creationSource channel spin f))=
      (-1 : ℂ) • inclusion (creationSource channel spin f) := by
  rw [GaussUnitaryHistory.reader_add]
  simp only [add_apply,GaussUnitaryHistory.reader_one,one_apply_eq_self]
  rw [ChargeResolvent.created_history_charge channel spin f profile sameSource]
  module

theorem history_increment_pair (a : NativeLie) (x y : HistorySpace) :
    inner ℂ (reader (chargeReader a+1) x) y=inner ℂ x (reader (chargeReader a+1) y) := by
  rw [GaussUnitaryHistory.reader_add]
  simp only [add_apply,inner_add_left,inner_add_right,GaussUnitaryHistory.reader_one,
    one_apply_eq_self]
  rw [ChargeResolvent.history_charge_pair]

def createdPhysicalTwoPoint (a s b t : Fin 2) (q : PhysicalMomentum) (z : ℂ) (hz : z.im≠0)
    (f g : QuantumTest) : ℂ :=
  inner ℂ (inclusion (creationSource a s f)) (sourceResolvent q z hz (inclusion (creationSource b t g)))

/-- The source-relative vertex Ward identity at physical momentum transfer
k: the increment charge of the created composite legs is -1, so the
(z-w)-scaled increment vertex returns the difference of the two physical
propagators plus the complete increment torque. -/
theorem source_relative_physical_vertex_ward (a s b t : Fin 2) (p k : PhysicalMomentum)
    (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (f g : QuantumTest)
    (leftProfile rightProfile : SourceCoordinateSlice → ℂ)
    (leftSource : ∀ u, f u=leftProfile u • CanonicalCompletedSector.seed)
    (rightSource : ∀ u, g u=rightProfile u • CanonicalCompletedSector.seed) :
    (z-w)*inner ℂ (inclusion (creationSource a s f))
      (incrementVertex (chargeReader nativeY) p k z w hz hw
        (inclusion (creationSource b t g))) =
    -(createdPhysicalTwoPoint a s b t (p+k) z hz f g-
      createdPhysicalTwoPoint a s b t p w hw f g)+
      inner ℂ (inclusion (creationSource a s f))
        (torque (chargeReader nativeY+1) p k z w hz hw
          (inclusion (creationSource b t g))) := by
  let x := inclusion (creationSource a s f)
  let y := inclusion (creationSource b t g)
  have hx := created_increment_charge a s f leftProfile leftSource
  have hy := created_increment_charge b t g rightProfile rightSource
  change reader (chargeReader nativeY+1) x=(-1 : ℂ)•x at hx
  change reader (chargeReader nativeY+1) y=(-1 : ℂ)•y at hy
  have ward := congrArg (fun T : HistorySpace →L[ℂ] HistorySpace => inner ℂ x (T y))
    (increment_ward (chargeReader nativeY) p k z w hz hw)
  simp only [smul_apply,sub_apply,add_apply,mul_apply_eq_comp,inner_smul_right,inner_sub_right,
    inner_add_right,hy,map_smul] at ward
  rw [←history_increment_pair nativeY x (sourceResolvent p w hw y),hx,inner_smul_left] at ward
  simp only [map_neg,map_one,neg_one_mul] at ward
  simp only [createdPhysicalTwoPoint]
  linear_combination ward

end LowEnergy.GaussComposite.PhysicalCharge
