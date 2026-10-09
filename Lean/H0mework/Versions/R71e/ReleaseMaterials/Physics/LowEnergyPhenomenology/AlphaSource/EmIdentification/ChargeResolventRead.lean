import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ChargeResolvent
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.PreparedCharge

/-! The original source charge at the prepared endpoints enters the same
two-energy propagator identity. The field increment subtracts the proven
prepared charge and retains the actual completion torque. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ChargeResolvent
open GaussCoreHilbert GaussCoreDifferential SourceFamilyOperator CanonicalGradedCharge
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open FullYSourceResolventGraphSplice
open GaussUnitaryHistory (HistorySpace Index sourceFilter reader inclusion)
open scoped InnerProductSpace Topology
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

theorem created_reader_charge (channel spin : Fin 2) (f : QuantumTest)
    (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) :
    chargeReader nativeY (creationSource channel spin f)=(-2 : ℂ) • creationSource channel spin f := by
  rw [←embed_creation_test,chargeReader_core,created_core_charge channel spin f profile sameSource,
    map_smul,embed_creation_test]

theorem created_history_charge (channel spin : Fin 2) (f : QuantumTest)
    (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) :
    reader (chargeReader nativeY) (inclusion (creationSource channel spin f))=
      (-2 : ℂ) • inclusion (creationSource channel spin f) := by
  rw [GaussUnitaryHistory.reader_inclusion,created_reader_charge channel spin f profile sameSource,map_smul]

theorem history_charge_pair (a : NativeLie) (x y : HistorySpace) :
    inner ℂ (reader (chargeReader a) x) y=inner ℂ x (reader (chargeReader a) y) := by
  apply lift_pair sourceFilter (constant (chargeReader a)) (constant (chargeReader a))
  intro F u v
  exact (CanonicalGradedGaugeVariation.gaugeReader_selfAdjoint GaussHistoryHilbert.sourcePoint .temporal a).isSymmetric u v

theorem same_resolvent_identity (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    (z-w) • (sameResolvent z hz*sameResolvent w hw)=sameResolvent z hz-sameResolvent w hw := by
  let P := comp (constant ((z-w) • (1 : H →L[ℂ] H)))
    (comp (resolventFamily z hz) (resolventFamily w hw))
  let Q := add (resolventFamily z hz)
    (comp (constant ((-1 : ℂ) • (1 : H →L[ℂ] H))) (resolventFamily w hw))
  have eq (F : Index) : P.component F=Q.component F := by
    have h := finite_torque_identity (GaussGradedCompression.compression F) (1 : H →L[ℂ] H)
      (GaussGradedCompression.compression_selfAdjoint F) z w hz hw
    simp only [mul_one,one_mul,sub_self,mul_zero,zero_mul] at h
    have inverse : (z-w) • (finiteResolvent F z*finiteResolvent F w)=finiteResolvent F z-finiteResolvent F w := by
      simpa only [finiteResolvent,neg_sub] using eq_neg_of_add_eq_zero_right h.symm
    change ((z-w) • (1 : H →L[ℂ] H))*(finiteResolvent F z*finiteResolvent F w)=
      finiteResolvent F z+((-1 : ℂ) • (1 : H →L[ℂ] H))*finiteResolvent F w
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg (fun T : H →L[ℂ] H => T x) inverse
    simpa only [smul_apply,mul_apply_eq_comp,one_apply_eq_self,add_apply,sub_apply,neg_apply,
      neg_one_smul,sub_eq_add_neg] using hx
  have h := lift_congr sourceFilter P Q eq
  simp only [P,Q,lift_comp,lift_add,constant_smul,lift_identity] at h
  change ((z-w) • (1 : HistorySpace →L[ℂ] HistorySpace))*(sameResolvent z hz*sameResolvent w hw)=
    sameResolvent z hz+((-1 : ℂ) • (1 : HistorySpace →L[ℂ] HistorySpace))*sameResolvent w hw at h
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun T : HistorySpace →L[ℂ] HistorySpace => T x) h
  simpa only [smul_apply,mul_apply_eq_comp,one_apply_eq_self,add_apply,sub_apply,neg_apply,
    neg_one_smul,sub_eq_add_neg] using hx

/-- The subtracted number is the proven charge of the unchanged source seed. -/
def incrementVertex (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) : HistorySpace →L[ℂ] HistorySpace :=
  vertex nativeY z w hz hw+sameResolvent z hz*sameResolvent w hw

def createdTwoPoint (a s b t : Fin 2) (z : ℂ) (hz : z.im≠0) (f g : QuantumTest) : ℂ :=
  inner ℂ (inclusion (creationSource a s f)) (sameResolvent z hz (inclusion (creationSource b t g)))

theorem source_relative_vertex_ward (a s b t : Fin 2) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (f g : QuantumTest) (leftProfile rightProfile : SourceCoordinateSlice → ℂ)
    (leftSource : ∀ u, f u=leftProfile u • CanonicalCompletedSector.seed)
    (rightSource : ∀ u, g u=rightProfile u • CanonicalCompletedSector.seed) :
    (z-w)*inner ℂ (inclusion (creationSource a s f))
      (incrementVertex z w hz hw (inclusion (creationSource b t g))) =
    -(createdTwoPoint a s b t z hz f g-createdTwoPoint a s b t w hw f g)+
      inner ℂ (inclusion (creationSource a s f))
        (torque nativeY z w hz hw (inclusion (creationSource b t g))) := by
  let x := inclusion (creationSource a s f)
  let y := inclusion (creationSource b t g)
  have hx := created_history_charge a s f leftProfile leftSource
  have hy := created_history_charge b t g rightProfile rightSource
  have ward := congrArg (fun T : HistorySpace →L[ℂ] HistorySpace => inner ℂ x (T y))
    (same_source_charge_ward nativeY z w hz hw)
  have inverse := congrArg (fun T : HistorySpace →L[ℂ] HistorySpace => inner ℂ x (T y))
    (same_resolvent_identity z w hz hw)
  change reader (chargeReader nativeY) x=(-2 : ℂ) • x at hx
  change reader (chargeReader nativeY) y=(-2 : ℂ) • y at hy
  simp only [smul_apply,add_apply,sub_apply,mul_apply_eq_comp,inner_smul_right,inner_add_right,
    inner_sub_right,hy,map_smul] at ward inverse
  rw [←history_charge_pair nativeY x (sameResolvent w hw y),hx,inner_smul_left] at ward
  change (z-w)*inner ℂ x ((vertex nativeY z w hz hw+sameResolvent z hz*sameResolvent w hw) y) = _
  simp only [add_apply,mul_apply_eq_comp,inner_add_right,createdTwoPoint]
  change (z-w)*(inner ℂ x (vertex nativeY z w hz hw y)+inner ℂ x (sameResolvent z hz (sameResolvent w hw y))) =
    -(inner ℂ x (sameResolvent z hz y)-inner ℂ x (sameResolvent w hw y))+
      inner ℂ x (torque nativeY z w hz hw y)
  simp only [map_neg,map_ofNat] at ward
  linear_combination ward+inverse

end LowEnergy.GaussComposite.ChargeResolvent
