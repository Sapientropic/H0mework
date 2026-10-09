import PhysicalChargeResolventRead
import CanonicalPreparedGraph

/-! The increment vertex on the actual prepared legs. On the original
same-source kernel section a created completed leg carries increment
charge -1 and an annihilated completed leg carries +1; density of the
scalar-Gram core transports the identity to every profile. The
(z-w)-scaled increment vertex between physical resolvents then returns
the signed difference of the two actual-leg propagators plus the
complete increment torque. No configuration amplitude is selected and
no pole or electromagnetic direction is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalCharge
open GaussCoreHilbert GaussCoreDifferential SourceFamilyOperator CanonicalGradedCharge
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates CanonicalGradedSpatialSource
open CanonicalPhysicalSpatial CanonicalPhysicalResolvent
open GaussDensityCore (ScalarTest)
open GaussComposite.SourceGraph
open GaussUnitaryHistory (HistorySpace Index sourceFilter reader inclusion)
open scoped InnerProductSpace Topology
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

/-- The proven sign of the field increment: a created letter lowers the
charge by one unit, an annihilated letter raises it by one unit. -/
def incrementSign (addition : Bool) : ℂ := if addition then (-1 : ℂ) else (1 : ℂ)

@[simp] theorem incrementSign_true : incrementSign true=(-1 : ℂ) := rfl
@[simp] theorem incrementSign_false : incrementSign false=(1 : ℂ) := rfl

theorem star_incrementSign (addition : Bool) : star (incrementSign addition)=incrementSign addition := by
  cases addition <;> simp [incrementSign]

private theorem leg_false (a s : Fin 2) : leg false a s=annihilationSource a s := rfl
private theorem leg_true (a s : Fin 2) : leg true a s=creationSource a s := rfl

/-- A core profile's completed creation leg is the original creation
source on the same-source kernel section. -/
private theorem completed_leg_bridge (addition : Bool) (a s : Fin 2) (f : ScalarTest) :
    completedLeg addition a s (core f)=leg addition a s (seedSection f) :=
  completedLeg_core addition a s f

private theorem created_bridge (a s : Fin 2) (f : ScalarTest) :
    completedLeg true a s (core f)=creationSource a s (seedSection f) :=
  (completed_leg_bridge true a s f).trans
    (congrArg (fun T : QuantumTest →ₗ[ℂ] H => T (seedSection f)) (leg_true a s))

private theorem annihilated_bridge (a s : Fin 2) (f : ScalarTest) :
    completedLeg false a s (core f)=annihilationSource a s (seedSection f) :=
  (completed_leg_bridge false a s f).trans
    (congrArg (fun T : QuantumTest →ₗ[ℂ] H => T (seedSection f)) (leg_false a s))

/-- The annihilation of the proven single-charge seed returns a neutral
configuration test: the +1 field increment cancels the prepared -1. -/
theorem annihilation_core_charge (channel spin : Fin 2) (f : QuantumTest)
    (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) :
    chargeAction nativeY (annihilationTest channel spin f)=0 := by
  have h := annihilation_charge_core channel spin f
  change chargeAction nativeY (annihilationTest channel spin f)-
    annihilationTest channel spin (chargeAction nativeY f)=
      annihilationTest channel spin f at h
  rw [source_section_charge f profile sameSource] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h,map_neg,add_neg_cancel]

theorem annihilation_reader_charge (channel spin : Fin 2) (f : QuantumTest)
    (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) :
    chargeReader nativeY (annihilationSource channel spin f)=0 := by
  rw [←embed_annihilation_test,chargeReader_core,
    annihilation_core_charge channel spin f profile sameSource,map_zero]

theorem annihilation_history_charge (channel spin : Fin 2) (f : QuantumTest)
    (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) :
    reader (chargeReader nativeY) (inclusion (annihilationSource channel spin f))=0 := by
  rw [GaussUnitaryHistory.reader_inclusion,
    annihilation_reader_charge channel spin f profile sameSource,map_zero]

/-- On the same-source kernel section a created completed leg carries
increment charge -1. -/
theorem created_prepared_increment (a s : Fin 2) (f : ScalarTest) :
    reader (chargeReader nativeY+1) (inclusion (completedLeg true a s (core f)))=
      (-1 : ℂ)•inclusion (completedLeg true a s (core f)) := by
  rw [created_bridge]
  exact created_increment_charge a s (seedSection f) _ (seedSection_apply f)

/-- On the same-source kernel section an annihilated completed leg
carries increment charge +1: it is neutral before the unit increment. -/
theorem annihilated_prepared_increment (a s : Fin 2) (f : ScalarTest) :
    reader (chargeReader nativeY+1) (inclusion (completedLeg false a s (core f)))=
      (1 : ℂ)•inclusion (completedLeg false a s (core f)) := by
  rw [annihilated_bridge]
  have zero := annihilation_history_charge a s (seedSection f) _ (seedSection_apply f)
  rw [GaussUnitaryHistory.reader_add]
  simp only [add_apply,GaussUnitaryHistory.reader_one,one_apply_eq_self]
  rw [zero,zero_add,one_smul]

/-- On the same-source kernel section the completed leg carries the
signed field increment of its letter. -/
theorem leg_increment_core (addition : Bool) (a s : Fin 2) (f : ScalarTest) :
    reader (chargeReader nativeY+1) (inclusion (completedLeg addition a s (core f)))=
      incrementSign addition•inclusion (completedLeg addition a s (core f)) := by
  cases addition with
  | false => exact (annihilated_prepared_increment a s f)
  | true => exact (created_prepared_increment a s f)

/-- The increment eigenspaces are closed, so the same-source identity
extends from the dense scalar-Gram core to every profile. -/
theorem prepared_leg_increment (addition : Bool) (a s : Fin 2) (f : Profile) :
    reader (chargeReader nativeY+1) (inclusion (completedLeg addition a s f))=
      incrementSign addition•inclusion (completedLeg addition a s f) := by
  let S : Set Profile := {f | reader (chargeReader nativeY+1)
      (inclusion (completedLeg addition a s f))=
        incrementSign addition•inclusion (completedLeg addition a s f)}
  have legC : Continuous fun f : Profile =>
      inclusion (completedLeg addition a s f) :=
    inclusion.continuous.comp (completedLeg addition a s).cont
  have eigC : Continuous fun f : Profile => reader (chargeReader nativeY+1)
      (inclusion (completedLeg addition a s f)) :=
    (reader (chargeReader nativeY+1)).cont.comp legC
  have closed : IsClosed S := isClosed_eq eigC (legC.const_smul (incrementSign addition))
  have covers : Set.univ ⊆ S := by
    rw [← Dense.closure_eq core_dense]
    apply closure_minimal _ closed
    rintro _ ⟨g, rfl⟩
    exact leg_increment_core addition a s g
  exact covers (Set.mem_univ f)

/-- The physical propagator between two actual prepared legs at momentum
q and resolvent point z. -/
def preparedTwoPoint (left right : Bool) (a s b t : Fin 2) (q : PhysicalMomentum)
    (z : ℂ) (hz : z.im≠0) (f g : Profile) : ℂ :=
  inner ℂ (inclusion (completedLeg left a s f))
    (sourceResolvent q z hz (inclusion (completedLeg right b t g)))

theorem preparedTwoPoint_bound (left right : Bool) (a s b t : Fin 2) (q : PhysicalMomentum)
    (z : ℂ) (hz : z.im≠0) (f g : Profile) :
    ‖preparedTwoPoint left right a s b t q z hz f g‖≤
      legBound*‖f‖*((1/|z.im|)*(legBound*‖g‖)) := by
  have inv_nonneg : 0≤1/|z.im| := one_div_nonneg.mpr (abs_nonneg _)
  have vn : ‖inclusion (completedLeg right b t g)‖≤legBound*‖g‖ := by
    rw [inclusion.norm_map]
    exact completedLeg_bound right b t g
  have right_bound : ‖sourceResolvent q z hz (inclusion (completedLeg right b t g))‖≤
      (1/|z.im|)*(legBound*‖g‖) :=
    (resolvent_bound q z hz _).trans (mul_le_mul_of_nonneg_left vn inv_nonneg)
  calc
    ‖inner ℂ (inclusion (completedLeg left a s f))
      (sourceResolvent q z hz (inclusion (completedLeg right b t g)))‖
      ≤ ‖inclusion (completedLeg left a s f)‖*
        ‖sourceResolvent q z hz (inclusion (completedLeg right b t g))‖ :=
      norm_inner_le_norm (𝕜 := ℂ) _ _
    _ = ‖completedLeg left a s f‖*
        ‖sourceResolvent q z hz (inclusion (completedLeg right b t g))‖ := by
      rw [inclusion.norm_map]
    _ ≤ ‖completedLeg left a s f‖*((1/|z.im|)*(legBound*‖g‖)) :=
      mul_le_mul_of_nonneg_left right_bound (norm_nonneg _)
    _ ≤ legBound*‖f‖*((1/|z.im|)*(legBound*‖g‖)) :=
      mul_le_mul_of_nonneg_right (completedLeg_bound left a s f)
        (mul_nonneg inv_nonneg (mul_nonneg legBound_nonnegative (norm_nonneg _)))

/-- The inner-product algebra of the signed increment Ward identity.
Rewrites against `⟪·,·⟫` on the completed history space only through
`simp only`: `rw` rechecks the large `Completion`-carrier instances. -/
private theorem increment_wedge
    (Ro Ri QP T : HistorySpace →L[ℂ] HistorySpace) (d σR σL : ℂ)
    (x y : HistorySpace)
    (h : d • (Ro*QP*Ri)=Ro*QP-QP*Ri+T)
    (hR : QP y=σR • y) (hL : QP x=σL • x)
    (pair : ∀ u v : HistorySpace, inner ℂ u (QP v)=inner ℂ (QP u) v)
    (hsL : (starRingEnd ℂ) σL=σL) :
    d*inner ℂ x (Ro (QP (Ri y)))=σR*inner ℂ x (Ro y)-σL*inner ℂ x (Ri y)+inner ℂ x (T y) := by
  have applied := congrArg (fun A : HistorySpace →L[ℂ] HistorySpace => inner ℂ x (A y)) h
  simp only [sub_eq_add_neg,smul_apply,add_apply,neg_apply,mul_apply_eq_comp,
    inner_smul_right,inner_add_right,inner_neg_right] at applied
  simp only [hR,map_smul,inner_smul_right,pair,hL,inner_smul_left,hsL] at applied
  linear_combination applied

/-- The signed increment Ward identity between actual prepared legs at
independent physical momenta: the (z-w)-scaled increment vertex returns
the signed difference of the two actual-leg propagators plus the
complete increment torque. -/
theorem prepared_increment_ward (left right : Bool) (a s b t : Fin 2)
    (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (f g : Profile) :
    (z-w)*inner ℂ (inclusion (completedLeg left a s f))
      (incrementVertex (chargeReader nativeY) p k z w hz hw
        (inclusion (completedLeg right b t g))) =
    incrementSign right*preparedTwoPoint left right a s b t (p+k) z hz f g-
      incrementSign left*preparedTwoPoint left right a s b t p w hw f g+
      inner ℂ (inclusion (completedLeg left a s f))
        (torque (chargeReader nativeY+1) p k z w hz hw
          (inclusion (completedLeg right b t g))) := by
  have product : incrementVertex (chargeReader nativeY) p k z w hz hw=
      sourceResolvent (p+k) z hz*reader (chargeReader nativeY+1)*
        sourceResolvent p w hw :=
    vertex_return (chargeReader nativeY+1) p k z w hz hw
  have hward : (z-w)•(sourceResolvent (p+k) z hz*reader (chargeReader nativeY+1)*
      sourceResolvent p w hw)=
      sourceResolvent (p+k) z hz*reader (chargeReader nativeY+1)-
        reader (chargeReader nativeY+1)*sourceResolvent p w hw+
          torque (chargeReader nativeY+1) p k z w hz hw := by
    rw [←product]
    exact increment_ward (chargeReader nativeY) p k z w hz hw
  have sc : (starRingEnd ℂ) (incrementSign left)=incrementSign left := by
    rw [starRingEnd_apply]
    exact star_incrementSign left
  have base := increment_wedge (sourceResolvent (p+k) z hz) (sourceResolvent p w hw)
    (reader (chargeReader nativeY+1)) (torque (chargeReader nativeY+1) p k z w hz hw)
    (z-w) (incrementSign right) (incrementSign left)
    (inclusion (completedLeg left a s f)) (inclusion (completedLeg right b t g))
    hward (prepared_leg_increment right b t g) (prepared_leg_increment left a s f)
    (fun u v => (history_increment_pair nativeY u v).symm) sc
  simp only [preparedTwoPoint,product,mul_apply_eq_comp]
  linear_combination base

theorem prepared_increment_ward_created (a s b t : Fin 2) (p k : PhysicalMomentum)
    (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (f g : Profile) :
    (z-w)*inner ℂ (inclusion (completedLeg true a s f))
      (incrementVertex (chargeReader nativeY) p k z w hz hw
        (inclusion (completedLeg true b t g))) =
    -(preparedTwoPoint true true a s b t (p+k) z hz f g-
      preparedTwoPoint true true a s b t p w hw f g)+
      inner ℂ (inclusion (completedLeg true a s f))
        (torque (chargeReader nativeY+1) p k z w hz hw
          (inclusion (completedLeg true b t g))) := by
  have h := prepared_increment_ward true true a s b t p k z w hz hw f g
  simp only [incrementSign_true] at h
  linear_combination h

theorem prepared_increment_ward_annihilated (a s b t : Fin 2) (p k : PhysicalMomentum)
    (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (f g : Profile) :
    (z-w)*inner ℂ (inclusion (completedLeg false a s f))
      (incrementVertex (chargeReader nativeY) p k z w hz hw
        (inclusion (completedLeg false b t g))) =
    preparedTwoPoint false false a s b t (p+k) z hz f g-
      preparedTwoPoint false false a s b t p w hw f g+
      inner ℂ (inclusion (completedLeg false a s f))
        (torque (chargeReader nativeY+1) p k z w hz hw
          (inclusion (completedLeg false b t g))) := by
  have h := prepared_increment_ward false false a s b t p k z w hz hw f g
  simp only [incrementSign_false] at h
  linear_combination h

theorem prepared_increment_bound (left right : Bool) (a s b t : Fin 2)
    (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (f g : Profile) :
    ‖inner ℂ (inclusion (completedLeg left a s f))
      (incrementVertex (chargeReader nativeY) p k z w hz hw
        (inclusion (completedLeg right b t g)))‖≤
      legBound*‖f‖*(‖chargeReader nativeY+1‖*(1/|z.im|)*(1/|w.im|)*(legBound*‖g‖)) := by
  have inv (u : ℂ) : 0≤1/|u.im| := one_div_nonneg.mpr (abs_nonneg _)
  have vn : ‖inclusion (completedLeg right b t g)‖≤legBound*‖g‖ := by
    rw [inclusion.norm_map]
    exact completedLeg_bound right b t g
  have pref : 0≤‖chargeReader nativeY+1‖*(1/|z.im|)*(1/|w.im|) :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (inv z)) (inv w)
  have inner_bound : ‖incrementVertex (chargeReader nativeY) p k z w hz hw
      (inclusion (completedLeg right b t g))‖≤
      ‖chargeReader nativeY+1‖*(1/|z.im|)*(1/|w.im|)*(legBound*‖g‖) :=
    (vertex_bound (chargeReader nativeY+1) p k z w hz hw _).trans
      (mul_le_mul_of_nonneg_left vn pref)
  calc
    ‖inner ℂ (inclusion (completedLeg left a s f))
      (incrementVertex (chargeReader nativeY) p k z w hz hw
        (inclusion (completedLeg right b t g)))‖
      ≤ ‖inclusion (completedLeg left a s f)‖*
        ‖incrementVertex (chargeReader nativeY) p k z w hz hw
          (inclusion (completedLeg right b t g))‖ :=
      norm_inner_le_norm (𝕜 := ℂ) _ _
    _ = ‖completedLeg left a s f‖*
        ‖incrementVertex (chargeReader nativeY) p k z w hz hw
          (inclusion (completedLeg right b t g))‖ := by
      rw [inclusion.norm_map]
    _ ≤ ‖completedLeg left a s f‖*
        (‖chargeReader nativeY+1‖*(1/|z.im|)*(1/|w.im|)*(legBound*‖g‖)) :=
      mul_le_mul_of_nonneg_left inner_bound (norm_nonneg _)
    _ ≤ legBound*‖f‖*(‖chargeReader nativeY+1‖*(1/|z.im|)*(1/|w.im|)*(legBound*‖g‖)) :=
      mul_le_mul_of_nonneg_right (completedLeg_bound left a s f)
        (mul_nonneg pref (mul_nonneg legBound_nonnegative (norm_nonneg _)))

/-- At zero momentum the prepared-leg propagator is exactly the signed
created two-point function of the kernel sections. -/
theorem preparedTwoPoint_original (a s b t : Fin 2) (z : ℂ) (hz : z.im≠0)
    (f g : ScalarTest) :
    preparedTwoPoint true true a s b t 0 z hz (core f) (core g)=
      ChargeResolvent.createdTwoPoint a s b t z hz (seedSection f) (seedSection g) := by
  have left : completedLeg true a s (core f)=creationSource a s (seedSection f) :=
    created_bridge a s f
  have right : completedLeg true b t (core g)=creationSource b t (seedSection g) :=
    created_bridge b t g
  unfold preparedTwoPoint ChargeResolvent.createdTwoPoint
  rw [congrArg inclusion left,congrArg inclusion right,resolvent_original]

/-- At zero momentum transfer the prepared increment Ward recovers the
signed source-relative vertex identity on the kernel sections. -/
theorem prepared_increment_ward_original (a s b t : Fin 2) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (f g : ScalarTest) :
    (z-w)*inner ℂ (inclusion (completedLeg true a s (core f)))
      (ChargeResolvent.incrementVertex z w hz hw
        (inclusion (completedLeg true b t (core g)))) =
    -(ChargeResolvent.createdTwoPoint a s b t z hz (seedSection f) (seedSection g)-
      ChargeResolvent.createdTwoPoint a s b t w hw (seedSection f) (seedSection g))+
      inner ℂ (inclusion (completedLeg true a s (core f)))
        (ChargeResolvent.torque nativeY z w hz hw
          (inclusion (completedLeg true b t (core g)))) := by
  rw [congrArg inclusion (created_bridge a s f),
    congrArg inclusion (created_bridge b t g)]
  exact ChargeResolvent.source_relative_vertex_ward a s b t z w hz hw
    (seedSection f) (seedSection g) (fun u => f u) (fun u => g u)
    (seedSection_apply f) (seedSection_apply g)

end LowEnergy.GaussComposite.PhysicalCharge
