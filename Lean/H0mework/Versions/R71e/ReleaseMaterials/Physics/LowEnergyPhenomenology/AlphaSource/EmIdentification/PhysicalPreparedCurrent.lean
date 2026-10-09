import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalPreparedCharge
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPhysicalWardEndpoints
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalRadialRead

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-!
# Electromagnetic channel vertex on actual prepared legs

The electromagnetic channel candidate is the source-generated spatial
current: `CanonicalPhysicalWardCore.currentAction k a` is the
unlocalized `k·J` contribution inside the physical Ward decomposition,
and `CanonicalGradedCharge.currentReader phi k a` is its bounded
localized reader on the completed history. This module places the
current vertex between the two physical resolvents and evaluates it on
the actual `completedLeg` external states, keeps the retained torque,
reads the unlocalized torque-current pair on kernel sections, and
recovers the zero-transfer statement that the physical channel vertex
vanishes at `k=0`. Nothing here selects an electromagnetic pole or a
value of alpha.
-/

namespace LowEnergy.GaussComposite.PhysicalCharge
open GaussCoreHilbert GaussCoreDifferential SourceFamilyOperator CanonicalGradedCharge
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates CanonicalGradedSpatialSource
open CanonicalPhysicalSpatial CanonicalPhysicalResolvent
open GaussDensityCore (ScalarTest)
open GaussComposite.SourceGraph
open GaussUnitaryHistory (HistorySpace Index sourceFilter reader inclusion)
open scoped InnerProductSpace Topology

/-- The electromagnetic channel vertex on actual prepared legs: the
bounded localized current reader between the physical resolvents at
momenta `p+k` and `p`, evaluated between two `completedLeg` external
states. -/
def preparedCurrentVertex (phi : CanonicalGradedSpatial.Localizer)
    (left right : Bool) (a s b t : Fin 2) (a' : NativeLie)
    (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (f g : Profile) : ℂ :=
  inner ℂ (inclusion (completedLeg left a s f))
    (vertex (currentReader phi k a') p k z w hz hw
      (inclusion (completedLeg right b t g)))

/-- The inner-product algebra of the channel Ward identity; same
`simp only`-only discipline as `increment_wedge` for the completed
history-space inner product. -/
private theorem current_wedge
    (Ro Ri J T : HistorySpace →L[ℂ] HistorySpace) (d : ℂ) (x y : HistorySpace)
    (h : d • (Ro*J*Ri)=Ro*J-J*Ri+T) :
    d*inner ℂ x (Ro (J (Ri y)))=inner ℂ x (Ro (J y))-inner ℂ x (J (Ri y))+inner ℂ x (T y) := by
  have applied := congrArg (fun A : HistorySpace →L[ℂ] HistorySpace => inner ℂ x (A y)) h
  simp only [sub_eq_add_neg,smul_apply,add_apply,neg_apply,mul_apply_eq_comp,
    inner_smul_right,inner_add_right,inner_neg_right] at applied
  linear_combination applied

/-- The channel vertex between physical resolvents obeys the
source-generated Ward identity with the complete retained torque: the
current reader is not assumed to commute with the compressions. -/
theorem prepared_current_ward (phi : CanonicalGradedSpatial.Localizer)
    (left right : Bool) (a s b t : Fin 2) (a' : NativeLie)
    (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (f g : Profile) :
    (z-w)*preparedCurrentVertex phi left right a s b t a' p k z w hz hw f g =
    inner ℂ (inclusion (completedLeg left a s f))
      (sourceResolvent (p+k) z hz (reader (currentReader phi k a')
        (inclusion (completedLeg right b t g))))-
    inner ℂ (inclusion (completedLeg left a s f))
      (reader (currentReader phi k a') (sourceResolvent p w hw
        (inclusion (completedLeg right b t g))))+
    inner ℂ (inclusion (completedLeg left a s f))
      (torque (currentReader phi k a') p k z w hz hw
        (inclusion (completedLeg right b t g))) := by
  unfold preparedCurrentVertex
  have product : vertex (currentReader phi k a') p k z w hz hw=
      sourceResolvent (p+k) z hz*reader (currentReader phi k a')*
        sourceResolvent p w hw :=
    vertex_return (currentReader phi k a') p k z w hz hw
  have hward := physical_charge_ward (currentReader phi k a') p k z w hz hw
  have base := current_wedge (sourceResolvent (p+k) z hz) (sourceResolvent p w hw)
    (reader (currentReader phi k a')) (torque (currentReader phi k a') p k z w hz hw)
    (z-w) (inclusion (completedLeg left a s f)) (inclusion (completedLeg right b t g))
    (by rw [product] at hward; exact hward)
  simp only [product,mul_apply_eq_comp]
  exact base

/-- Norm bound for the localized current reader: the `k`-weighted sum
of the three spatial-component bounds. -/
theorem currentReader_bound (phi : CanonicalGradedSpatial.Localizer)
    (k : PhysicalMomentum) (a : NativeLie) :
    ‖currentReader phi k a‖≤∑ i : Fin 3, ‖((k i : ℂ))‖*
      CanonicalGradedLocalCurrent.bound phi (.spatial i) a := by
  calc
    ‖currentReader phi k a‖ =
      ‖∑ i : Fin 3, (k i : ℂ) • CanonicalGradedLocalCurrent.localReader phi (.spatial i) a‖ := rfl
    _ ≤ ∑ i : Fin 3, ‖(k i : ℂ) • CanonicalGradedLocalCurrent.localReader phi (.spatial i) a‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖((k i : ℂ))‖*
        CanonicalGradedLocalCurrent.bound phi (.spatial i) a := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ‖(k i : ℂ) • CanonicalGradedLocalCurrent.localReader phi (.spatial i) a‖ =
          ‖((k i : ℂ))‖*‖CanonicalGradedLocalCurrent.localReader phi (.spatial i) a‖ :=
          norm_smul _ _
        _ ≤ ‖((k i : ℂ))‖*CanonicalGradedLocalCurrent.bound phi (.spatial i) a :=
          mul_le_mul_of_nonneg_left (CanonicalGradedLocalCurrent.localReader_norm _ _ _)
            (norm_nonneg _)

/-- Norm bound for the prepared channel vertex: the `legBound`-weighted
current-reader bound over the two resolvent denominators. -/
theorem preparedCurrentVertex_bound (phi : CanonicalGradedSpatial.Localizer)
    (left right : Bool) (a s b t : Fin 2) (a' : NativeLie)
    (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (f g : Profile) :
    ‖preparedCurrentVertex phi left right a s b t a' p k z w hz hw f g‖≤
      legBound*‖f‖*(‖currentReader phi k a'‖*(1/|z.im|)*(1/|w.im|)*(legBound*‖g‖)) := by
  have inv (u : ℂ) : 0≤1/|u.im| := one_div_nonneg.mpr (abs_nonneg _)
  have vn : ‖inclusion (completedLeg right b t g)‖≤legBound*‖g‖ := by
    rw [inclusion.norm_map]
    exact completedLeg_bound right b t g
  have pref : 0≤‖currentReader phi k a'‖*(1/|z.im|)*(1/|w.im|) :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (inv z)) (inv w)
  have inner_bound : ‖vertex (currentReader phi k a') p k z w hz hw
      (inclusion (completedLeg right b t g))‖≤
      ‖currentReader phi k a'‖*(1/|z.im|)*(1/|w.im|)*(legBound*‖g‖) :=
    (vertex_bound (currentReader phi k a') p k z w hz hw _).trans
      (mul_le_mul_of_nonneg_left vn pref)
  calc
    ‖preparedCurrentVertex phi left right a s b t a' p k z w hz hw f g‖
      ≤ ‖inclusion (completedLeg left a s f)‖*
        ‖vertex (currentReader phi k a') p k z w hz hw
          (inclusion (completedLeg right b t g))‖ :=
      norm_inner_le_norm (𝕜 := ℂ) _ _
    _ = ‖completedLeg left a s f‖*
        ‖vertex (currentReader phi k a') p k z w hz hw
          (inclusion (completedLeg right b t g))‖ := by
      rw [inclusion.norm_map]
    _ ≤ ‖completedLeg left a s f‖*
        (‖currentReader phi k a'‖*(1/|z.im|)*(1/|w.im|)*(legBound*‖g‖)) :=
      mul_le_mul_of_nonneg_left inner_bound (norm_nonneg _)
    _ ≤ legBound*‖f‖*(‖currentReader phi k a'‖*(1/|z.im|)*(1/|w.im|)*(legBound*‖g‖)) :=
      mul_le_mul_of_nonneg_right (completedLeg_bound left a s f)
        (mul_nonneg pref (mul_nonneg legBound_nonnegative (norm_nonneg _)))

/-- The physical channel vertex vanishes at zero momentum transfer:
`currentReader phi 0 a` is the zero operator, so the resolvent-sandwiched
current and the whole channel vertex are zero. The electromagnetic
channel lives at nonzero transfer. -/
theorem prepared_current_vertex_zero (phi : CanonicalGradedSpatial.Localizer)
    (left right : Bool) (a s b t : Fin 2) (a' : NativeLie)
    (p : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (f g : Profile) :
    preparedCurrentVertex phi left right a s b t a' p 0 z w hz hw f g=0 := by
  have zero : currentReader phi 0 a'=(0 : H →L[ℂ] H) := by
    apply norm_eq_zero.mp
    apply le_antisymm
    · exact (currentReader_bound phi 0 a').trans_eq (by simp)
    · exact norm_nonneg _
  have vzero : vertex (0 : H →L[ℂ] H) p 0 z w hz hw=0 := by
    rw [vertex_return]
    simp only [GaussUnitaryHistory.reader_zero,zero_mul,mul_zero]
  simp only [preparedCurrentVertex,zero,vzero,zero_apply,inner_zero_right]

/-- The unlocalized spatial-current read on actual prepared kernel
sections: `sourcePair` between the left kernel section and the
Ward-core `k·J` action on the right kernel section. -/
def preparedCoreCurrentRead (k : PhysicalMomentum) (a : NativeLie)
    (f g : ScalarTest) : ℂ :=
  GaussFockPair.sourcePair (seedSection f)
    (CanonicalPhysicalWardCore.currentAction k a (seedSection g))

/-- The configuration-torque read on actual prepared kernel sections:
the remaining half of the Ward-core decomposition. -/
def preparedCoreTorqueRead (a : NativeLie) (f g : ScalarTest) : ℂ :=
  GaussFockPair.sourcePair (seedSection f)
    (CanonicalPhysicalWardCore.configurationTorque a (seedSection g))

/-- The unlocalized channel current vanishes at zero transfer on the
actual kernel sections. -/
theorem preparedCoreCurrentRead_zero (a : NativeLie) (f g : ScalarTest) :
    preparedCoreCurrentRead 0 a f g=0 := by
  have zero : CanonicalPhysicalWardCore.currentAction 0 a (seedSection g)=0 := by
    apply DFunLike.ext
    intro z
    rw [CanonicalPhysicalWardCore.currentAction_apply]
    have cm : contractedCurrent z 0 a=0 := by
      simp only [contractedCurrent,Pi.zero_apply,Complex.ofReal_zero,zero_smul,
        Finset.sum_const_zero]
    rw [cm]
    show GaussQuantumMultiplier.quantizer 0 ((seedSection g) z) = 0
    simp only [map_zero,zero_apply]
  simp only [preparedCoreCurrentRead,zero,GaussFockPair.sourcePair,
    map_zero,inner_zero_right]

/-- On actual prepared kernel sections the insertion pairing splits
exactly into the configuration-torque and channel-current reads: this
is the Ward-core endpoint theorem instantiated on `seedSection` legs,
using `seedSection_project` to collapse the label projection. -/
theorem prepared_core_insertion (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ)
    (f g : ScalarTest) :
    inner ℂ (embed (seedSection f))
      (CanonicalPhysicalWardEndpoints.sourceInsertion p k a cut (seedSection g)) =
    preparedCoreTorqueRead a f g+preparedCoreCurrentRead k a f g := by
  have base := CanonicalPhysicalWardEndpoints.paired_current_return p k a cut
    (seedSection f) (seedSection g)
  simp only [LowEnergy.ActualRadial.seedSection_project] at base
  have sum : GaussFockPair.sourcePair (seedSection f)
      (CanonicalPhysicalWardCore.configurationTorque a (seedSection g)+
        CanonicalPhysicalWardCore.currentAction k a (seedSection g)) =
    preparedCoreTorqueRead a f g+preparedCoreCurrentRead k a f g := by
    simp only [preparedCoreTorqueRead,preparedCoreCurrentRead,GaussFockPair.sourcePair,
      map_add,inner_add_right]
  exact base.trans sum

/-- The channel current on an actual created prepared leg equals the
kernel-side current action plus the localized momentum defect: the
leg-level `creation_reader_current_momentum` transported through the
`created_bridge`. -/
theorem prepared_created_current_momentum (phi : CanonicalGradedSpatial.Localizer)
    (p : PhysicalMomentum) (channel spin : Fin 2) (f : ScalarTest) :
    currentReader phi p nativeY (completedLeg true channel spin (core f))-
      creationSource channel spin (currentAction phi p nativeY (seedSection f)) =
    -(CanonicalGradedSpatial.momentumReader phi p
        (completedLeg true channel spin (core f))-
      creationSource channel spin (CanonicalGradedSpatial.localAction phi p
        (seedSection f))) := by
  have bridge : completedLeg true channel spin (core f)=
      creationSource channel spin (seedSection f) :=
    completedLeg_core true channel spin f
  rw [bridge]
  exact creation_reader_current_momentum phi p channel spin (seedSection f)

/-- At zero momenta the channel vertex between actual prepared legs
reads as the original same-resolvent current insertion: the literal
`vertex_original` specialization through `congrArg` at the pairing
level, avoiding `vertex`-definition reduction during matching. -/
theorem prepared_current_vertex_original (phi : CanonicalGradedSpatial.Localizer)
    (left right : Bool) (a s b t : Fin 2) (a' : NativeLie) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (f g : Profile) :
    preparedCurrentVertex phi left right a s b t a' 0 0 z w hz hw f g=
    inner ℂ (inclusion (completedLeg left a s f))
      (FullYSourceResolventGraphSplice.sameResolvent z hz
        (reader (currentReader phi 0 a')
          (FullYSourceResolventGraphSplice.sameResolvent w hw
            (inclusion (completedLeg right b t g))))) := by
  have step : inner ℂ (inclusion (completedLeg left a s f))
      (vertex (currentReader phi 0 a') 0 0 z w hz hw
        (inclusion (completedLeg right b t g))) =
    inner ℂ (inclusion (completedLeg left a s f))
      ((FullYSourceResolventGraphSplice.sameResolvent z hz*
        reader (currentReader phi 0 a')*
        FullYSourceResolventGraphSplice.sameResolvent w hw)
          (inclusion (completedLeg right b t g))) :=
    congrArg (fun A : HistorySpace →L[ℂ] HistorySpace =>
      inner ℂ (inclusion (completedLeg left a s f))
        (A (inclusion (completedLeg right b t g))))
      (vertex_original (currentReader phi 0 a') z w hz hw)
  unfold preparedCurrentVertex
  rw [step]
  simp only [mul_apply_eq_comp]

end LowEnergy.GaussComposite.PhysicalCharge
