import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalPreparedCurrent
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalBilocal
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPhysicalYResolvent
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.Electromagnetic.Canonical

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-!
# The electromagnetic channel on prepared legs: native charge product

The electromagnetic channel is identified at the proven charge
direction `nativeY`: the prepared seed carries charge -1 under
`chargeReader nativeY`, so the channel current between two prepared
external states is `currentReader phi k nativeY` sandwiched between the
physical resolvents. Its pole residue couples the two legs through the
charge product `incrementSign left * incrementSign right`, which is
exactly the `Q_a Q_b` factor in `V_ab(r)=Q_a Q_b C_EM/r`: +1 for
same-type pairs and -1 for mixed pairs, with `|Q|=1` by construction.
The remaining `C_EM` coefficient chain lives in the main window's
`Electromagnetic.canonicalCoulomb`; nothing here asserts its value.
-/

namespace LowEnergy.GaussComposite.PhysicalCharge
open GaussCoreHilbert GaussCoreDifferential SourceFamilyOperator CanonicalGradedCharge
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates CanonicalGradedSpatialSource
open CanonicalPhysicalSpatial CanonicalPhysicalResolvent
open GaussDensityCore (ScalarTest)
open GaussComposite.SourceGraph
open GaussUnitaryHistory (HistorySpace Index sourceFilter reader inclusion)
open scoped InnerProductSpace Topology

/-- The electromagnetic channel vertex: the current reader at the proven
charge direction `nativeY`, between the two physical resolvents on actual
prepared legs. The channel is identified, not chosen: `nativeY` is the
direction under which the prepared electron seed has charge -1. -/
def emChannelVertex (phi : CanonicalGradedSpatial.Localizer)
    (left right : Bool) (a s b t : Fin 2)
    (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (f g : Profile) : ℂ :=
  preparedCurrentVertex phi left right a s b t nativeY p k z w hz hw f g

/-- The channel Ward identity at the charge direction, inherited with
the complete commutator torque. -/
theorem em_channel_ward (phi : CanonicalGradedSpatial.Localizer)
    (left right : Bool) (a s b t : Fin 2)
    (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (f g : Profile) :
    (z-w)*emChannelVertex phi left right a s b t p k z w hz hw f g =
    inner ℂ (inclusion (completedLeg left a s f))
      (sourceResolvent (p+k) z hz (reader (currentReader phi k nativeY)
        (inclusion (completedLeg right b t g))))-
    inner ℂ (inclusion (completedLeg left a s f))
      (reader (currentReader phi k nativeY) (sourceResolvent p w hw
        (inclusion (completedLeg right b t g))))+
    inner ℂ (inclusion (completedLeg left a s f))
      (torque (currentReader phi k nativeY) p k z w hz hw
        (inclusion (completedLeg right b t g))) := by
  unfold emChannelVertex
  exact prepared_current_ward phi left right a s b t nativeY p k z w hz hw f g

/-- The electromagnetic channel vanishes at zero momentum transfer. -/
theorem em_channel_vertex_zero (phi : CanonicalGradedSpatial.Localizer)
    (left right : Bool) (a s b t : Fin 2)
    (p : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (f g : Profile) :
    emChannelVertex phi left right a s b t p 0 z w hz hw f g=0 := by
  unfold emChannelVertex
  exact prepared_current_vertex_zero phi left right a s b t nativeY p z w hz hw f g

/-- The two-leg charge product entering the channel residue: the
`Q_a Q_b` factor of `V_ab(r)=Q_a Q_b C_EM/r`, evaluated at the proven
charge signs of the prepared legs. -/
def preparedChargeProduct (left right : Bool) : ℂ :=
  incrementSign left * incrementSign right

/-- Electron charge normalization: each leg carries unit charge
`|Q|=1` at the identified direction. -/
theorem prepared_charge_unit (addition : Bool) : ‖incrementSign addition‖=1 := by
  cases addition <;> simp [incrementSign]

/-- The charge product is real (its star is itself), so it can stand in
front of a channel-residue coefficient without a phase. -/
theorem star_charge_product (left right : Bool) :
    (starRingEnd ℂ) (preparedChargeProduct left right)=preparedChargeProduct left right := by
  cases left <;> cases right <;>
    simp [preparedChargeProduct, incrementSign, ← Complex.star_def]

@[simp] theorem charge_product_created_created :
    preparedChargeProduct true true=1 := by simp [preparedChargeProduct, incrementSign]

@[simp] theorem charge_product_created_annihilated :
    preparedChargeProduct true false=-1 := by simp [preparedChargeProduct, incrementSign]

@[simp] theorem charge_product_annihilated_created :
    preparedChargeProduct false true=-1 := by simp [preparedChargeProduct, incrementSign]

@[simp] theorem charge_product_annihilated_annihilated :
    preparedChargeProduct false false=1 := by simp [preparedChargeProduct, incrementSign]

/-- The residue charge factor read off the signed increment Ward:
`(z-w)` times the increment vertex between the two prepared legs returns
`sigma_R * G_{p+k}(z) - sigma_L * G_p(w) + <L,T R>`, so at a channel pole
each propagator term carries the OTHER endpoint's charge sign and the
product `sigma_L sigma_R` is the `Q_a Q_b` of the interaction. -/
theorem em_residue_charge_factor (left right : Bool) (a s b t : Fin 2)
    (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (f g : Profile) :
    incrementSign right*preparedTwoPoint left right a s b t (p+k) z hz f g-
      incrementSign left*preparedTwoPoint left right a s b t p w hw f g =
    (z-w)*inner ℂ (inclusion (completedLeg left a s f))
      (incrementVertex (chargeReader nativeY) p k z w hz hw
        (inclusion (completedLeg right b t g)))-
      inner ℂ (inclusion (completedLeg left a s f))
        (torque (chargeReader nativeY+1) p k z w hz hw
          (inclusion (completedLeg right b t g))) := by
  have h := prepared_increment_ward left right a s b t p k z w hz hw f g
  rw [h]
  abel

/-- Norm bound for the channel vertex, inherited through the
charge-direction specialization. -/
theorem emChannelVertex_bound (phi : CanonicalGradedSpatial.Localizer)
    (left right : Bool) (a s b t : Fin 2)
    (p k : PhysicalMomentum) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (f g : Profile) :
    ‖emChannelVertex phi left right a s b t p k z w hz hw f g‖≤
      legBound*‖f‖*(‖currentReader phi k nativeY‖*(1/|z.im|)*(1/|w.im|)*(legBound*‖g‖)) := by
  unfold emChannelVertex
  exact preparedCurrentVertex_bound phi left right a s b t nativeY p k z w hz hw f g

/-- On kernel sections the channel current read at the charge direction
is the WardCore unlocalized spatial `k·J` action on `nativeY`. -/
def emCoreCurrentRead (k : PhysicalMomentum) (f g : ScalarTest) : ℂ :=
  preparedCoreCurrentRead k nativeY f g

/-- The charge-direction core current vanishes at zero transfer. -/
theorem emCoreCurrentRead_zero (f g : ScalarTest) :
    emCoreCurrentRead 0 f g=0 := preparedCoreCurrentRead_zero nativeY f g

/-- The interaction coefficient `Q_a Q_b * C_EM` between the two
prepared legs: the real charge product times the already generated
canonical Coulomb coefficient. This is the numerator of `V_ab(r)`
before the 1/r spatial kernel is attached by the main window; nothing
here asserts its SI value. -/
def emCoulombCoupling (left right : Bool) : ℝ :=
  (preparedChargeProduct left right).re *
    SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedAction.AtomicScales.canonicalCoulomb

/-- Same-type prepared legs give the repulsive-signed Coulomb
numerator `+C_EM`. -/
theorem em_coulomb_same :
    emCoulombCoupling true true=
      SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedAction.AtomicScales.canonicalCoulomb ∧
    emCoulombCoupling false false=
      SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedAction.AtomicScales.canonicalCoulomb := by
  unfold emCoulombCoupling
  constructor <;> simp [preparedChargeProduct, incrementSign]

/-- Mixed prepared legs give the attractive-signed numerator `-C_EM`. -/
theorem em_coulomb_mixed :
    emCoulombCoupling true false=
      -SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedAction.AtomicScales.canonicalCoulomb ∧
    emCoulombCoupling false true=
      -SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedAction.AtomicScales.canonicalCoulomb := by
  unfold emCoulombCoupling
  constructor <;> simp [preparedChargeProduct, incrementSign]

/-- The interaction numerator is nonzero on every prepared-leg pair,
since both factors are nonzero. -/
theorem em_coulomb_nonzero (left right : Bool) :
    emCoulombCoupling left right≠0 := by
  unfold emCoulombCoupling
  apply mul_ne_zero
  · cases left <;> cases right <;>
      simp [preparedChargeProduct, incrementSign]
  · have hpos :
        0 < SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedAction.AtomicScales.canonicalCoulomb := by
      rw [SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedAction.AtomicScales.original_coulomb_coefficient]
      apply div_pos
      · exact sq_pos_of_pos (mul_pos (by norm_num)
          SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.spinScale_pos)
      · exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
          SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
    exact hpos.ne'

/-- The identified channel's single current component: the localized
spatial current at direction `nativeY`. `currentReader` is its literal
momentum contraction. -/
def emCurrent (phi : CanonicalGradedSpatial.Localizer) (i : Fin 3) :
    CanonicalGradedSpatialKernel.NativeCurrent :=
  ⟨phi, CanonicalGradedCurrent.Component.spatial i, nativeY⟩

/-- The charge-direction channel current equals the contraction of the
EM component currents, closing the loop between the vertex and the
bilocal response layers. -/
theorem emCurrent_contracted (phi : CanonicalGradedSpatial.Localizer)
    (k : PhysicalMomentum) :
    currentReader phi k nativeY=
      ∑ i : Fin 3, (k i : ℂ) •
        CanonicalGradedSpatialKernel.current (emCurrent phi i) := by
  simp only [currentReader,emCurrent,CanonicalGradedSpatialKernel.current]

/-- The electromagnetic channel response: the physical current-current
propagator at the charge direction between actual prepared legs. Its
finite kernel is the source-generated `finiteKernel` at the EM
component currents; nothing is chosen. -/
def emChannelResponse (phi : CanonicalGradedSpatial.Localizer)
    (p k ell : PhysicalMomentum) (i j : Fin 3) (cut : ℕ)
    (age frequency damping : ℝ) (positive : 0<damping) :
    HistorySpace →L[ℂ] HistorySpace :=
  PhysicalBilocal.physicalFullResponse p k ell (emCurrent phi i) (emCurrent phi j)
    cut age frequency damping positive

/-- On actual source legs the EM channel response reads directly as the
main window's physical current response: the grade-zero projection is
transparent on prepared external states. -/
theorem em_channel_response_return (phi : CanonicalGradedSpatial.Localizer)
    (p k ell : PhysicalMomentum) (i j : Fin 3) (cut : ℕ)
    (age frequency damping : ℝ) (positive : 0<damping)
    (left right : Bool) (a s b t : Fin 2) (f g : QuantumTest)
    (profile : SourceCoordinateSlice → ℂ)
    (sameSource : ∀ z, f z=profile z • CanonicalCompletedSector.seed) :
    inner ℂ (inclusion (leg left a s f))
      (emChannelResponse phi p k ell i j cut age frequency damping positive
        (inclusion (leg right b t g)))=
    inner ℂ (inclusion (leg left a s f))
      (CanonicalPhysicalCurrent.response p k ell (emCurrent phi i) (emCurrent phi j)
        age frequency damping positive (inclusion (leg right b t g))) := by
  unfold emChannelResponse
  exact PhysicalBilocal.physical_composite_response_return p k ell _ _ cut
    age frequency damping positive left right a s b t f g profile sameSource

/-- The EM channel response is independent of the literal cutoff on
actual prepared legs, inherited from the physical response layer. -/
theorem em_channel_response_cutoff_independent
    (phi : CanonicalGradedSpatial.Localizer)
    (p k ell : PhysicalMomentum) (i j : Fin 3) (cut other : ℕ)
    (age frequency damping : ℝ) (positive : 0<damping) :
    emChannelResponse phi p k ell i j cut age frequency damping positive=
      emChannelResponse phi p k ell i j other age frequency damping positive := by
  unfold emChannelResponse
  exact PhysicalBilocal.physical_full_cutoff_independent p k ell _ _ cut other
    age frequency damping positive

/-- Grade powers keep the homogeneous raise: `G*Tⁿ = TⁿG + n·Tⁿ`
whenever `G*T = T*G + T`. -/
private theorem grade_power_homogeneous {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (G T : R) (n : ℕ)
    (raises : G*T=T*G+T) : G*T^n=T^n*G+(n : ℂ)•T^n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ T k, ← mul_assoc, ih, add_mul, smul_mul_assoc, ← pow_succ,
        mul_assoc, raises, mul_add, ← mul_assoc, ← pow_succ, Nat.cast_add,
        Nat.cast_one]
      nth_rewrite 2 [← one_smul ℂ (T^(k+1))]
      rw [add_assoc, ← add_smul]
      congr 1
      abel

/-- The grade-zero left projection kills every positive power of the
nilpotent Yukawa step, mirroring `power_left_zero` at the Number-free
projection that actually retains prepared legs. -/
theorem grade_zero_step_left_zero (p : PhysicalMomentum) (F : Index) (cut : ℕ)
    (z : ℂ) (hz : z.im≠0) (n : ℕ) (positive : 0<n) :
    gradeZeroProjection*(CanonicalPhysicalYResolvent.step p F cut z)^n=0 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [mul_apply_eq_comp]
  change gradeZeroProjection
    (((CanonicalPhysicalYResolvent.step p F cut z)^n) x)=0
  have kill (u : H) : inner ℂ u
      (gradeZeroProjection
        (((CanonicalPhysicalYResolvent.step p F cut z)^n) x))=0 := by
    rw [← grade_zero_projection_pair]
    exact positive_grade_pair_zero _ n positive
      (grade_power_homogeneous _ _ n
        (CanonicalPhysicalYResolvent.step_raises p F cut z hz))
      _ _ (grade_zero_projected u)
  have sq := kill (gradeZeroProjection
    (((CanonicalPhysicalYResolvent.step p F cut z)^n) x))
  exact (inner_self_eq_zero).mp sq

/-- The grade-zero projection sees the Volterra series as itself:
all positive steps vanish on the left. -/
theorem grade_zero_series_return (p : PhysicalMomentum) (F : Index) (cut : ℕ)
    (z : ℂ) (hz : z.im≠0) :
    gradeZeroProjection*CanonicalPhysicalYResolvent.series p F cut z=
      gradeZeroProjection := by
  rw [CanonicalPhysicalYResolvent.series, Finset.mul_sum]
  rw [Finset.sum_eq_single 0]
  · rw [pow_zero, mul_one]
  · intro n _ different
    exact grade_zero_step_left_zero p F cut z hz n (Nat.pos_of_ne_zero different)
  · intro outside
    exact (outside (by simp)).elim

/-- The grade-zero projection of the complete finite resolvent equals
the grade-zero projection of the physical resolvent. -/
theorem grade_zero_finite_full_left (p : PhysicalMomentum) (F : Index) (cut : ℕ)
    (z : ℂ) (hz : z.im≠0) :
    gradeZeroProjection*CanonicalPhysicalYResolvent.finiteFull p F cut z=
      gradeZeroProjection*CanonicalPhysicalResolvent.finiteResolvent p F z := by
  rw [CanonicalPhysicalYResolvent.finiteFull, ← mul_assoc,
    grade_zero_series_return p F cut z hz]

/-- Lifted to history: the grade-zero reader of the complete resolvent
is the grade-zero reader of the physical resolvent. -/
theorem grade_zero_completed_left_return (p : PhysicalMomentum) (cut : ℕ) (z : ℂ)
    (hz : z.im≠0) :
    reader gradeZeroProjection*CanonicalPhysicalYResolvent.fullResolvent p cut z hz=
      reader gradeZeroProjection*CanonicalPhysicalResolvent.sourceResolvent p z hz := by
  change lift sourceFilter (constant gradeZeroProjection)*lift sourceFilter
    (CanonicalPhysicalYResolvent.fullFamily p cut z hz)=
    lift sourceFilter (constant gradeZeroProjection)*lift sourceFilter
    (CanonicalPhysicalResolvent.resolventFamily p z hz)
  calc
    _ = lift sourceFilter (comp (constant gradeZeroProjection)
        (CanonicalPhysicalYResolvent.fullFamily p cut z hz)) :=
      (lift_comp sourceFilter _ _).symm
    _ = lift sourceFilter (comp (constant gradeZeroProjection)
        (CanonicalPhysicalResolvent.resolventFamily p z hz)) :=
      lift_congr sourceFilter _ _ (fun F => grade_zero_finite_full_left p F cut z hz)
    _ = _ := lift_comp sourceFilter _ _

/-- The grade-zero reader is a contraction on history space. -/
theorem reader_grade_zero_bound (x : HistorySpace) :
    ‖reader gradeZeroProjection x‖≤‖x‖ := by
  have piece (g : H) : ‖gradeZeroProjection g‖≤‖g‖ := by
    change ‖gradeZeroPiece g‖≤‖g‖
    exact grade_zero_piece_bound g
  have bound : ‖reader gradeZeroProjection x‖≤1*‖x‖ := by
    apply SourceBoundaryGram.lift_bound_explicit sourceFilter
      (constant gradeZeroProjection) 1 zero_le_one
    intro F g
    change ‖gradeZeroProjection g‖≤1*‖g‖
    simpa only [one_mul] using piece g
  simpa only [one_mul] using bound

/-- The channel's projected full propagator on prepared legs: the
complete `compression + cutoff` resolvent between actual external
states, read through the grade-zero projection that retains every
Number sector of the prepared legs. -/
def preparedFullTwoPoint (left right : Bool) (a s b t : Fin 2)
    (p : PhysicalMomentum) (cut : ℕ) (z : ℂ) (hz : z.im≠0)
    (f g : Profile) : ℂ :=
  inner ℂ (inclusion (completedLeg left a s f))
    (reader gradeZeroProjection
      (CanonicalPhysicalYResolvent.fullResolvent p cut z hz
        (inclusion (completedLeg right b t g))))

/-- Under the grade-zero projection the complete propagator returns
the physical resolvent two-point: the cutoff Yukawa tail does not
contaminate the channel's pole carrier on actual prepared legs. -/
theorem prepared_full_twoPoint_projected (left right : Bool) (a s b t : Fin 2)
    (p : PhysicalMomentum) (cut : ℕ) (z : ℂ) (hz : z.im≠0)
    (f g : Profile) :
    preparedFullTwoPoint left right a s b t p cut z hz f g=
    inner ℂ (inclusion (completedLeg left a s f))
      (reader gradeZeroProjection
        (CanonicalPhysicalResolvent.sourceResolvent p z hz
          (inclusion (completedLeg right b t g)))) := by
  unfold preparedFullTwoPoint
  have base := congrArg
    (inner ℂ (inclusion (completedLeg left a s f)))
    (congrArg (fun T : HistorySpace →L[ℂ] HistorySpace =>
      T (inclusion (completedLeg right b t g)))
      (grade_zero_completed_left_return p cut z hz))
  simp only [mul_apply_eq_comp] at base
  exact base

/-- On actual kernel legs the grade-zero projection is transparent:
the projected full propagator is the literal complete-resolvent
two-point between the prepared states. -/
theorem prepared_full_twoPoint_leg (left right : Bool) (a s b t : Fin 2)
    (p : PhysicalMomentum) (cut : ℕ) (z : ℂ) (hz : z.im≠0)
    (f g : ScalarTest) :
    preparedFullTwoPoint left right a s b t p cut z hz (core f) (core g)=
    inner ℂ (inclusion (completedLeg left a s (core f)))
      (CanonicalPhysicalYResolvent.fullResolvent p cut z hz
        (inclusion (completedLeg right b t (core g)))) := by
  unfold preparedFullTwoPoint
  rw [← grade_zero_history_pair]
  have fixed := source_leg_grade_zero_fixed left a s (seedSection f) _
    (seedSection_apply f)
  rw [← completedLeg_core] at fixed
  rw [fixed]

/-- The projected full propagator on prepared legs is cutoff
independent: every literal cut reads the same pole carrier. -/
theorem prepared_full_twoPoint_cutoff_independent (left right : Bool) (a s b t : Fin 2)
    (p : PhysicalMomentum) (cut other : ℕ) (z : ℂ) (hz : z.im≠0)
    (f g : Profile) :
    preparedFullTwoPoint left right a s b t p cut z hz f g=
      preparedFullTwoPoint left right a s b t p other z hz f g := by
  rw [prepared_full_twoPoint_projected, prepared_full_twoPoint_projected]

/-- Norm bound for the projected full propagator on prepared legs:
`legBound²·‖f‖‖g‖/|z.im|`, inherited from the physical resolvent. -/
theorem preparedFullTwoPoint_bound (left right : Bool) (a s b t : Fin 2)
    (p : PhysicalMomentum) (cut : ℕ) (z : ℂ) (hz : z.im≠0)
    (f g : Profile) :
    ‖preparedFullTwoPoint left right a s b t p cut z hz f g‖≤
      legBound*‖f‖*((1/|z.im|)*(legBound*‖g‖)) := by
  unfold preparedFullTwoPoint
  have legL : ‖inclusion (completedLeg left a s f)‖≤legBound*‖f‖ := by
    rw [inclusion.norm_map]
    exact completedLeg_bound left a s f
  have legR : ‖inclusion (completedLeg right b t g)‖≤legBound*‖g‖ := by
    rw [inclusion.norm_map]
    exact completedLeg_bound right b t g
  have returned := congrArg (fun T : HistorySpace →L[ℂ] HistorySpace =>
      T (inclusion (completedLeg right b t g)))
    (grade_zero_completed_left_return p cut z hz)
  rw [mul_apply_eq_comp, mul_apply_eq_comp] at returned
  have res : ‖reader gradeZeroProjection
      (CanonicalPhysicalYResolvent.fullResolvent p cut z hz
        (inclusion (completedLeg right b t g)))‖≤
      (1/|z.im|)*(legBound*‖g‖) := by
    rw [returned]
    exact (reader_grade_zero_bound _).trans
      ((CanonicalPhysicalResolvent.resolvent_bound p z hz
        (inclusion (completedLeg right b t g))).trans
        (mul_le_mul_of_nonneg_left legR
          (le_of_lt (one_div_pos.mpr (abs_pos.mpr hz)))))
  exact (norm_inner_le_norm (𝕜:=ℂ) _ _).trans
    (mul_le_mul legL res (norm_nonneg _)
      (mul_nonneg legBound_nonnegative (norm_nonneg f)))

end LowEnergy.GaussComposite.PhysicalCharge
