import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalPreparedCoulomb
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPhysicalWard
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationElectricPreparedWard

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-!
# Full-resolvent channel vertex and the four-channel Ward core on prepared legs

The main window now supplies `CanonicalPhysicalWard.vertex`, the charge
vertex between the *complete* `compression+cutoff` resolvents, and
`PreparationVacuumFullElectricWard.coreChannels`, the four-term kernel
split `configurationTorque + currentAction + pairCurrent + yukawaTorque`
of the Ward core `wardCore`. This module transports both to the
grade-zero projection that actually reaches the prepared legs: the
(1,0) `historyProjection` versions in `CanonicalPhysicalWard` cannot
see card-2/card-0 legs, so every statement here is reproved at
`gradeZeroProjection`, which the legs survive. The retained Ward
defect and the Yukawa channel remain explicit; nothing here selects an
electromagnetic pole or a value of alpha.
-/

namespace LowEnergy.GaussComposite.PhysicalCharge
open GaussCoreHilbert GaussCoreDifferential SourceFamilyOperator CanonicalGradedCharge
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates CanonicalGradedSpatialSource
open CanonicalPhysicalSpatial CanonicalPhysicalResolvent
open GaussDensityCore (ScalarTest)
open GaussComposite.SourceGraph
open GaussUnitaryHistory (HistorySpace Index sourceFilter reader inclusion)
open scoped InnerProductSpace Topology

private theorem inverse_commutes {R : Type*} [Monoid R] (P D U : R)
    (left : U*D=1) (right : D*U=1) (commutes : P*D=D*P) : P*U=U*P := by
  calc
    P*U = (U*D)*(P*U) := by rw [left, one_mul]
    _ = U*(D*P)*U := by simp only [mul_assoc]
    _ = U*(P*D)*U := by rw [commutes]
    _ = (U*P)*(D*U) := by simp only [mul_assoc]
    _ = U*P := by rw [right, mul_one]

/-- Each label projection commutes with the compression resolvent: the
resolvent is the inverse of `compression - z·1`, and `compression`
preserves every label block. -/
theorem resolvent_label_blocks (p : PhysicalMomentum) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : NativeHistoryGrade.Label) :
    Commute (NativeHistoryGrade.projection g)
      (CanonicalPhysicalResolvent.finiteResolvent p F z) := by
  have shifted := (CanonicalPhysicalSpatial.compression_blocks p F g).sub_right
    ((Commute.one_right (NativeHistoryGrade.projection g)).smul_right z)
  exact inverse_commutes
    (NativeHistoryGrade.projection g) _ _
    (FullYSourceResolventGraphSplice.resolvent_left _
      (CanonicalPhysicalSpatial.compression_selfAdjoint p F) z hz)
    (FullYSourceResolventGraphSplice.resolvent_right _
      (CanonicalPhysicalSpatial.compression_selfAdjoint p F) z hz) shifted.eq

/-- Each label projection commutes with the bounded charge reader. -/
theorem charge_label_blocks (a : NativeLie) (g : NativeHistoryGrade.Label) :
    Commute (NativeHistoryGrade.projection g) (chargeReader a) :=
  CanonicalGradedCurrent.boundedMatrix_blocks (chargeMatrix a)
    (CanonicalGradedCurrent.gaugeMatrix_preserves 0 .temporal a) g

/-- The grade-zero projection commutes with the compression resolvent. -/
theorem resolvent_grade_zero_blocks (p : PhysicalMomentum) (F : Index) (z : ℂ)
    (hz : z.im≠0) :
    Commute gradeZeroProjection (CanonicalPhysicalResolvent.finiteResolvent p F z) :=
  GaussComposite.grade_zero_commutes _ (fun g => resolvent_label_blocks p F z hz g)

/-- The grade-zero projection commutes with the charge reader. -/
theorem charge_grade_zero_blocks (a : NativeLie) :
    Commute gradeZeroProjection (chargeReader a) :=
  GaussComposite.grade_zero_commutes _ (fun g => charge_label_blocks a g)

/-- Reader-level commutation lifts componentwise commutation. -/
theorem reader_commutes (A B : H →L[ℂ] H) (comm : Commute A B) :
    Commute (reader A) (reader B) := by
  change lift sourceFilter (constant A)*lift sourceFilter (constant B) =
    lift sourceFilter (constant B)*lift sourceFilter (constant A)
  calc
    _ = lift sourceFilter (comp (constant A) (constant B)) :=
      (lift_comp sourceFilter _ _).symm
    _ = lift sourceFilter (comp (constant B) (constant A)) :=
      lift_congr sourceFilter _ _ (fun F => comm.eq)
    _ = _ := lift_comp sourceFilter _ _

/-- The grade-zero reader commutes with the physical resolvent. -/
theorem sourceResolvent_grade_zero (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) :
    Commute (reader gradeZeroProjection)
      (CanonicalPhysicalResolvent.sourceResolvent p z hz) := by
  change lift sourceFilter (constant gradeZeroProjection)*lift sourceFilter
    (CanonicalPhysicalResolvent.resolventFamily p z hz) =
    lift sourceFilter (CanonicalPhysicalResolvent.resolventFamily p z hz)*
      lift sourceFilter (constant gradeZeroProjection)
  calc
    _ = lift sourceFilter (comp (constant gradeZeroProjection)
        (CanonicalPhysicalResolvent.resolventFamily p z hz)) :=
      (lift_comp sourceFilter _ _).symm
    _ = lift sourceFilter (comp (CanonicalPhysicalResolvent.resolventFamily p z hz)
        (constant gradeZeroProjection)) :=
      lift_congr sourceFilter _ _ (fun F => (resolvent_grade_zero_blocks p F z hz).eq)
    _ = _ := lift_comp sourceFilter _ _

/-- The grade-zero reader commutes with the lifted charge reader. -/
theorem reader_charge_grade_zero (a : NativeLie) :
    Commute (reader gradeZeroProjection) (reader (chargeReader a)) :=
  reader_commutes _ _ (charge_grade_zero_blocks a)

private theorem left_vertex_return {R : Type*} [Monoid R] (P U V A B Q : R)
    (left : P*U=P*A) (right : P*V=P*B) (pA : Commute P A) (pQ : Commute P Q) :
    P*(U*Q*V)=P*(A*Q*B) := by
  have route (X : R) : P*(A*Q*X)=(A*Q)*(P*X) := by
    calc
      _ = ((P*A)*Q)*X := by simp only [mul_assoc]
      _ = A*(P*Q)*X := by rw [pA.eq]; simp only [mul_assoc]
      _ = (A*Q)*(P*X) := by rw [pQ.eq]; simp only [mul_assoc]
  calc
    _ = P*(A*Q*V) := by simp only [← mul_assoc]; rw [left]
    _ = (A*Q)*(P*V) := route V
    _ = (A*Q)*(P*B) := by rw [right]
    _ = P*(A*Q*B) := (route B).symm

/-- Grade-zero projection of the full vertex is the grade-zero
projection of the physical vertex: the Yukawa tail cannot pollute the
pole-carrying channel vertex. -/
theorem grade_zero_vertex_return (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ)
    (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    reader gradeZeroProjection*CanonicalPhysicalWard.vertex p k a cut z w hz hw =
      reader gradeZeroProjection*(CanonicalPhysicalResolvent.sourceResolvent (p+k) z hz*
        reader (chargeReader a)*CanonicalPhysicalResolvent.sourceResolvent p w hw) := by
  rw [CanonicalPhysicalWard.vertex_return]
  exact left_vertex_return _ _ _ _ _ _
    (grade_zero_completed_left_return (p+k) cut z hz)
    (grade_zero_completed_left_return p cut w hw)
    (sourceResolvent_grade_zero (p+k) z hz) (reader_charge_grade_zero a)

private theorem projected_response_identity {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P Q U V A B W X : E →L[ℂ] E) (d : ℂ)
    (hW : W=Q*V-U*Q+d • X) (hU : P*U=P*A) (hV : P*V=P*B)
    (hQ : Commute P Q) (hX : P*X=P*(A*Q*B)) :
    P*W=P*(Q*B-A*Q+d • (A*Q*B)) := by
  have qr : P*(Q*V)=P*(Q*B) := by
    calc
      _ = Q*(P*V) := by rw [← mul_assoc, hQ.eq, mul_assoc]
      _ = _ := by rw [hV, ← mul_assoc, ← hQ.eq, mul_assoc]
  have rq : P*(U*Q)=P*(A*Q) := by rw [← mul_assoc, ← mul_assoc, hU]
  rw [hW, mul_add, mul_sub, qr, rq, mul_smul_comm, hX, mul_add, mul_sub, mul_smul_comm]

/-- Grade-zero projection of the full Ward response: the cutoff torque
collapses to the physical-resolvent expression. -/
theorem grade_zero_response_return (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ)
    (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    reader gradeZeroProjection*CanonicalPhysicalWard.response p k a cut z w hz hw =
      reader gradeZeroProjection*
        (reader (chargeReader a)*CanonicalPhysicalResolvent.sourceResolvent p w hw-
          CanonicalPhysicalResolvent.sourceResolvent (p+k) z hz*reader (chargeReader a)+
          (z-w) • (CanonicalPhysicalResolvent.sourceResolvent (p+k) z hz*
            reader (chargeReader a)*CanonicalPhysicalResolvent.sourceResolvent p w hw)) :=
  projected_response_identity _ _ _ _ _ _ _ _ (z-w)
    (CanonicalPhysicalWard.response_return p k a cut z w hz hw)
    (grade_zero_completed_left_return (p+k) cut z hz)
    (grade_zero_completed_left_return p cut w hw)
    (reader_charge_grade_zero a) (grade_zero_vertex_return p k a cut z w hz hw)

/-- The projected full vertex is cutoff-independent. -/
theorem grade_zero_vertex_cutoff_independent (p k : PhysicalMomentum) (a : NativeLie)
    (cut other : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    reader gradeZeroProjection*CanonicalPhysicalWard.vertex p k a cut z w hz hw =
      reader gradeZeroProjection*CanonicalPhysicalWard.vertex p k a other z w hz hw :=
  (grade_zero_vertex_return p k a cut z w hz hw).trans
    (grade_zero_vertex_return p k a other z w hz hw).symm

/-- The projected full response is cutoff-independent. -/
theorem grade_zero_response_cutoff_independent (p k : PhysicalMomentum) (a : NativeLie)
    (cut other : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    reader gradeZeroProjection*CanonicalPhysicalWard.response p k a cut z w hz hw =
      reader gradeZeroProjection*CanonicalPhysicalWard.response p k a other z w hz hw :=
  (grade_zero_response_return p k a cut z w hz hw).trans
    (grade_zero_response_return p k a other z w hz hw).symm

/-- The projected full vertex carries the standard resolvent bound. -/
theorem grade_zero_vertex_bound (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ)
    (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (x : HistorySpace) :
    ‖reader gradeZeroProjection
      (CanonicalPhysicalWard.vertex p k a cut z w hz hw x)‖ ≤
      ((1/|z.im|)*‖chargeReader a‖*(1/|w.im|))*‖x‖ := by
  have returned := congrArg (fun T : HistorySpace →L[ℂ] HistorySpace => T x)
    (grade_zero_vertex_return p k a cut z w hz hw)
  change reader gradeZeroProjection
    (CanonicalPhysicalWard.vertex p k a cut z w hz hw x)=
    reader gradeZeroProjection (CanonicalPhysicalResolvent.sourceResolvent (p+k) z hz
      (reader (chargeReader a) (CanonicalPhysicalResolvent.sourceResolvent p w hw x)))
      at returned
  rw [returned]
  calc
    _ ≤ ‖CanonicalPhysicalResolvent.sourceResolvent (p+k) z hz
        (reader (chargeReader a) (CanonicalPhysicalResolvent.sourceResolvent p w hw x))‖ :=
      reader_grade_zero_bound _
    _ ≤ (1/|z.im|)*‖reader (chargeReader a)
        (CanonicalPhysicalResolvent.sourceResolvent p w hw x)‖ :=
      resolvent_bound _ _ _ _
    _ ≤ (1/|z.im|)*(‖chargeReader a‖*
        ‖CanonicalPhysicalResolvent.sourceResolvent p w hw x‖) :=
      mul_le_mul_of_nonneg_left
        (CanonicalPhysicalWard.charge_bound a _) (by positivity)
    _ ≤ (1/|z.im|)*(‖chargeReader a‖*((1/|w.im|)*‖x‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (resolvent_bound p w hw x) (norm_nonneg _))
        (by positivity)
    _ = _ := by ring

/-- The full-resolvent channel vertex between two prepared legs: the
charge vertex between complete `compression+cutoff` resolvents at
momenta `p+k` and `p`, evaluated on `completedLeg` external states. -/
def preparedFullVertex (left right : Bool) (a s b t : Fin 2) (a' : NativeLie)
    (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (f g : Profile) : ℂ :=
  inner ℂ (inclusion (completedLeg left a s f))
    (CanonicalPhysicalWard.vertex p k a' cut z w hz hw
      (inclusion (completedLeg right b t g)))

/-- The full-resolvent cross-momentum Ward identity on actual prepared
legs: `(z-w)` times the channel vertex equals the charge endpoint
difference plus the retained full response. -/
theorem prepared_full_ward (left right : Bool) (a s b t : Fin 2) (a' : NativeLie)
    (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (f g : Profile) :
    (z-w)*preparedFullVertex left right a s b t a' p k cut z w hz hw f g =
    inner ℂ (inclusion (completedLeg left a s f))
      (CanonicalPhysicalYResolvent.fullResolvent (p+k) cut z hz
        (reader (chargeReader a') (inclusion (completedLeg right b t g))))-
    inner ℂ (inclusion (completedLeg left a s f))
      (reader (chargeReader a') (CanonicalPhysicalYResolvent.fullResolvent p cut w hw
        (inclusion (completedLeg right b t g))))+
    inner ℂ (inclusion (completedLeg left a s f))
      (CanonicalPhysicalWard.response p k a' cut z w hz hw
        (inclusion (completedLeg right b t g))) := by
  unfold preparedFullVertex
  have applied := congrArg (fun T : HistorySpace →L[ℂ] HistorySpace =>
    inner ℂ (inclusion (completedLeg left a s f)) (T (inclusion (completedLeg right b t g))))
    (CanonicalPhysicalWard.full_charge_ward p k a' cut z w hz hw)
  simp only [sub_eq_add_neg,smul_apply,add_apply,neg_apply,mul_apply_eq_comp,
    inner_smul_right,inner_add_right,inner_neg_right] at applied
  simpa only [sub_eq_add_neg] using applied

/-- The projected full vertex on prepared legs equals the projected
physical vertex on prepared legs: the grade-zero projection removes the
cutoff tail without touching the pole carrier. -/
theorem prepared_full_vertex_projected (left right : Bool) (a s b t : Fin 2)
    (a' : NativeLie) (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (f g : Profile) :
    inner ℂ (inclusion (completedLeg left a s f))
      (reader gradeZeroProjection
        (CanonicalPhysicalWard.vertex p k a' cut z w hz hw
          (inclusion (completedLeg right b t g)))) =
    inner ℂ (inclusion (completedLeg left a s f))
      (reader gradeZeroProjection
        (CanonicalPhysicalResolvent.sourceResolvent (p+k) z hz
          (reader (chargeReader a')
            (CanonicalPhysicalResolvent.sourceResolvent p w hw
              (inclusion (completedLeg right b t g)))))) := by
  have base := congrArg
    (inner ℂ (inclusion (completedLeg left a s f)))
    (congrArg (fun T : HistorySpace →L[ℂ] HistorySpace =>
      T (inclusion (completedLeg right b t g)))
      (grade_zero_vertex_return p k a' cut z w hz hw))
  simp only [mul_apply_eq_comp] at base
  exact base

/-- On kernel legs the projection is invisible: the projected full
vertex pairing equals the unprojected one, so the return above is a
genuine identification of the leg-level vertex. -/
theorem prepared_full_vertex_leg (left right : Bool) (a s b t : Fin 2)
    (a' : NativeLie) (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (f g : ScalarTest) :
    inner ℂ (inclusion (completedLeg left a s (core f)))
      (reader gradeZeroProjection
        (CanonicalPhysicalWard.vertex p k a' cut z w hz hw
          (inclusion (completedLeg right b t (core g))))) =
    preparedFullVertex left right a s b t a' p k cut z w hz hw (core f) (core g) := by
  unfold preparedFullVertex
  rw [← grade_zero_history_pair]
  have fixed := source_leg_grade_zero_fixed left a s (seedSection f) _
    (seedSection_apply f)
  rw [← completedLeg_core] at fixed
  rw [fixed]

/-- The electromagnetic channel vertex between complete resolvents:
`nativeY` is the proven charge direction, not a chosen label. -/
def emFullVertex (left right : Bool) (a s b t : Fin 2)
    (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (f g : Profile) : ℂ :=
  preparedFullVertex left right a s b t nativeY p k cut z w hz hw f g

/-- The electromagnetic channel Ward between complete resolvents. -/
theorem em_full_ward (left right : Bool) (a s b t : Fin 2)
    (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (f g : Profile) :
    (z-w)*emFullVertex left right a s b t p k cut z w hz hw f g =
    inner ℂ (inclusion (completedLeg left a s f))
      (CanonicalPhysicalYResolvent.fullResolvent (p+k) cut z hz
        (reader (chargeReader nativeY) (inclusion (completedLeg right b t g))))-
    inner ℂ (inclusion (completedLeg left a s f))
      (reader (chargeReader nativeY) (CanonicalPhysicalYResolvent.fullResolvent p cut w hw
        (inclusion (completedLeg right b t g))))+
    inner ℂ (inclusion (completedLeg left a s f))
      (CanonicalPhysicalWard.response p k nativeY cut z w hz hw
        (inclusion (completedLeg right b t g))) :=
  prepared_full_ward left right a s b t nativeY p k cut z w hz hw f g

/-- The projected electromagnetic vertex equals the projected physical
vertex: cutoff independence of the channel carrier. -/
theorem em_full_vertex_projected (left right : Bool) (a s b t : Fin 2)
    (p k : PhysicalMomentum) (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (f g : Profile) :
    inner ℂ (inclusion (completedLeg left a s f))
      (reader gradeZeroProjection
        (CanonicalPhysicalWard.vertex p k nativeY cut z w hz hw
          (inclusion (completedLeg right b t g)))) =
    inner ℂ (inclusion (completedLeg left a s f))
      (reader gradeZeroProjection
        (CanonicalPhysicalResolvent.sourceResolvent (p+k) z hz
          (reader (chargeReader nativeY)
            (CanonicalPhysicalResolvent.sourceResolvent p w hw
              (inclusion (completedLeg right b t g)))))) :=
  prepared_full_vertex_projected left right a s b t nativeY p k cut z w hz hw f g

/-- The four-channel electromagnetic Ward core on kernel-level prepared
legs: configuration torque, channel current, quartic pair current and
Yukawa torque at the proven charge direction. -/
def emCoreChannels (k : PhysicalMomentum) (f g : QuantumTest) : ℂ :=
  PreparationVacuumFullElectricWard.coreChannels k nativeY f g

/-- The four channels sum to the single Ward-core pairing. -/
theorem em_core_channels_source (k : PhysicalMomentum) (f g : QuantumTest) :
    emCoreChannels k f g =
      GaussFockPair.sourcePair f
        (PreparationVacuumFullElectricWard.wardCore k nativeY g) :=
  PreparationVacuumFullElectricWard.coreChannels_source k nativeY f g

/-- The explicit four-term split of the electromagnetic Ward core. -/
theorem em_core_channels_split (k : PhysicalMomentum) (f g : QuantumTest) :
    emCoreChannels k f g =
      GaussFockPair.sourcePair f
        (CanonicalPhysicalWardCore.configurationTorque nativeY g)+
      GaussFockPair.sourcePair f
        (CanonicalPhysicalWardCore.currentAction k nativeY g)+
      GaussFockPair.sourcePair f
        (PreparationVacuumFullElectricWard.pairCurrent k nativeY g)+
      GaussFockPair.sourcePair f
        (PreparationVacuumFullElectricWard.yukawaTorque nativeY g) := by
  simp only [emCoreChannels,PreparationVacuumFullElectricWard.coreChannels]

/-- On actual prepared kernel legs the full insertion pairing splits
exactly into the four channel reads plus the explicit finite-truncation
Ward defect: `L = embed l` and `R = embed r` remove both residual
terms in `transportRemainder`. -/
theorem em_insertion_kernel (p k : PhysicalMomentum) (cut : ℕ) (F : Index)
    (f g : ScalarTest) :
    inner ℂ (embed (seedSection f))
      (CanonicalPhysicalWard.finiteInsertion p k nativeY cut F (embed (seedSection g))) =
    emCoreChannels k (seedSection f) (seedSection g)+
      inner ℂ (embed (seedSection f))
        (PreparationVacuumFullElectricWard.wardDefect p k nativeY cut F (seedSection g)) := by
  have h := PreparationVacuumFullElectricWard.insertion_actual_channels p k nativeY cut F
    (seedSection f) (seedSection g) (embed (seedSection f)) (embed (seedSection g))
  simp only [PreparationVacuumFullElectricWard.transportRemainder, sub_self,
    map_zero, inner_zero_left, inner_zero_right, add_zero] at h
  exact h

end LowEnergy.GaussComposite.PhysicalCharge
