import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalGradedGaugeVariation

/-! The original grade-raising Yukawa cutoff is retained in the perturbed
finite family, then erased only by its actual left N1/G0 observation. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalGradedGaugeReturn
open SourceFiniteUnitary CanonicalGradedVariation CanonicalGradedCurrent
open SourceFamilyOperator
open GaussCoreHilbert
open GaussUnitaryHistory (HistorySpace Index reader sourceFilter)
open scoped Topology InnerProductSpace Interval
section Finite
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _

private theorem continuous_time (C : E →L[ℂ] E) : Continuous (SourceFiniteUnitary.time C) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (hasDerivAt_exp_smul_const ((-Complex.I) • C) t).continuousAt)

theorem left_time_return (C A P : E →L[ℂ] E) (preserves : Commute P C)
    (annihilates : P*A=0) (t : ℝ) : P * SourceFiniteUnitary.time (C+A) t = P * SourceFiniteUnitary.time C t := by
  let f := fun s : ℝ => SourceFiniteUnitary.time C s * ((-Complex.I) • (C-(C+A))) * SourceFiniteUnitary.time (C+A) (t-s)
  have hf : IntervalIntegrable f MeasureTheory.volume 0 t :=
    (((continuous_time C).mul continuous_const).mul
      ((continuous_time (C+A)).comp (continuous_const.sub continuous_id))).intervalIntegrable 0 t
  let L := ContinuousLinearMap.mul ℂ (E →L[ℂ] E) P
  have hz (s : ℝ) : L (f s)=0 := by
    change P * (SourceFiniteUnitary.time C s * ((-Complex.I) • (C-(C+A))) * SourceFiniteUnitary.time (C+A) (t-s))=0
    have sub : C-(C+A) = -A := by abel
    rw [sub, ← mul_assoc, ← mul_assoc, (time_commutes C P preserves s).eq]
    simp only [mul_assoc, mul_smul_comm, mul_neg, annihilates, neg_zero, smul_zero, mul_zero, zero_mul]
  have h := L.intervalIntegral_comp_comm hf
  have hi : P*differenceIntegral (C+A) C t=0 := by
    change (∫ s in (0 : ℝ)..t, L (f s))=P*differenceIntegral (C+A) C t at h
    simp_rw [hz] at h
    simpa only [intervalIntegral.integral_zero] using h.symm
  rw [← time_difference] at hi
  rw [mul_sub, sub_eq_zero] at hi
  exact hi.symm

end Finite

open CanonicalGradedGaugeVariation
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open FullYSourceCutoffVolterra
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) :=
  NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _

private theorem gauge_projection (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie) :
    Commute sourceProjection (gaugeReader z mu a) :=
  boundedMatrix_blocks (gaugeMatrix z mu a) (gaugeMatrix_preserves z mu a) sourceLabel

theorem cutoff_projection (cut : ℕ) : sourceProjection*cutoff cut=0 := by
  apply positive_grade_left_zero _ 1 _ (by omega)
  simpa only [Nat.cast_one, one_smul] using cutoff_raises cut

private theorem perturbed_selfAdjoint (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie)
    (parameter : ℝ) (F : Index) :
    IsSelfAdjoint (GaussGradedCompression.compression F+parameter • gaugeReader z mu a) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (GaussGradedCompression.compression F x+parameter • gaugeReader z mu a x) y =
    inner ℂ x (GaussGradedCompression.compression F y+parameter • gaugeReader z mu a y)
  rw [inner_add_left, inner_add_right, inner_smul_left_eq_star_smul, inner_smul_right_eq_smul]
  have hc := GaussGradedCompression.compression_pair F x y
  change inner ℂ (GaussGradedCompression.compression F x) y=
    inner ℂ x (GaussGradedCompression.compression F y) at hc
  have hb := (gaugeReader_selfAdjoint z mu a).isSymmetric x y
  change inner ℂ (gaugeReader z mu a x) y=inner ℂ x (gaugeReader z mu a y) at hb
  rw [hc, hb]
  rfl

private theorem perturbed_projection (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie)
    (parameter : ℝ) (F : Index) :
    Commute sourceProjection (GaussGradedCompression.compression F+parameter • gaugeReader z mu a) := by
  apply ContinuousLinearMap.ext
  intro x
  have hc := congrArg (fun T : H →L[ℂ] H => T x)
    (GaussGradedCompression.compression_commutes F sourceLabel).eq
  have hb := congrArg (fun T : H →L[ℂ] H => T x) (gauge_projection z mu a).eq
  change sourceProjection (GaussGradedCompression.compression F x)=
    GaussGradedCompression.compression F (sourceProjection x) at hc
  change sourceProjection (gaugeReader z mu a x)=gaugeReader z mu a (sourceProjection x) at hb
  change sourceProjection (GaussGradedCompression.compression F x+parameter • gaugeReader z mu a x)=
    GaussGradedCompression.compression F (sourceProjection x)+parameter • gaugeReader z mu a (sourceProjection x)
  rw [map_add, LinearMapClass.map_smul_of_tower, hc, hb]

theorem finite_parameter_return (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie)
    (cut : ℕ) (parameter t : ℝ) (F : Index) :
    sourceProjection * SourceFiniteUnitary.time
      (GaussGradedCompression.compression F+parameter • gaugeReader z mu a+cutoff cut) t =
    sourceProjection * SourceFiniteUnitary.time
      (GaussGradedCompression.compression F+parameter • gaugeReader z mu a) t :=
  left_time_return _ _ sourceProjection
    (perturbed_projection z mu a parameter F) (cutoff_projection cut) t

/-- This family keeps the literal source cutoff in every finite component. -/
def fullProjectedFamily (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie)
    (cut : ℕ) (parameter t : ℝ) : Operator Index H where
  component F := sourceProjection * SourceFiniteUnitary.time
    (GaussGradedCompression.compression F+parameter • gaugeReader z mu a+cutoff cut) t
  bounded := ⟨1, zero_le_one, fun F x => by
    rw [finite_parameter_return]
    change ‖sourceProjection (SourceFiniteUnitary.time
      (GaussGradedCompression.compression F+parameter • gaugeReader z mu a) t x)‖ ≤ 1*‖x‖
    rw [one_mul]
    exact (NativeHistoryGrade.piece_bound sourceLabel _).trans_eq
      (SourceFiniteUnitary.time_norm _
        ((GaussGradedCompression.compression_selfAdjoint F).add
          ((IsSelfAdjoint.all parameter).smul (gaugeReader_selfAdjoint z mu a))) t x)⟩

def fullProjected (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie)
    (cut : ℕ) (parameter t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (fullProjectedFamily z mu a cut parameter t)

theorem fullProjected_return (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie)
    (cut : ℕ) (parameter t : ℝ) :
    fullProjected z mu a cut parameter t = historyProjection * gaugeTime z mu a parameter t := by
  change lift sourceFilter (fullProjectedFamily z mu a cut parameter t) =
    lift sourceFilter (constant sourceProjection) * lift sourceFilter _
  exact (lift_congr sourceFilter _
    (comp (constant sourceProjection) (CanonicalGradedVariation.timeFamily
      GaussGradedCompression.compression GaussGradedCompression.compression_selfAdjoint
      (gaugeReader z mu a) (gaugeReader_selfAdjoint z mu a) parameter t))
    (fun F => finite_parameter_return z mu a cut parameter t F)).trans (lift_comp sourceFilter _ _)

theorem fullProjected_original (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie)
    (cut : ℕ) (t : ℝ) :
    fullProjected z mu a cut 0 t=historyProjection * sourceEvolution cut t := by
  rw [fullProjected_return, gaugeTime_zero_parameter, cutoff_left_return]

set_option synthInstance.maxHeartbeats 200000 in
theorem fullProjected_derivative (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie)
    (cut : ℕ) (t : ℝ) :
    HasDerivAt (fun parameter : ℝ => fullProjected z mu a cut parameter t)
      (historyProjection * gaugeVariation z mu a t) 0 := by
  have h := (gaugeTime_derivative z mu a t).const_mul historyProjection
  simp_rw [fullProjected_return]
  exact h

private theorem two_leg_return {R : Type*} [Monoid R]
    (P U V W Z A : R) (left : P*U=P*V) (right : P*W=P*Z)
    (time_preserves : Commute P V) (reader_preserves : Commute P A) :
    P*U*A*W=P*V*A*Z := by
  calc
    _ = (P*V)*A*W := by rw [left]
    _ = V*A*(P*W) := by rw [time_preserves.eq]; simp only [mul_assoc, reader_preserves.eq]
    _ = V*A*(P*Z) := by rw [right]
    _ = _ := by rw [time_preserves.eq]; simp only [mul_assoc, reader_preserves.eq]

def finiteCurrent (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (parameter t : ℝ) (F : Index) : H →L[ℂ] H :=
  let C := GaussGradedCompression.compression F+parameter • gaugeReader z nu b+cutoff cut
  sourceProjection * SourceFiniteUnitary.time C (-t) * gaugeReader z mu a * SourceFiniteUnitary.time C t

theorem finiteCurrent_return (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (parameter t : ℝ) (F : Index) :
    finiteCurrent z mu nu a b cut parameter t F =
      sourceProjection * SourceFiniteUnitary.time
        (GaussGradedCompression.compression F+parameter • gaugeReader z nu b) (-t) * gaugeReader z mu a *
        SourceFiniteUnitary.time (GaussGradedCompression.compression F+parameter • gaugeReader z nu b) t :=
  two_leg_return _ _ _ _ _ _ (finite_parameter_return z nu b cut parameter (-t) F)
    (finite_parameter_return z nu b cut parameter t F)
    (SourceFiniteUnitary.time_commutes _ _ (perturbed_projection z nu b parameter F) (-t))
    (gauge_projection z mu a)

def fullCurrentFamily (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (parameter t : ℝ) : Operator Index H where
  component F := finiteCurrent z mu nu a b cut parameter t F
  bounded := ⟨‖gaugeReader z mu a‖, norm_nonneg _, fun F x => by
    rw [finiteCurrent_return]
    let C := GaussGradedCompression.compression F+parameter • gaugeReader z nu b
    have hc : IsSelfAdjoint C := perturbed_selfAdjoint z nu b parameter F
    change ‖sourceProjection (SourceFiniteUnitary.time C (-t)
      (gaugeReader z mu a (SourceFiniteUnitary.time C t x)))‖ ≤ ‖gaugeReader z mu a‖*‖x‖
    calc
      _ ≤ ‖SourceFiniteUnitary.time C (-t) (gaugeReader z mu a (SourceFiniteUnitary.time C t x))‖ :=
        NativeHistoryGrade.piece_bound sourceLabel _
      _ = ‖gaugeReader z mu a (SourceFiniteUnitary.time C t x)‖ := SourceFiniteUnitary.time_norm C hc (-t) _
      _ ≤ ‖gaugeReader z mu a‖*‖SourceFiniteUnitary.time C t x‖ := (gaugeReader z mu a).le_opNorm _
      _ = _ := by rw [SourceFiniteUnitary.time_norm C hc]⟩

def fullCurrent (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (parameter t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (fullCurrentFamily z mu nu a b cut parameter t)

theorem fullCurrent_return (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (parameter t : ℝ) :
    fullCurrent z mu nu a b cut parameter t=historyProjection * currentOperator z mu nu a b parameter t := by
  let T := CanonicalGradedVariation.timeFamily GaussGradedCompression.compression
    GaussGradedCompression.compression_selfAdjoint (gaugeReader z nu b) (gaugeReader_selfAdjoint z nu b) parameter
  have h := lift_congr sourceFilter (fullCurrentFamily z mu nu a b cut parameter t)
    (comp (comp (comp (constant sourceProjection) (T (-t))) (constant (gaugeReader z mu a))) (T t))
    (fun F => finiteCurrent_return z mu nu a b cut parameter t F)
  rw [lift_comp, lift_comp, lift_comp] at h
  change fullCurrent z mu nu a b cut parameter t =
    historyProjection * gaugeTime z nu b parameter (-t) * reader (gaugeReader z mu a) *
      gaugeTime z nu b parameter t at h
  simpa only [currentOperator, mul_assoc] using h

def fullObservation (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (parameter t : ℝ) (x y : HistorySpace) : ℂ :=
  inner ℂ x (fullCurrent z mu nu a b cut parameter t (historyProjection y))

theorem fullObservation_return (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (parameter t : ℝ) (x y : HistorySpace) :
    fullObservation z mu nu a b cut parameter t x y=currentObservation z mu nu a b parameter t x y := by
  rw [fullObservation, fullCurrent_return]
  exact (projection_pair x (currentOperator z mu nu a b parameter t (historyProjection y))).symm

set_option synthInstance.maxHeartbeats 200000 in
theorem fullObservation_derivative (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (t : ℝ) (x y : HistorySpace) :
    HasDerivAt (fun parameter : ℝ => fullObservation z mu nu a b cut parameter t x y)
      (inner ℂ (historyProjection x) (currentDerivative z mu nu a b t (historyProjection y))) 0 := by
  simp_rw [fullObservation_return]
  exact currentObservation_derivative z mu nu a b t x y

theorem fullObservation_cutoff_independent (z : SourceCoordinateSlice) (mu nu : Component)
    (a b : NativeLie) (cut other : ℕ) (parameter t : ℝ) (x y : HistorySpace) :
    fullObservation z mu nu a b cut parameter t x y=fullObservation z mu nu a b other parameter t x y := by
  rw [fullObservation_return, fullObservation_return]

#print axioms fullObservation_derivative
#print axioms fullObservation_cutoff_independent

#print axioms finite_parameter_return
#print axioms fullProjected_derivative
end LowEnergy.CanonicalGradedGaugeReturn
