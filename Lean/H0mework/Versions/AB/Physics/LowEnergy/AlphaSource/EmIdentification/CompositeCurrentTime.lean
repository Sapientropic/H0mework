import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeGradeProjection

/-! Full literal-Y configuration-current time for the original G=0 readout,
retaining every Number sector and the unchanged source filter. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite
open GaussCoreHilbert SourceFamilyOperator
open SourceQuantumScalarChart CanonicalGradedCurrent CanonicalGradedLocalCurrent
open GaussUnitaryHistory (HistorySpace Index sourceFilter reader)
open FullYSourceCutoffVolterra
open scoped InnerProductSpace Topology
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

theorem grade_zero_projection_bound (x : H) : ‖gradeZeroProjection x‖≤‖x‖ := grade_zero_piece_bound x

theorem grade_zero_compression (F : Index) : Commute gradeZeroProjection (GaussGradedCompression.compression F) :=
  grade_zero_commutes _ (GaussGradedCompression.compression_commutes F)

theorem grade_zero_current (phi : Localizer) (mu : Component) (a : NativeLie) :
    Commute gradeZeroProjection (localReader phi mu a) :=
  grade_zero_commutes _ (localReader_blocks phi mu a)

theorem grade_zero_perturbed (phi : Localizer) (mu : Component) (a : NativeLie)
    (parameter : ℝ) (F : Index) :
    Commute gradeZeroProjection (GaussGradedCompression.compression F+parameter • localReader phi mu a) :=
  by
    apply ContinuousLinearMap.ext
    intro x
    have hc := congrArg (fun T : H →L[ℂ] H => T x) (grade_zero_compression F).eq
    have hb := congrArg (fun T : H →L[ℂ] H => T x) (grade_zero_current phi mu a).eq
    change gradeZeroProjection (GaussGradedCompression.compression F x)=
      GaussGradedCompression.compression F (gradeZeroProjection x) at hc
    change gradeZeroProjection (localReader phi mu a x)=localReader phi mu a (gradeZeroProjection x) at hb
    change gradeZeroProjection (GaussGradedCompression.compression F x+parameter • localReader phi mu a x)=
      GaussGradedCompression.compression F (gradeZeroProjection x)+parameter • localReader phi mu a (gradeZeroProjection x)
    rw [map_add,LinearMapClass.map_smul_of_tower,hc,hb]

theorem grade_zero_finite_time (phi : Localizer) (mu : Component) (a : NativeLie)
    (cut : ℕ) (parameter t : ℝ) (F : Index) :
    gradeZeroProjection*SourceFiniteUnitary.time
      (GaussGradedCompression.compression F+parameter • localReader phi mu a+cutoff cut) t =
    gradeZeroProjection*SourceFiniteUnitary.time
      (GaussGradedCompression.compression F+parameter • localReader phi mu a) t :=
  CanonicalGradedGaugeReturn.left_time_return _ _ gradeZeroProjection
    (grade_zero_perturbed phi mu a parameter F) (grade_zero_cutoff cut) t

private theorem current_two_leg {R : Type*} [Monoid R] (P U V W Z A : R)
    (left : P*U=P*V) (right : P*W=P*Z) (time : Commute P V) (current : Commute P A) :
    P*U*A*W=P*V*A*Z := by
  calc
    _ = (P*V)*A*W := by rw [left]
    _ = V*A*(P*W) := by rw [time.eq]; simp only [mul_assoc,current.eq]
    _ = V*A*(P*Z) := by rw [right]
    _ = _ := by rw [time.eq]; simp only [mul_assoc,current.eq]

def fullCurrentFinite (phi psi : Localizer) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (parameter t : ℝ) (F : Index) : H →L[ℂ] H :=
  let C := GaussGradedCompression.compression F+parameter • localReader psi nu b+cutoff cut
  gradeZeroProjection*SourceFiniteUnitary.time C (-t)*localReader phi mu a*SourceFiniteUnitary.time C t

theorem full_current_finite_return (phi psi : Localizer) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (parameter t : ℝ) (F : Index) :
    fullCurrentFinite phi psi mu nu a b cut parameter t F =
      gradeZeroProjection*SourceFiniteUnitary.time
        (GaussGradedCompression.compression F+parameter • localReader psi nu b) (-t)*
          localReader phi mu a*SourceFiniteUnitary.time
            (GaussGradedCompression.compression F+parameter • localReader psi nu b) t := by
  apply current_two_leg gradeZeroProjection _ _ _ _ (localReader phi mu a)
    (grade_zero_finite_time psi nu b cut parameter (-t) F)
    (grade_zero_finite_time psi nu b cut parameter t F)
    (SourceFiniteUnitary.time_commutes _ _ (grade_zero_perturbed psi nu b parameter F) (-t))
    (grade_zero_current phi mu a)

theorem full_current_finite_bound (phi psi : Localizer) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (parameter t : ℝ) (F : Index) (x : H) :
    ‖fullCurrentFinite phi psi mu nu a b cut parameter t F x‖≤bound phi mu a*‖x‖ := by
  rw [full_current_finite_return]
  let C := GaussGradedCompression.compression F+parameter • localReader psi nu b
  have symmetric : IsSelfAdjoint C := by
    dsimp only [C]
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro u v
    change inner ℂ (GaussGradedCompression.compression F u+parameter • localReader psi nu b u) v =
      inner ℂ u (GaussGradedCompression.compression F v+parameter • localReader psi nu b v)
    rw [inner_add_left,inner_add_right,inner_smul_left_eq_star_smul,inner_smul_right_eq_smul]
    have hc := GaussGradedCompression.compression_pair F u v
    change inner ℂ (GaussGradedCompression.compression F u) v=
      inner ℂ u (GaussGradedCompression.compression F v) at hc
    have hb := (localReader_selfAdjoint psi nu b).isSymmetric u v
    change inner ℂ (localReader psi nu b u) v=inner ℂ u (localReader psi nu b v) at hb
    rw [hc,hb]
    rfl
  change ‖gradeZeroProjection (SourceFiniteUnitary.time C (-t)
    (localReader phi mu a (SourceFiniteUnitary.time C t x)))‖≤_
  calc
    _ ≤ ‖SourceFiniteUnitary.time C (-t) (localReader phi mu a (SourceFiniteUnitary.time C t x))‖ :=
      grade_zero_projection_bound _
    _ = ‖localReader phi mu a (SourceFiniteUnitary.time C t x)‖ := SourceFiniteUnitary.time_norm C symmetric (-t) _
    _ ≤ bound phi mu a*‖SourceFiniteUnitary.time C t x‖ :=
      ((localReader phi mu a).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (localReader_norm phi mu a) (norm_nonneg _))
    _ = _ := by rw [SourceFiniteUnitary.time_norm C symmetric]

def fullCurrentFamily (phi psi : Localizer) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (parameter t : ℝ) : Operator Index H where
  component := fullCurrentFinite phi psi mu nu a b cut parameter t
  bounded := ⟨bound phi mu a,bound_nonnegative phi mu a,
    fun F x => full_current_finite_bound phi psi mu nu a b cut parameter t F x⟩

def fullCurrent (phi psi : Localizer) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (parameter t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (fullCurrentFamily phi psi mu nu a b cut parameter t)

theorem full_current_return (phi psi : Localizer) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (parameter t : ℝ) :
    fullCurrent phi psi mu nu a b cut parameter t =
      reader gradeZeroProjection*currentOperator phi psi mu nu a b parameter t := by
  let timeFamily := CanonicalGradedVariation.timeFamily GaussGradedCompression.compression
    GaussGradedCompression.compression_selfAdjoint (localReader psi nu b)
      (localReader_selfAdjoint psi nu b) parameter
  calc
    _ = lift sourceFilter (comp (constant gradeZeroProjection)
      (comp (timeFamily (-t)) (comp (constant (localReader phi mu a)) (timeFamily t)))) := by
      apply lift_congr
      intro F
      change fullCurrentFinite phi psi mu nu a b cut parameter t F =
        gradeZeroProjection*(SourceFiniteUnitary.time
          (GaussGradedCompression.compression F+parameter • localReader psi nu b) (-t)*
          (localReader phi mu a*SourceFiniteUnitary.time
            (GaussGradedCompression.compression F+parameter • localReader psi nu b) t))
      simpa only [mul_assoc] using full_current_finite_return phi psi mu nu a b cut parameter t F
    _ = _ := by
      rw [lift_comp,lift_comp,lift_comp]
      change reader gradeZeroProjection*(localTime psi nu b parameter (-t)*
        (reader (localReader phi mu a)*localTime psi nu b parameter t)) = _
      simp only [currentOperator,mul_assoc]

theorem full_current_derivative (phi psi : Localizer) (mu nu : Component) (a b : NativeLie)
    (cut : ℕ) (t : ℝ) :
    HasDerivAt (fun parameter : ℝ => fullCurrent phi psi mu nu a b cut parameter t)
      (reader gradeZeroProjection*currentDerivative phi psi mu nu a b t) 0 := by
  simp only [full_current_return]
  exact (currentOperator_derivative phi psi mu nu a b t).const_mul (reader gradeZeroProjection)

end LowEnergy.GaussComposite
