import H0mework.Physics.Admission.EmpiricalReferenceScaleCouplingBoundary
import H0mework.Physics.Source.GeneratedPhysicalPlebanskiConfiguration

/-!
# Dynamic tetrad-generated gauge geometry

This module supplies the first nonseparable Stage-5 mouth.  A gravity tetrad
is compared with the exact source-generated tetrad at the origin.  Its
time-axis deformation `s` generates the everywhere-positive coframe scale

`ρ(s) = s² + s + 1`.

The resulting diagonal coframe `diag(ρ,1,1,1)` has volume `ρ`, and its
coordinate two-form Hodge operator is

`(F01,F02,F03,F23,F31,F12)
  ↦ (ρF23,ρF31,ρF12,-ρ⁻¹F01,-ρ⁻¹F02,-ρ⁻¹F03)`.

This Hodge squares to `-id` and varies genuinely with the gravity tetrad.  All
three empirical gauge constitutive operators are built from this same Hodge.

Boundary: this is the exact time-axis diagonal coframe subfamily, not yet the
full arbitrary `GL(4)` coframe Hodge formula.  It is an aligned intermediate
producer toward the full Stage-5 hard gate and must not be cited as that final
general-coframe result.
-/

namespace SaturationMonoid.PhysicsCore.DynamicTetradGaugeGeometry

open ProofFreeRicherAnholonomicSource
open PhysicalIIPlusFrechetVariation
open SourceGeneratedPhysicalPlebanskiConfiguration
open EmpiricalReferenceScaleCouplingBoundary
open scoped RealInnerProductSpace

noncomputable section

abbrev GaugeTwoFormVector := LorentzianTwoForm

/-- Gravity-tetrad displacement in the selected time-axis coframe mode. -/
def tetradGaugeMode (source : Source) (tetrad : TetradVector) : ℝ :=
  tetrad (0, 0) - tetradVectorAtOrigin source (0, 0)

/-- Globally positive polynomial scale.  Its derivative at the source mode
is nonzero, unlike the even surrogate `1+s²`. -/
def dynamicGaugeScale (source : Source) (tetrad : TetradVector) : ℝ :=
  let mode := tetradGaugeMode source tetrad
  mode ^ 2 + mode + 1

@[fun_prop] theorem tetradGaugeMode_contDiff (source : Source) :
    ContDiff ℝ ⊤ (tetradGaugeMode source) := by
  unfold tetradGaugeMode
  fun_prop

@[fun_prop] theorem dynamicGaugeScale_contDiff (source : Source) :
    ContDiff ℝ ⊤ (dynamicGaugeScale source) := by
  unfold dynamicGaugeScale
  fun_prop

theorem dynamicGaugeScale_pos (source : Source) (tetrad : TetradVector) :
    0 < dynamicGaugeScale source tetrad := by
  let mode := tetradGaugeMode source tetrad
  have hsquare : 0 ≤ (mode + (1 / 2 : ℝ)) ^ 2 := sq_nonneg _
  change 0 < mode ^ 2 + mode + 1
  nlinarith

theorem dynamicGaugeScale_ne_zero (source : Source) (tetrad : TetradVector) :
    dynamicGaugeScale source tetrad ≠ 0 :=
  ne_of_gt (dynamicGaugeScale_pos source tetrad)

/-- Exact dynamic coframe represented by this Stage-5 subfamily. -/
def dynamicGaugeCoframe
    (source : Source) (tetrad : TetradVector) : LorentzianCoframe :=
  Matrix.diagonal
    ![dynamicGaugeScale source tetrad, (1 : ℝ), (1 : ℝ), (1 : ℝ)]

/-- The volume is computed from the generated coframe, not supplied as a
separate gauge-sector parameter. -/
def dynamicGaugeVolume (source : Source) (tetrad : TetradVector) : ℝ :=
  dynamicGaugeScale source tetrad

@[simp] theorem dynamicGaugeVolume_eq_scale
    (source : Source) (tetrad : TetradVector) :
    dynamicGaugeVolume source tetrad = dynamicGaugeScale source tetrad := by
  rfl

theorem dynamicGaugeCoframe_det
    (source : Source) (tetrad : TetradVector) :
    Matrix.det (dynamicGaugeCoframe source tetrad) =
      dynamicGaugeVolume source tetrad := by
  simp [dynamicGaugeVolume, dynamicGaugeCoframe, Fin.prod_univ_succ]

@[fun_prop] theorem dynamicGaugeVolume_contDiff (source : Source) :
    ContDiff ℝ ⊤ (dynamicGaugeVolume source) := by
  exact dynamicGaugeScale_contDiff source

theorem dynamicGaugeVolume_pos (source : Source) (tetrad : TetradVector) :
    0 < dynamicGaugeVolume source tetrad := by
  rw [dynamicGaugeVolume_eq_scale]
  exact dynamicGaugeScale_pos source tetrad

/-- Coordinate Hodge map of the generated diagonal Lorentz coframe. -/
def dynamicGaugeHodgeLinear
    (source : Source) (tetrad : TetradVector) :
    GaugeTwoFormVector →ₗ[ℝ] GaugeTwoFormVector where
  toFun := fun form =>
    let scale := dynamicGaugeScale source tetrad
    ![scale * form 3,
      scale * form 4,
      scale * form 5,
      -(scale⁻¹ * form 0),
      -(scale⁻¹ * form 1),
      -(scale⁻¹ * form 2)]
  map_add' := by
    intro first second
    ext index
    fin_cases index <;> simp <;> ring
  map_smul' := by
    intro scalar form
    ext index
    fin_cases index <;> simp <;> ring

/-- Continuous-linear packaging at a fixed gravity tetrad. -/
def dynamicGaugeHodgeCLM
    (source : Source) (tetrad : TetradVector) :
    GaugeTwoFormVector →L[ℝ] GaugeTwoFormVector :=
  ⟨dynamicGaugeHodgeLinear source tetrad,
    (dynamicGaugeHodgeLinear source tetrad).continuous_of_finiteDimensional⟩

@[simp] theorem dynamicGaugeHodgeCLM_apply
    (source : Source) (tetrad : TetradVector)
    (form : GaugeTwoFormVector) :
    dynamicGaugeHodgeCLM source tetrad form =
      dynamicGaugeHodgeLinear source tetrad form :=
  rfl

@[fun_prop] theorem dynamicGaugeHodge_joint_contDiff (source : Source) :
    ContDiff ℝ ⊤
      (fun pair : TetradVector × GaugeTwoFormVector =>
        dynamicGaugeHodgeLinear source pair.1 pair.2) := by
  have hscale :
      ContDiff ℝ ⊤
        (fun pair : TetradVector × GaugeTwoFormVector =>
          dynamicGaugeScale source pair.1) :=
    (dynamicGaugeScale_contDiff source).comp contDiff_fst
  have hinverse :
      ContDiff ℝ ⊤
        (fun pair : TetradVector × GaugeTwoFormVector =>
          (dynamicGaugeScale source pair.1)⁻¹) :=
    hscale.inv (fun pair => dynamicGaugeScale_ne_zero source pair.1)
  apply contDiff_pi'
  intro index
  fin_cases index
  · simpa [dynamicGaugeHodgeLinear] using hscale.mul (by fun_prop :
      ContDiff ℝ ⊤
        (fun pair : TetradVector × GaugeTwoFormVector => pair.2 3))
  · simpa [dynamicGaugeHodgeLinear] using hscale.mul (by fun_prop :
      ContDiff ℝ ⊤
        (fun pair : TetradVector × GaugeTwoFormVector => pair.2 4))
  · simpa [dynamicGaugeHodgeLinear] using hscale.mul (by fun_prop :
      ContDiff ℝ ⊤
        (fun pair : TetradVector × GaugeTwoFormVector => pair.2 5))
  · simpa [dynamicGaugeHodgeLinear] using (hinverse.mul (by fun_prop :
      ContDiff ℝ ⊤
        (fun pair : TetradVector × GaugeTwoFormVector => pair.2 0))).neg
  · simpa [dynamicGaugeHodgeLinear] using (hinverse.mul (by fun_prop :
      ContDiff ℝ ⊤
        (fun pair : TetradVector × GaugeTwoFormVector => pair.2 1))).neg
  · simpa [dynamicGaugeHodgeLinear] using (hinverse.mul (by fun_prop :
      ContDiff ℝ ⊤
        (fun pair : TetradVector × GaugeTwoFormVector => pair.2 2))).neg

/-- Composition rule exposing the joint tetrad/form smoothness to `fun_prop`.
Both inputs remain live; fixed-tetrad and fixed-form slices follow by taking one
of the two maps to be constant. -/
@[fun_prop] theorem dynamicGaugeHodge_comp_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (source : Source) {tetrad : E → TetradVector}
    {form : E → GaugeTwoFormVector}
    (htetrad : ContDiff ℝ ⊤ tetrad)
    (hform : ContDiff ℝ ⊤ form) :
    ContDiff ℝ ⊤
      (fun x => dynamicGaugeHodgeCLM source (tetrad x) (form x)) := by
  simpa only [dynamicGaugeHodgeCLM_apply, Function.comp_def] using
    (dynamicGaugeHodge_joint_contDiff source).comp
      (htetrad.prodMk hform)

@[simp] theorem dynamicGaugeHodgeLinear_square
    (source : Source) (tetrad : TetradVector)
    (form : GaugeTwoFormVector) :
    dynamicGaugeHodgeLinear source tetrad
        (dynamicGaugeHodgeLinear source tetrad form) = -form := by
  have hscale := dynamicGaugeScale_ne_zero source tetrad
  ext index
  fin_cases index <;>
    simp [dynamicGaugeHodgeLinear, hscale]

/-- Invertible Hodge operator generated from the same gravity tetrad. -/
def dynamicGaugeHodgeEquiv
    (source : Source) (tetrad : TetradVector) :
    GaugeTwoFormVector ≃ₗ[ℝ] GaugeTwoFormVector where
  toFun := dynamicGaugeHodgeLinear source tetrad
  invFun := fun form => -dynamicGaugeHodgeLinear source tetrad form
  left_inv := by
    intro form
    change
      -dynamicGaugeHodgeLinear source tetrad
          (dynamicGaugeHodgeLinear source tetrad form) = form
    rw [dynamicGaugeHodgeLinear_square]
    simp
  right_inv := by
    intro form
    rw [map_neg, dynamicGaugeHodgeLinear_square]
    simp
  map_add' := (dynamicGaugeHodgeLinear source tetrad).map_add
  map_smul' := (dynamicGaugeHodgeLinear source tetrad).map_smul

@[simp] theorem dynamicGaugeHodgeEquiv_apply
    (source : Source) (tetrad : TetradVector)
    (form : GaugeTwoFormVector) :
    dynamicGaugeHodgeEquiv source tetrad form =
      dynamicGaugeHodgeLinear source tetrad form :=
  rfl

/-- All three constitutive operators share the exact dynamic Hodge value. -/
def dynamicGaugeConstitutiveBlock
    (source : Source) (tetrad : TetradVector)
    (boundary : EmpiricalReferenceScaleCouplings) :
    StandardModelGaugeConstitutiveBlock ℝ GaugeTwoFormVector where
  spacetimeHodge := dynamicGaugeHodgeEquiv source tetrad
  strongCouplingSquared := boundary.strongCouplingSquared
  weakCouplingSquared := boundary.weakCouplingSquared
  hyperchargeCouplingSquared := boundary.hyperchargeCouplingSquared

def dynamicStrongOperator
    (source : Source) (tetrad : TetradVector)
    (boundary : EmpiricalReferenceScaleCouplings) :
    GaugeTwoFormVector ≃ₗ[ℝ] GaugeTwoFormVector :=
  (dynamicGaugeConstitutiveBlock source tetrad boundary).strongOperator

def dynamicWeakOperator
    (source : Source) (tetrad : TetradVector)
    (boundary : EmpiricalReferenceScaleCouplings) :
    GaugeTwoFormVector ≃ₗ[ℝ] GaugeTwoFormVector :=
  (dynamicGaugeConstitutiveBlock source tetrad boundary).weakOperator

def dynamicHyperchargeOperator
    (source : Source) (tetrad : TetradVector)
    (boundary : EmpiricalReferenceScaleCouplings) :
    GaugeTwoFormVector ≃ₗ[ℝ] GaugeTwoFormVector :=
  (dynamicGaugeConstitutiveBlock source tetrad boundary).hyperchargeOperator

theorem all_three_operators_share_dynamicHodge
    (source : Source) (tetrad : TetradVector)
    (boundary : EmpiricalReferenceScaleCouplings) :
    (dynamicGaugeConstitutiveBlock source tetrad boundary).spacetimeHodge =
        dynamicGaugeHodgeEquiv source tetrad ∧
      dynamicStrongOperator source tetrad boundary =
        hodgeConstitutiveOperator (dynamicGaugeHodgeEquiv source tetrad)
          boundary.strongCouplingSquared ∧
      dynamicWeakOperator source tetrad boundary =
        hodgeConstitutiveOperator (dynamicGaugeHodgeEquiv source tetrad)
          boundary.weakCouplingSquared ∧
      dynamicHyperchargeOperator source tetrad boundary =
        hodgeConstitutiveOperator (dynamicGaugeHodgeEquiv source tetrad)
          boundary.hyperchargeCouplingSquared :=
  ⟨rfl, rfl, rfl, rfl⟩

@[simp] theorem tetradGaugeMode_at_source (source : Source) :
    tetradGaugeMode source (tetradVectorAtOrigin source) = 0 := by
  simp [tetradGaugeMode]

@[simp] theorem dynamicGaugeScale_at_source (source : Source) :
    dynamicGaugeScale source (tetradVectorAtOrigin source) = 1 := by
  simp [dynamicGaugeScale]

@[simp] theorem dynamicGaugeVolume_at_source (source : Source) :
    dynamicGaugeVolume source (tetradVectorAtOrigin source) = 1 := by
  rw [dynamicGaugeVolume_eq_scale]
  exact dynamicGaugeScale_at_source source

theorem dynamicGaugeHodge_at_source
    (source : Source) :
    dynamicGaugeHodgeEquiv source (tetradVectorAtOrigin source) =
      lorentzianCoframeHodgeEquiv := by
  ext form index
  fin_cases index <;>
    simp [dynamicGaugeHodgeEquiv, dynamicGaugeHodgeLinear,
      lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge]

/-- A unit displacement of the gravity tetrad changes both generated volume
and Hodge.  This is the machine-level nonconstancy needed before coupling the
gauge action to tetrad variation. -/
def timeModeProbe (source : Source) : TetradVector :=
  tetradVectorAtOrigin source +
    EuclideanSpace.basisFun (LorentzianIndex × LorentzianIndex) ℝ (0, 0)

theorem timeModeProbe_mode (source : Source) :
    tetradGaugeMode source (timeModeProbe source) = 1 := by
  norm_num [tetradGaugeMode, timeModeProbe,
    EuclideanSpace.basisFun_apply]

theorem timeModeProbe_volume (source : Source) :
    dynamicGaugeVolume source (timeModeProbe source) = 3 := by
  rw [dynamicGaugeVolume_eq_scale]
  simp [dynamicGaugeScale, timeModeProbe_mode]
  ring

theorem dynamicGaugeHodge_not_constant (source : Source) :
    dynamicGaugeHodgeEquiv source (timeModeProbe source) ≠
      dynamicGaugeHodgeEquiv source (tetradVectorAtOrigin source) := by
  intro hequal
  have hvalue := congrArg
    (fun operator : GaugeTwoFormVector ≃ₗ[ℝ] GaugeTwoFormVector =>
      operator (fun index => if index = 3 then 1 else 0) 0)
    hequal
  norm_num [dynamicGaugeHodgeEquiv, dynamicGaugeHodgeLinear,
    dynamicGaugeScale, timeModeProbe_mode] at hvalue

end
end SaturationMonoid.PhysicsCore.DynamicTetradGaugeGeometry
