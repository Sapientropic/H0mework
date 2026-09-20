import H0mework.Physics.Geometry.DynamicBreakingVacuum
import H0mework.Physics.Admission.EmpiricalReferenceScaleCouplingBoundary

/-!
# Stage-9B typed blockwise constitutive operator

The positive Stage-9 source coframe now generates both sides of the
constitutive split without identifying their types.  The gravitational block
is the internal Lorentz bivector dual on
`PhysicalBivector = Λ²_internal ⊗ Λ²_spacetime`.  The gauge block is a
spacetime Hodge operator on `LorentzianTwoForm`, obtained by conjugating the
fixed orthonormal-frame Hodge with the actual exterior-square frame induced by
the source coframe.  The exterior-square identity is proved componentwise.

The three gauge operators use that one generated spacetime Hodge and the
independent empirical coupling boundary.  Thus `Kχ` is blockwise and typed:
source, coframe, and responsibility are unified, while gravity internal dual
and gauge spacetime Hodge remain distinct operators.
-/

namespace SaturationMonoid.PhysicsCore.StageNineBlockwiseConstitutive

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineEnrichedProofFreeSource
open EmpiricalReferenceScaleCouplingBoundary

noncomputable section

def gravityInternalDualLinear : PhysicalBivector →ₗ[ℝ] PhysicalBivector where
  toFun := internalBivectorDual
  map_add' := by
    intro first second
    funext internalPair spacetimePair
    fin_cases internalPair <;>
      simp [internalBivectorDual, lorentzianCoframeHodge] <;> abel
  map_smul' := by
    intro scalar bivector
    funext internalPair spacetimePair
    fin_cases internalPair <;>
      simp [internalBivectorDual, lorentzianCoframeHodge]

theorem gravityInternalDualLinear_square (bivector : PhysicalBivector) :
    gravityInternalDualLinear (gravityInternalDualLinear bivector) =
      -bivector := by
  funext internalPair spacetimePair
  fin_cases internalPair <;>
    simp [gravityInternalDualLinear, internalBivectorDual,
      lorentzianCoframeHodge]

def gravityInternalDualEquiv :
    PhysicalBivector ≃ₗ[ℝ] PhysicalBivector where
  toFun := gravityInternalDualLinear
  invFun := fun bivector => -gravityInternalDualLinear bivector
  left_inv := by
    intro bivector
    change -gravityInternalDualLinear (gravityInternalDualLinear bivector) = bivector
    rw [gravityInternalDualLinear_square]
    simp
  right_inv := by
    intro bivector
    change gravityInternalDualLinear (-gravityInternalDualLinear bivector) = bivector
    rw [map_neg, gravityInternalDualLinear_square]
    simp
  map_add' := gravityInternalDualLinear.map_add
  map_smul' := gravityInternalDualLinear.map_smul

abbrev GaugeTwoForm := LorentzianTwoForm

def positiveCoframeTwoFormFrame
    (point : BasePoint) : GaugeTwoForm ≃ₗ[ℝ] GaugeTwoForm where
  toFun := fun form =>
    ![form 0,
      form 1 + point 2 * form 5,
      form 2 - point 2 * form 4,
      form 3, form 4, form 5]
  invFun := fun form =>
    ![form 0,
      form 1 - point 2 * form 5,
      form 2 + point 2 * form 4,
      form 3, form 4, form 5]
  left_inv := by
    intro form
    ext index
    fin_cases index <;> simp
  right_inv := by
    intro form
    ext index
    fin_cases index <;> simp
  map_add' := by
    intro first second
    ext index
    fin_cases index <;> simp <;> ring
  map_smul' := by
    intro scalar form
    ext index
    fin_cases index <;> simp <;> ring

/-- The explicit two-form frame is exactly the exterior-square action of the
source-generated coframe, not an independent metric choice. -/
theorem positiveCoframeTwoFormFrame_eq_coframeWedge
    (point : BasePoint) (form : GaugeTwoForm) (internalPair : Fin 6) :
    positiveCoframeTwoFormFrame point form internalPair =
      ∑ spacetimePair : Fin 6,
        coframeWedge (canonicalPhysicalSource.coframeAt point)
          internalPair spacetimePair * form spacetimePair := by
  fin_cases internalPair <;>
    simp [positiveCoframeTwoFormFrame,
      canonicalPhysicalSource_coframeAt_eq_transvection,
      coframeWedge, pairFirst, pairSecond, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Fin.sum_univ_six]
  all_goals ring

def positiveGaugeSpacetimeHodge
    (point : BasePoint) : GaugeTwoForm ≃ₗ[ℝ] GaugeTwoForm :=
  (positiveCoframeTwoFormFrame point).trans
    (lorentzianCoframeHodgeEquiv.trans
      (positiveCoframeTwoFormFrame point).symm)

theorem positiveGaugeSpacetimeHodge_square
    (point : BasePoint) (form : GaugeTwoForm) :
    positiveGaugeSpacetimeHodge point
        (positiveGaugeSpacetimeHodge point form) = -form := by
  unfold positiveGaugeSpacetimeHodge
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hfixed := congrArg
    (fun operator : LorentzianTwoFormHodgeOperator =>
      operator (positiveCoframeTwoFormFrame point form))
    lorentzianCoframeHodge_square
  change (positiveCoframeTwoFormFrame point).symm
    (lorentzianCoframeHodgeEquiv
      (lorentzianCoframeHodgeEquiv
        (positiveCoframeTwoFormFrame point form))) = -form
  rw [show lorentzianCoframeHodgeEquiv
      (lorentzianCoframeHodgeEquiv
        (positiveCoframeTwoFormFrame point form)) =
      -(positiveCoframeTwoFormFrame point form) by exact hfixed]
  rw [map_neg, LinearEquiv.symm_apply_apply]

theorem positiveGaugeSpacetimeHodge_origin :
    positiveGaugeSpacetimeHodge 0 = lorentzianCoframeHodgeEquiv := by
  apply LinearEquiv.ext
  intro form
  ext index
  fin_cases index <;>
    simp [positiveGaugeSpacetimeHodge, positiveCoframeTwoFormFrame,
      lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge]

structure StageNineBlockwiseKChi where
  gravityInternalDual : PhysicalBivector ≃ₗ[ℝ] PhysicalBivector
  gaugeSpacetimeHodge : GaugeTwoForm ≃ₗ[ℝ] GaugeTwoForm
  strong : GaugeTwoForm ≃ₗ[ℝ] GaugeTwoForm
  weak : GaugeTwoForm ≃ₗ[ℝ] GaugeTwoForm
  hypercharge : GaugeTwoForm ≃ₗ[ℝ] GaugeTwoForm

def generatedBlockwiseKChi
    (point : BasePoint) (boundary : EmpiricalReferenceScaleCouplings) :
    StageNineBlockwiseKChi where
  gravityInternalDual := gravityInternalDualEquiv
  gaugeSpacetimeHodge := positiveGaugeSpacetimeHodge point
  strong := hodgeConstitutiveOperator (positiveGaugeSpacetimeHodge point)
    boundary.strongCouplingSquared
  weak := hodgeConstitutiveOperator (positiveGaugeSpacetimeHodge point)
    boundary.weakCouplingSquared
  hypercharge := hodgeConstitutiveOperator
    (positiveGaugeSpacetimeHodge point)
    boundary.hyperchargeCouplingSquared

theorem generatedBlockwiseKChi_typed_boundary
    (point : BasePoint) (boundary : EmpiricalReferenceScaleCouplings) :
    (generatedBlockwiseKChi point boundary).gravityInternalDual =
        gravityInternalDualEquiv ∧
      (generatedBlockwiseKChi point boundary).gaugeSpacetimeHodge =
        positiveGaugeSpacetimeHodge point ∧
      (generatedBlockwiseKChi point boundary).strong =
        hodgeConstitutiveOperator (positiveGaugeSpacetimeHodge point)
          boundary.strongCouplingSquared ∧
      (generatedBlockwiseKChi point boundary).weak =
        hodgeConstitutiveOperator (positiveGaugeSpacetimeHodge point)
          boundary.weakCouplingSquared ∧
      (generatedBlockwiseKChi point boundary).hypercharge =
        hodgeConstitutiveOperator (positiveGaugeSpacetimeHodge point)
          boundary.hyperchargeCouplingSquared :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem positiveSource_generates_IIPlus_and_blockwiseKChi
    (point : BasePoint) :
    physicalIIPlusBivector (canonicalPhysicalSource.coframeAt point) =
        gravityInternalDualEquiv
          (coframeWedge (canonicalPhysicalSource.coframeAt point)) ∧
      (generatedBlockwiseKChi point unitBoundary).gaugeSpacetimeHodge =
        positiveGaugeSpacetimeHodge point ∧
      Matrix.det (canonicalPhysicalSource.coframeAt point) ≠ 0 := by
  exact ⟨rfl, rfl, canonicalPhysicalSource_globally_nondegenerate point⟩


end

end SaturationMonoid.PhysicsCore.StageNineBlockwiseConstitutive

