import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedFiniteGram.Projection

open scoped InnerProductSpace
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem gram_kernel_eq_zero (source : ι → H) (independent : LinearIndependent ℂ source)
    (a : Coordinates ι) (zero : action (gram source) a = 0) : a = 0 := by
  have gone : synthesis source a = 0 := kernel_synthesis source zero
  have reads := Fintype.linearIndependent_iff.mp independent (fun i => a i) gone
  ext i
  exact reads i

private def dualWeights (source : ι → H) (independent : LinearIndependent ℂ source) (i : ι) : Coordinates ι :=
  SourceGeneratedFiniteGram.coefficients (gram source) (Matrix.isHermitian_gram ℂ source)
    (EuclideanSpace.single i (1 : ℂ)) (fun a zero => by
      rw [gram_kernel_eq_zero source independent a zero,inner_zero_left])

/-- The actual Gram equation for the coordinate unit generates its Hilbert cotest. -/
def dualColumn (source : ι → H) (independent : LinearIndependent ℂ source) (i : ι) : H :=
  synthesis source (dualWeights source independent i)

/-- The original source coefficients are independent continuous inner-product reads. -/
theorem inner_dualColumn_eq_coefficients (source : ι → H) (independent : LinearIndependent ℂ source)
    (i : ι) (increment : H) :
    inner ℂ (dualColumn source independent i) increment = coefficients source increment i := by
  let d := dualWeights source independent i
  let a := coefficients source increment
  have coordinate : action (gram source) d = EuclideanSpace.single i (1 : ℂ) :=
    SourceGeneratedFiniteGram.equation _ _ _ _
  have symmetric : (action (gram source)).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_gram ℂ source)
  calc
    _ = inner ℂ d (rhs source increment) := synthesis_inner source d increment
    _ = inner ℂ d (action (gram source) a) := by rw [equation]
    _ = inner ℂ (action (gram source) d) a := (symmetric d a).symm
    _ = _ := by rw [coordinate,EuclideanSpace.inner_single_left,map_one,one_mul]

end SourceGeneratedFiniteGram.Projection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
