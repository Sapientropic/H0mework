import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixImage

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedFiniteGram.PrefixReadback

open private compatibleData compatible_data from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixReadback
open private rhs_mem_range from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The paid Gram image inverse is linear in the observed coordinates, so it can execute as a source operation. -/
def inverseLinear (source : ι → H) : Coordinates ι →ₗ[ℂ] H :=
  let gram := Projection.gram source
  let project := ((Kernel gram)ᗮ.starProjection).toLinearMap.codRestrict (action gram).range
    fun data => rhs_mem_range gram (Matrix.isHermitian_gram ℂ source)
      (compatibleData source data) (compatible_data source data)
  ((Kernel gram).liftQ (Projection.synthesis source) (Projection.kernel_synthesis source)).comp
    ((action gram).quotKerEquivRange.symm.toLinearMap.comp project)

theorem inverseLinear_apply (source : ι → H) (data : Coordinates ι) :
    inverseLinear source data = inverse source data := rfl

end SourceGeneratedFiniteGram.PrefixReadback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
