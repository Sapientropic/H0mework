import H0mework.Fock.PrimeField.ClockSplittingSection

/-! The full joint carrier is the original prime completion plus its generated clock fibre. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockSplitting

open SourcePrimeClockResidual

noncomputable section

local instance : Module ℤ (SourcePrimeCompletion.Field × ℤ) := Prod.instModule

def coordinates : JointField →ₗ[ℤ] SourcePrimeCompletion.Field × ℤ := primeProjection.prod clockRead

def rebuild : (SourcePrimeCompletion.Field × ℤ) →ₗ[ℤ] JointField :=
  sectionMap.comp (LinearMap.fst ℤ _ _) +
    (LinearMap.toSpanSingleton ℤ JointField SourcePrimeClockResidual.residual).comp (LinearMap.snd ℤ _ _)

theorem rebuild_apply (value : SourcePrimeCompletion.Field × ℤ) :
    rebuild value = sectionMap value.1 + value.2 • SourcePrimeClockResidual.residual :=
  congrArg (fun hidden : JointField => sectionMap value.1 + hidden)
    (int_smul_eq_zsmul JointField.isModule value.2 SourcePrimeClockResidual.residual)

theorem rebuild_prime (value : SourcePrimeCompletion.Field × ℤ) : primeProjection (rebuild value) = value.1 := by
  rw [rebuild_apply, map_add, map_zsmul, section_prime, residual_prime_zero, zsmul_zero, add_zero]

theorem rebuild_clock (value : SourcePrimeCompletion.Field × ℤ) : clockRead (rebuild value) = value.2 := by
  simp only [rebuild_apply, map_add, map_zsmul, section_clock, residual_clock_unit,
    zsmul_eq_mul, Int.cast_id, mul_one, zero_add]

theorem coordinates_rebuild (value : SourcePrimeCompletion.Field × ℤ) : coordinates (rebuild value) = value := by
  apply Prod.ext
  · exact rebuild_prime value
  · exact rebuild_clock value

theorem rebuild_coordinates (value : JointField) : rebuild (coordinates value) = value := by
  apply joint_ext
  · exact rebuild_prime (coordinates value)
  · exact rebuild_clock (coordinates value)

def chart : JointField ≃ₗ[ℤ] SourcePrimeCompletion.Field × ℤ :=
  LinearEquiv.ofLinearMap coordinates rebuild (LinearMap.ext coordinates_rebuild) (LinearMap.ext rebuild_coordinates)

theorem projection_surjective : Function.Surjective primeProjection :=
  fun value => ⟨sectionMap value, section_prime value⟩

theorem full_inverse_fibre (value : SourcePrimeCompletion.Field) (clock : ℤ) :
    ∃! joint : JointField, primeProjection joint = value ∧ clockRead joint = clock := by
  refine ⟨rebuild (value, clock), ⟨rebuild_prime _, rebuild_clock _⟩, ?_⟩
  intro joint specification
  exact joint_ext joint (rebuild (value, clock))
    (specification.1.trans (rebuild_prime (value, clock)).symm) (specification.2.trans (rebuild_clock (value, clock)).symm)

end
end SourcePrimeClockSplitting
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
