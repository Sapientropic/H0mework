import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ContactFeedback.PrimitiveSource
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Box
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPrimitiveActionSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators
namespace Paid
export OriginalContactFeedbackSource (primitiveRaw primitiveScale primitiveMean original_primitive_read original_primitive_mean primitive_inner_raw primitive_positive_tail primitive_lower_word original_primitive_even)
export FiniteMobiusResolventFlux (M Rplus actualMean coefficient cutoff cutoff_read)
export OriginalPrimitiveRankBalance (conjugateCoordinate)
end Paid

def sourceRadius (n : ℕ+) : ℝ := (1/4:ℝ)*(n:ℕ)
def sourcePower (coordinate : BurnolCompletedMellinCoordinate) (n : ℕ+) : ℂ :=
  Paid.primitiveScale coordinate*(1/2:ℂ)*((n:ℕ):ℂ)^(star coordinate.value)
def sourceWord (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ∑ n∈burnolCenteredMobiusCutoffFinset 4,Paid.coefficient n*
    (if sourceRadius n<x then sourcePower coordinate n*(x:ℂ)^(-star coordinate.value)-Paid.primitiveMean coordinate else 0)

theorem source_radius_positive (n : ℕ+) : 0<sourceRadius n := by
  unfold sourceRadius
  positivity

theorem source_radius_bounded (n : ℕ+) (source : n∈burnolCenteredMobiusCutoffFinset 4) : sourceRadius n<4 := by
  have bound := (mem_burnolCenteredMobiusCutoffFinset 4 n).mp source
  norm_num [burnolCenteredMobiusCutoff] at bound
  have realBound : ((n:ℕ):ℝ)<16 := by exact_mod_cast bound
  unfold sourceRadius
  nlinarith

theorem primitive_pullback_positive (coordinate : BurnolCompletedMellinCoordinate) (n : ℕ+) (x : ℝ) (positive : 0<x) :
    Paid.primitiveRaw coordinate (x/(n:ℕ))-Paid.primitiveMean coordinate=
      if sourceRadius n<x then sourcePower coordinate n*(x:ℂ)^(-star coordinate.value)-Paid.primitiveMean coordinate else 0 := by
  have nPositive : (0:ℝ)<(n:ℕ) := by exact_mod_cast n.pos
  by_cases outside : sourceRadius n<x
  · have tail : (1/4:ℝ)<x/(n:ℕ) := (lt_div_iff₀ nPositive).mpr outside
    rw [if_pos outside,Paid.primitive_positive_tail coordinate _ tail]
    have power : ((x/(n:ℕ):ℝ):ℂ)^(-star coordinate.value)=
        (x:ℂ)^(-star coordinate.value)*((n:ℕ):ℂ)^(star coordinate.value) := by
      rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg positive.le (le_of_lt nPositive)]
      rw [div_eq_mul_inv,← Complex.cpow_neg]
      simp only [neg_neg,Complex.ofReal_natCast]
    rw [power]
    unfold sourcePower
    ring
  · have inside : x/(n:ℕ)∈symmetricInterval (1/4:ℝ) :=
      ⟨by have pos := div_pos positive nPositive; linarith,(div_le_iff₀ nPositive).mpr (le_of_not_gt outside)⟩
    rw [if_neg outside,Paid.primitive_inner_raw coordinate _ inside,sub_self]

theorem original_finite_positive_word (coordinate : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume,∀ _positive : 0<x,
      Paid.M (OriginalRieszFiniteSource.edgePrimitive coordinate) x=
        if x≤4 then sourceWord coordinate x else 0 := by
  filter_upwards [Paid.primitive_lower_word coordinate] with x word positive
  rw [word]
  by_cases upper : x≤4
  · rw [if_pos upper,indicator_of_mem (show x∈symmetricInterval 4 from ⟨by linarith,upper⟩)]
    unfold sourceWord
    apply Finset.sum_congr rfl
    intro n _
    rw [primitive_pullback_positive coordinate n x positive]
  · rw [if_neg upper,indicator_of_notMem (show x∉symmetricInterval 4 from fun h=>upper h.2)]
end OriginalPrimitiveActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
