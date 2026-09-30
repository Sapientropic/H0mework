import H0mework.Fock.HistoryConditional.GWordInverseSourceMoments

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGWordInverse

open SourceGeneratedActionWords SourceSuccessorBoundary SourceCopyTimeModel
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def correction (depth : Nat) (word : List (Fock.Letter depth)) (source : SourceOperationNative.Carrier process) :
    SourceJointClockGraph.Carrier :=
  let remainder := SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.residual depth word source))
  SourceCopyGraph.axes (mass remainder)
    (((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ)⁻¹ *
      (SourceJointClockGraph.clock remainder - ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℂ) * mass remainder))

theorem recovery_native_moments (depth : Nat) (word : List (Fock.Letter depth)) (source : SourceOperationNative.Carrier process) :
    recover depth word (SourceJointClockGraph.read (SourceClockComplex.ofNative source)) =
      SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.recover depth word source)) +
        correction depth word source := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change hilbert (recover depth word (SourceJointClockGraph.read (SourceClockComplex.ofNative source))) =
        readWord (SourceClockComplex.ofNative (SourceCompiledWordOperator.recover depth word source)) + 0
      rw [native_hilbert_recover, add_zero]
    · change mass (recover depth word (SourceJointClockGraph.read (SourceClockComplex.ofNative source))) =
        mass (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.recover depth word source))) +
          mass (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.residual depth word source)))
      rw [mass_recover, native_mass_balance]
  · change SourceJointClockGraph.clock (recover depth word (SourceJointClockGraph.read (SourceClockComplex.ofNative source))) =
      SourceJointClockGraph.clock (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.recover depth word source))) +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ)⁻¹ *
        (SourceJointClockGraph.clock (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.residual depth word source))) -
          ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℂ) *
            mass (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.residual depth word source))))
    rw [clock_recover, ← native_mass_balance depth word source, ← native_clock_balance depth word source]
    have nonzero : ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (SourceCompiledWordOperator.slope_positive _).ne'
    field_simp
    ring

end
end SourceGWordInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
