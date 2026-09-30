import H0mework.Versions.X.Fock.HistoryConditional.InformationLossBudget

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInformationLoss

open scoped Classical
noncomputable section
local notation "entropy" =>
  SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population.entropy

theorem conditional_entropy_readback {Source Observed Next : Type*}
    [Fintype Source] [MeasurableSpace Source] [MeasurableSingletonClass Source]
    [Fintype Next] [MeasurableSpace Next] [MeasurableSingletonClass Next]
    (source : PMF Source) (read : Source → Observed) (nextRead : Source → Next)
    (value : Observed) (supported : value ∈ (source.map read).support) :
    entropy (SourceConditionalNext.conditionalNext source read nextRead value supported) =
      -∑ point : Source, (SourceConditionalHistory.conditional source read value supported point).toReal *
        Real.log ((SourceConditionalNext.conditionalNext source read nextRead value supported) (nextRead point)).toReal := by
  have paid := SourceConditionalNext.mean_is_conditional source read nextRead
    (fun next => (Real.log ((SourceConditionalNext.conditionalNext source read nextRead value supported) next).toReal : ℂ))
    value supported
  have real := congrArg Complex.re paid
  simp only [SourceConditionalNext.mean, SourceWeightedRecovery.conditionalMean, Complex.re_sum,
    Complex.smul_re, Complex.ofReal_re, smul_eq_mul, Function.comp_apply] at real
  exact congrArg Neg.neg real

end
end SourceConditionalInformationLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
