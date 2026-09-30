import H0mework.Versions.X.Fock.HistoryConditional.GWordProgramRealization

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGWordProgram

open SourceSuccessorBoundary
noncomputable section

theorem action_kernel (left right : Nat × Nat) (leftPositive : 0 < left.1) (rightPositive : 0 < right.1) :
    action left leftPositive = action right rightPositive ↔ left = right := by
  constructor
  · intro same
    have first := congrArg (fun operation : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier =>
      SourceJointClockGraph.clock (operation (SourceJointClockGraph.read (Finsupp.single 0 1)))) same
    have second := congrArg (fun operation : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier =>
      SourceJointClockGraph.clock (operation (SourceJointClockGraph.read (Finsupp.single 1 1)))) same
    simp only [action_source, SourceJointClockGraph.clock_source, clock_word left leftPositive, clock_word right rightPositive,
      SourceClockComplex.clock_single, mass_single] at first second
    norm_num [SourceClockModel.rawClock] at first second
    have firstNat : left.1 + left.2 = right.1 + right.2 := by exact_mod_cast first
    have secondNat : left.1 * 2 + left.2 = right.1 * 2 + right.2 := by exact_mod_cast second
    apply Prod.ext <;> omega
  · intro same
    subst right
    rfl

end
end SourceGWordProgram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
