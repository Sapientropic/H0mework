import H0mework.Fock.SourceHistoryClock.BinomialModel

/-! The source action determines the full three-moment future fibre of the existing generic model. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock

open SourceSuccessorBoundary

noncomputable section

theorem projection_fibre_iff (left right : Nat →₀ ℤ) :
    projection left = projection right ↔
      mass ℤ left = mass ℤ right ∧ SourceClockModel.clock left = SourceClockModel.clock right ∧ second left = second right := by
  constructor
  · intro same
    exact ⟨(massRead_source left).symm.trans ((congrArg massRead same).trans (massRead_source right)),
      (clockRead_source left).symm.trans ((congrArg clockRead same).trans (clockRead_source right)),
      (secondRead_source left).symm.trans ((congrArg secondRead same).trans (secondRead_source right))⟩
  · rintro ⟨massEq, clockEq, secondEq⟩
    apply (SourceGeneratedActionObservationHistory.model_fibre_iff _ _ left right).mpr
    change ∀ stage : Nat, second ((push ℤ ^ stage) left) = second ((push ℤ ^ stage) right)
    have all (stage : Nat) :
        mass ℤ ((push ℤ ^ stage) left) = mass ℤ ((push ℤ ^ stage) right) ∧
          SourceClockModel.clock ((push ℤ ^ stage) left) = SourceClockModel.clock ((push ℤ ^ stage) right) ∧
          second ((push ℤ ^ stage) left) = second ((push ℤ ^ stage) right) := by
      induction stage with
      | zero => exact ⟨massEq, clockEq, secondEq⟩
      | succ stage previous =>
          simp only [pow_succ', Module.End.mul_apply]
          rw [mass_push, mass_push, SourceClockModel.clock_push, SourceClockModel.clock_push, second_push, second_push]
          exact ⟨previous.1, congrArg₂ (· + ·) previous.2.1 previous.1,
            congrArg₂ (· + ·) previous.2.2 previous.2.1⟩
    exact fun stage => (all stage).2.2

theorem model_ext_iff (left right : Model) :
    left = right ↔ massRead left = massRead right ∧ clockRead left = clockRead right ∧ secondRead left = secondRead right := by
  refine Submodule.Quotient.induction_on _ left fun leftWord => ?_
  refine Submodule.Quotient.induction_on _ right fun rightWord => ?_
  change projection leftWord = projection rightWord ↔
    massRead (projection leftWord) = massRead (projection rightWord) ∧
      clockRead (projection leftWord) = clockRead (projection rightWord) ∧
        secondRead (projection leftWord) = secondRead (projection rightWord)
  rw [massRead_source, massRead_source, clockRead_source, clockRead_source, secondRead_source, secondRead_source]
  exact projection_fibre_iff leftWord rightWord

end
end SourceBinomialClock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
