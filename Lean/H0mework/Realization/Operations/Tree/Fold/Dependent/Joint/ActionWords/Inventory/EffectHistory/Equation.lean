import H0mework.Realization.ObservationActions.WordsModel
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionEffectHistory
section Equation
variable {I C W : Type u} [AddCommGroup C] [Module ℤ C] [AddCommGroup W] [Module ℤ W]
variable (actions : I → C →ₗ[ℤ] C) (waves : I → W →ₗ[ℤ] W) (observe : C →ₗ[ℤ] W)
def residual (word : List I) (point : C) : W :=
  SourceGeneratedActionWords.run waves word (observe point)-observe (SourceGeneratedActionWords.run actions word point)
def accumulated : List I → C → W
  | [],_ => 0
  | letter::rest,point => SourceGeneratedActionWords.run waves rest (residual actions waves observe [letter] point)+
      accumulated rest (actions letter point)
theorem accumulated_eq (word : List I) (point : C) : accumulated actions waves observe word point = residual actions waves observe word point := by
  induction word generalizing point with
  | nil => simp only [accumulated,residual,SourceGeneratedActionWords.run,Module.End.one_apply,sub_self]
  | cons letter rest previous =>
    simp only [accumulated,previous,residual,SourceGeneratedActionWords.run,Module.End.mul_apply,Module.End.one_apply,map_sub]
    abel
def history : List I → C → List (I × C × W)
  | [],_ => []
  | letter::rest,point => (letter,point,residual actions waves observe [letter] point)::history rest (actions letter point)
theorem history_length (word : List I) (point : C) : (history actions waves observe word point).length=word.length := by
  induction word generalizing point with
  | nil => rfl
  | cons letter rest previous => exact congrArg Nat.succ (previous (actions letter point))
end Equation
end SourceGeneratedActionEffectHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
