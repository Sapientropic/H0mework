import H0mework.Physics.Actual.RuntimeConsumer

/-! The original weak-history admission identifies one complete smooth
classical configuration. Its full field equations and nontriviality are
consumed together, without narrowing the original admissible history. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9G

open StageNineHolonomicField StageNineCClassicalWorldAcceptance
open StageNineEnrichedProofFreeSource

noncomputable section

/-- Admission uses the complete original source history and its weak images. -/
def LawfulClassicalActual (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∃ smooth : configuration.Smooth, ∃ candidate : Stage9CU.Weak.Candidate,
    Stage9CU.Weak.density candidate = Stage9CU.Fields.compactCoordinates configuration smooth

theorem original_actual_admitted : LawfulClassicalActual Stage9C.Material.SpinPair.actual :=
  ⟨Stage9CU.History.configuration_smooth 7, Stage9CU.Weak.canonical, rfl⟩

theorem lawfulClassicalActual_eq_original
    {configuration : StageNineHolonomicConfiguration}
    (admitted : LawfulClassicalActual configuration) :
    configuration = Stage9C.Material.SpinPair.actual := by
  obtain ⟨smooth, admitted⟩ := admitted
  exact Stage9CU.Weak.configuration_eq_firstWrite_of_candidate smooth admitted

theorem lawfulClassicalActual_classicalWorldAcceptance
    {configuration : StageNineHolonomicConfiguration}
    (admitted : LawfulClassicalActual configuration) :
    ClassicalWorldAcceptance positiveSmoothUnifiedSource configuration := by
  rw [lawfulClassicalActual_eq_original admitted]
  exact Stage9C.Material.SpinPair.actual_classicalWorldAcceptance

theorem sourceGeneratedUniqueClassicalActual :
    ∃! configuration, LawfulClassicalActual configuration ∧
      ClassicalWorldAcceptance positiveSmoothUnifiedSource configuration :=
  ⟨Stage9C.Material.SpinPair.actual,
    ⟨original_actual_admitted, Stage9C.Material.SpinPair.actual_classicalWorldAcceptance⟩,
    fun _ admitted => lawfulClassicalActual_eq_original admitted.1⟩

end
end SaturationMonoid.PhysicsCore.Stage9G
