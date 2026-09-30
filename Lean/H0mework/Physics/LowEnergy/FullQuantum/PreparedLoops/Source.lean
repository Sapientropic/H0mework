import H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Words
import H0mework.Physics.LowEnergy.FullQuantum.CoframeResponse.Boundary

/-! The actual preparation, rather than a bare trace, consumes the source exterior arrow. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops
open ClosedLoops StateGreen CoframeResponse Triangular
open YangMills.FullPairing DiracExteriorMatterAction Stage9DEF
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
noncomputable section

theorem prepared_six_read (point : BasePoint) (v : DiracExteriorMatterCarrier) :
    inner ℂ (prepared point) (naturalCoordinates (MixedSymbol.degreeSix v))=0 := by
  rw [prepared,inner_embed]
  simp [Compatibility.coordinates,MixedSymbol.degreeSix,sourceColorDoubletDual]

theorem arrow_prepared_zero (point : BasePoint) (A : Mother) (arrow : Arrow A) :
    inner ℂ (prepared point) (operator A (prepared point))=0 := by
  have output := LinearMap.congr_fun arrow.1 (Compatibility.embed (Stage9DEF.Source.vector point))
  change MixedSymbol.degreeSix (A (Compatibility.embed (Stage9DEF.Source.vector point)))=
    A (Compatibility.embed (Stage9DEF.Source.vector point)) at output
  rw [prepared,operator_coordinates,← output]
  exact prepared_six_read point _

theorem expansion_prepared (point : BasePoint) (A diagonal : Mother) (generated : Expansion A diagonal) :
    inner ℂ (prepared point) (operator A (prepared point))=
      inner ℂ (prepared point) (operator diagonal (prepared point)) := by
  have zero := arrow_prepared_zero point (A-diagonal) generated.2
  have subtract : operator (A-diagonal)=operator A-operator diagonal := by ext v; simp [operator]
  rw [subtract,sub_apply,inner_sub_right] at zero
  exact sub_eq_zero.mp zero

theorem boundary_grade (C : StageNineHolonomicConfiguration) (point : BasePoint) :
    Commute MixedSymbol.degreeSix (boundaryWeight C point) := by
  unfold boundaryWeight
  apply Commute.smul_right
  exact (grade_spin 0 _).mul_right (grade_principal 0 C point)

theorem weighted_expansion (point : BasePoint) (C : StageNineHolonomicConfiguration) (atPoint : BasePoint)
    (A diagonal : Mother) (generated : Expansion A diagonal) :
    inner ℂ (prepared point) (operator (boundaryWeight C atPoint*A) (prepared point))=
      inner ℂ (prepared point) (operator (boundaryWeight C atPoint*diagonal) (prepared point)) :=
  expansion_prepared point _ _ ((Expansion.refl _ (boundary_grade C atPoint)).mul generated)

theorem weighted_arrow_zero (point : BasePoint) (C : StageNineHolonomicConfiguration) (atPoint : BasePoint)
    (A : Mother) (arrow : Arrow A) :
    inner ℂ (prepared point) (operator (boundaryWeight C atPoint*A) (prepared point))=0 :=
  arrow_prepared_zero point _ (Arrow.diagonal_left (boundary_grade C atPoint) arrow)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops
