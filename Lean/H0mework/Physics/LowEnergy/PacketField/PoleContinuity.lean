import H0mework.Physics.LowEnergy.PacketField.Pole

/-! A finite source numerator generates a bounded pole field on the actual
radial interval and both orientations, including its radial zero extension. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open LightModes LightInteraction DrivenInteraction VertexTensor
noncomputable section

abbrev RadialBand := {q : ℝ // |q| ≤ momentumRadius}

instance radialBand_compactSpace : CompactSpace RadialBand := by
  apply isCompact_iff_compactSpace.mp
  simpa only [Metric.closedBall,Real.dist_eq,sub_zero] using! isCompact_closedBall (0 : ℝ) momentumRadius

theorem radialRoot_continuous : Continuous (fun point : RadialBand => axialRoot point.val) := by
  apply continuous_iff_continuousAt.mpr
  intro point
  exact (axialRoot_continuousAt point.val point.property).comp continuous_subtype_val.continuousAt

theorem radialDerivative_continuous : Continuous (fun point : RadialBand => axialDerivative point.val) := by
  apply continuous_iff_continuousAt.mpr
  intro point
  exact (axialDerivative_continuousAt point.val point.property).comp continuous_subtype_val.continuousAt

theorem poleDenominator_continuous (sign : Bool) : Continuous (fun point : RadialBand => poleDenominator sign point.val) := by
  unfold poleDenominator
  have root := Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp radialRoot_continuous)
  have derivative := Complex.continuous_ofReal.comp radialDerivative_continuous
  exact (continuous_const.mul root).mul derivative

theorem poleValue_continuous (terms : List PoleTerm) (sign : Bool) :
    Continuous (fun point : RadialBand×ℝ => poleValue terms sign point.2 point.1.val) := by
  have root : Continuous (fun point : RadialBand×ℝ => (Real.sqrt (axialRoot point.1.val) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (radialRoot_continuous.comp continuous_fst))
  have radial : Continuous (fun point : RadialBand×ℝ => (point.1.val : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
  have orientation : Continuous (fun point : RadialBand×ℝ => (point.2 : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_snd
  have numerator := (reducedPolynomial_continuous terms).comp
    (((continuous_const (y := growthSign sign)).mul root).prodMk (orientation.prodMk radial))
  have denominator := (poleDenominator_continuous sign).comp
    (continuous_fst : Continuous (Prod.fst : RadialBand×ℝ → RadialBand))
  exact (continuous_const.mul numerator).div denominator
    (fun point => poleDenominator_nonzero sign point.1.val point.1.property)

attribute [local irreducible] poleValue

theorem poleValue_bounded (terms : List PoleTerm) (sign : Bool) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ (point : RadialBand) (orientation : ℝ), |orientation|≤1 →
      ‖poleValue terms sign orientation point.val‖≤bound := by
  have compact : IsCompact (Set.univ ×ˢ Set.Icc (-1 : ℝ) 1 : Set (RadialBand×ℝ)) :=
    isCompact_univ.prod isCompact_Icc
  obtain ⟨bound,upper⟩ := compact.bddAbove_image (poleValue_continuous terms sign).norm.continuousOn
  refine ⟨max bound 0,le_max_right _ _,?_⟩
  intro point orientation small
  have member : (point,orientation)∈(Set.univ ×ˢ Set.Icc (-1 : ℝ) 1 : Set (RadialBand×ℝ)) :=
    ⟨Set.mem_univ point,abs_le.mp small⟩
  exact (upper (Set.mem_image_of_mem _ member)).trans (le_max_left _ _)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
