import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.ArithmeticQuarter
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.ActedPrice
import H0mework.Versions.R7e4da746.Arithmetic.BurnolPhysical.QuarterMellinAdditiveRechartAction

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open Complex Filter MeasureTheory Set BurnolPhysicalState
open AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History.PrimePowerCurrent
open Character.GlobalCoPoissonCurrent ThetaJRoleRepresentation
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Source
open scoped Topology InnerProductSpace
local notation "order" => generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "R" => burnolDirectRightResolventCLM

/-- A whole arithmetic unit action is exactly the first Fourier-inverted native Gram leg. -/
theorem actual_native_unit_first_field (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (scale : Units NNReal) :
    quarterMellinAdditiveEvenRechart (quarterDilationTestAction (c.value/2)
      (scaleSquare scale) (scaleSquare_pos scale) (nativeTopQuarterTest c zero)) =
    fourierL2.symm (burnolMultiplicativeDilation (Real.log (scaleValue scale))
      (((R c)^(order c.value)) (nativeCotest c))) := by
  rw [quarterMellinAdditiveEvenRechart_dilation, actual_native_top_rechart]
  have clock : -(Real.log (scaleSquare scale))/2 = -Real.log (scaleValue scale) := by
    rw [scaleSquare, Real.log_pow]
    ring
  rw [clock]
  have source := congrArg fourierL2.symm
    (fourierL2_burnolMultiplicativeDilation (-Real.log (scaleValue scale))
      (nativeOutgoingCotest c (order c.value)))
  rw [fourierL2.symm_apply_apply, neg_neg] at source
  have field : fourierL2 (nativeOutgoingCotest c (order c.value)) =
      (((R c)^(order c.value)) (nativeCotest c)) := by
    rw [← actual_native_acted_field c zero (order c.value), fourierL2.apply_symm_apply]
  rw [field] at source
  exact source

/-- The literal prime-exponent generator, before any retained scalar read. -/
theorem actual_native_arithmetic_basis_field (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (exponent : PrimeExponentLattice) :
    quarterMellinAdditiveEvenRechart
      (nativeTopArithmeticTest c zero (AddMonoidAlgebra.single exponent 1)) =
    fourierL2.symm (burnolMultiplicativeDilation (Real.log (scaleValue (primeExponentScale exponent)))
      (((R c)^(order c.value)) (nativeCotest c))) := by
  rw [nativeTopArithmeticTest, primeExponentPoleQuarterTestMap_single, one_smul]
  exact actual_native_unit_first_field c zero (primeExponentScale exponent)

/-- Its complete prime boundary keeps the two actual Gram rows together. -/
theorem actual_native_arithmetic_boundary_field (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (index : ConductorPrimePowerIndex) :
    quarterMellinAdditiveEvenRechart
      (nativeTopArithmeticTest c zero (factorizationBoundaryValue index)) =
    fourierL2.symm (((R c)^(order c.value)) (nativeCotest c)) -
      fourierL2.symm (burnolMultiplicativeDilation
        (Real.log (scaleValue (primePowerUnit index.1 index.2.1)))
        (((R c)^(order c.value)) (nativeCotest c))) := by
  change quarterMellinAdditiveEvenRechartLinear (c.value/2)
    (nativeTopArithmeticTest c zero (factorizationBoundaryValue index)) = _
  rw [actual_native_arithmetic_boundary, map_sub]
  change quarterMellinAdditiveEvenRechart (nativeTopQuarterTest c zero) -
    quarterMellinAdditiveEvenRechart (quarterDilationTestAction _ _ _ _) = _
  rw [actual_native_top_rechart, actual_native_unit_first_field, actual_native_acted_field c zero (order c.value)]

/-- The second whole native source stays an independent L2 input; no Mellin convergence is borrowed for it. -/
theorem actual_native_arithmetic_basis_pairing (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (exponent : PrimeExponentLattice) (right : BurnolL2) :
    inner ℂ (burnolMultiplicativeDilation (Real.log (scaleValue (primeExponentScale exponent)))
      (((R c)^(order c.value)) (nativeCotest c))) right =
    inner ℂ (quarterMellinAdditiveEvenRechart
      (nativeTopArithmeticTest c zero (AddMonoidAlgebra.single exponent 1)))
      (fourierL2.symm right) := by
  rw [actual_native_arithmetic_basis_field]
  exact (fourierL2.symm.inner_map_map _ _).symm


/-- Every finite signed prime-exponent current reads the actual acted top, not just one boundary. -/
theorem actual_native_arithmetic_retained_current (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (event : PrimeExponentFactorizationCarrier) :
    quarterMellinL2Functional (c.value/2) (nativeTopArithmeticTest c zero event) =
      (4 * ((2 : ℂ)^(order c.value) * generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner c.value c.value *
        burnolAmbientCompletedMellinEvaluator c (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices.physicalCotest c : BurnolL2))) *
      selectedPrimeExponentPoleMellinMap (burnolPaZeroObservation c zero)
        (burnolPaZeroObservation_nontrivial c zero) event := by
  induction event using AddMonoidAlgebra.induction_on with
  | of exponent =>
    rw [AddMonoidAlgebra.of_apply, nativeTopArithmeticTest, primeExponentPoleQuarterTestMap_single, one_smul]
    simp only [Multiplicative.toAdd, Equiv.symm_apply_apply]
    have selected := selectedPrimeExponentPoleMellinMap_single (burnolPaZeroObservation c zero)
      (burnolPaZeroObservation_nontrivial c zero) exponent
    change selectedPrimeExponentPoleMellinMap (burnolPaZeroObservation c zero)
      (burnolPaZeroObservation_nontrivial c zero) (AddMonoidAlgebra.single exponent 1) = _ at selected
    rw [selected]
    have action := LinearMap.congr_fun (quarterDilationFunctional_eigenlaw (c.value/2)
      (scaleSquare (primeExponentScale exponent)) (scaleSquare_pos _)) (nativeTopQuarterTest c zero)
    change quarterMellinL2Functional (c.value/2) (quarterDilationTestAction (c.value/2)
      (scaleSquare (primeExponentScale exponent)) (scaleSquare_pos _) (nativeTopQuarterTest c zero)) =
      ((scaleSquare (primeExponentScale exponent) : ℂ)^((1/4 : ℂ) - c.value/2)) •
        quarterMellinL2Functional (c.value/2) (nativeTopQuarterTest c zero) at action
    rw [action, actual_native_top_quarter_read]
    change _ = _ * ((scaleSquare (primeExponentScale exponent) : ℂ)^((1/4 : ℂ) - c.value/2))
    simp only [smul_eq_mul]
    ring
  | add left right leftHypothesis rightHypothesis =>
    simp only [map_add, leftHypothesis, rightHypothesis]
    ring
  | smul coefficient value inductionHypothesis =>
    simp only [map_smul, map_zsmul, inductionHypothesis]
    simp only [zsmul_eq_mul]
    ring

/-- The original spectral-state consumer evaluates the whole signed current with both independent read faces. -/
theorem actual_native_arithmetic_current_faces (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (event : PrimeExponentFactorizationCarrier) :
    (4 * ((2 : ℂ)^(order c.value) * generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner c.value c.value *
        burnolAmbientCompletedMellinEvaluator c (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices.physicalCotest c : BurnolL2))) *
      selectedPrimeExponentPoleMellinMap (burnolPaZeroObservation c zero)
        (burnolPaZeroObservation_nontrivial c zero) event =
      inner ℂ (selectedPrimeExponentPoleRootSpectralState (burnolPaZeroObservation c zero)
        (burnolPaZeroObservation_nontrivial c zero)).fst
          (quarterMellinL2Feature (c.value/2) (nativeTopArithmeticTest c zero event)) +
      inner ℂ (selectedPrimeExponentPoleRootSpectralState (burnolPaZeroObservation c zero)
        (burnolPaZeroObservation_nontrivial c zero)).snd
          (quarterMellinL2Functional (c.value/2) (nativeTopArithmeticTest c zero event)) := by
  rw [← actual_native_arithmetic_retained_current c zero event]
  exact actual_native_arithmetic_three_faces c zero event

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
