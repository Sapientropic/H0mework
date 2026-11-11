import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.ConjugateLow
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSectorEulerMixedSource.Mixed
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.OppositeForcing
open Complex MeasureTheory Set Filter BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCompactAdjointRSource OriginalKSectorEulerMixedSource
open OriginalKCoefficientBFiniteAction OriginalKElementaryArithmeticAction
open OriginalKFiniteOrderRelease OriginalKFiniteOrderRelease.UnitPowerSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.ConjugateLow
open scoped InnerProductSpace Topology
open private elementary_projection from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Field
open private actual_seed_right_input from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSectorEulerMixedSource.Mixed
local notation "q" => (1/4 : ℝ)
local notation "P" => burnolEvenAmbientProjection
local notation "R" => burnolDirectRightResolventCLM
local notation "K" => burnolCompletedMellinRieszVector
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "μ" => FiniteMobiusResolventFlux.actualMean
local notation "U" => Response.wholeU
local notation "V" => Response.wholeV
local notation "seed" => OriginalKSectorEulerMixedSource.NativeK.seed
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem gap_star (d : BurnolCompletedMellinCoordinate) :
    star (burnolMellinGapMoment (star d.value)) = (q : ℂ)^(1-d.value)/(1-d.value) := by
  have qne : (q : ℂ) ≠ 0 := by norm_num
  have power : star ((q : ℂ)^(1-star d.value)) = (q : ℂ)^(1-d.value) := by
    simp only [Complex.cpow_def_of_ne_zero qne]
    change (starRingEnd ℂ) (Complex.exp _) = _
    rw [← Complex.exp_conj]
    congr 1
    rw [show Complex.log (q : ℂ) = (Real.log q : ℂ) from (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ q)).symm]
    rw [map_mul,map_sub,map_one,Complex.conj_ofReal]
    change _*(1-star (star d.value)) = _
    rw [star_star]
  change star ((q : ℂ)^(1-star d.value)/(1-star d.value)) = _
  rw [star_div₀,power,star_sub,star_one,star_star]

private theorem compact_zero_mean_price (d : BurnolCompletedMellinCoordinate) (source : BurnolL2)
    (zeroMean : μ source = 0) (physical : BurnolPaAmbientCarrier) :
    actualCompactRightPrice d source physical =
      -2 * actualCompactTailCoefficient d source * inner ℂ (physical : BurnolL2) (K (barC d) : BurnolL2) := by
  have denominator : 1-d.value ≠ 0 := by
    intro equality
    have real := congrArg Complex.re (sub_eq_zero.mp equality)
    norm_num at real
    linarith [d.belowOne]
  have half : d.value/2-1/2 ≠ 0 := by
    intro equality
    apply denominator
    linear_combination -2*equality
  have qpower : (q : ℂ)*(q : ℂ)^(-d.value) = (q : ℂ)^(1-d.value) := by
    conv_lhs => arg 1; rw [← Complex.cpow_one (q : ℂ)]
    rw [← Complex.cpow_add _ _ (by norm_num : (q : ℂ) ≠ 0)]
    congr 1
  have pairing : star (inner ℂ (K (OriginalKQuarterTailPhysicalSource.actualStarSource d)) physical) =
      inner ℂ (physical : BurnolL2) (K (barC d) : BurnolL2) := by
    exact inner_conj_symm _ _
  unfold actualCompactRightPrice
  rw [zeroMean,sub_zero]
  simp only [star_add,star_mul,star_neg,star_ofNat,gap_star,pairing]
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]
  rw [show (2:ℂ)*(q:ℂ)*(q:ℂ)^(-d.value) = 2*(q:ℂ)^(1-d.value) by rw [mul_assoc,qpower]]
  rw [show d.value/2-1/2 = -(1-d.value)/2 by ring]
  field_simp [denominator]
  ring

private theorem seed_combination (c : BurnolCompletedMellinCoordinate) (physical : BurnolPaAmbientCarrier) :
    (1-(barC c).value)*actualSeedRightPrice (barC c) physical -
      2*inner ℂ (physical : BurnolL2) seed =
        -2*inner ℂ (physical : BurnolL2) (K c : BurnolL2)/(star (c).value*GapEuler.gapMean q c) := by
  have coef : star (c).value*GapEuler.gapMean q c ≠ 0 := by
    have scalar : star (c).value ≠ 0 := ne_of_apply_ne Complex.re (by
      simp only [Complex.star_def,Complex.conj_re,Complex.zero_re]
      linarith [c.rightHalf])
    apply mul_ne_zero scalar
    intro zero
    have actual := GapEuler.gapMean_primitive q (by norm_num) c
    rw [zero,mul_zero] at actual
    exact (mul_ne_zero (by norm_num : (1/2 : ℂ) ≠ 0)
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))) actual.symm
  have source := congrArg (inner ℂ (physical : BurnolL2)) (elementary_unit_resolvent c)
  have projected := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left physical (elementarySource c)
  change inner ℂ physical (P (elementarySource c)) = inner ℂ (physical : BurnolL2) (elementarySource c) at projected
  rw [elementary_projection] at projected
  rw [← projected,unitResolventSource,inner_smul_right,inner_sub_right,inner_smul_right] at source
  have seedPrice := (actual_original_seed_R_right_prices (barC c) physical).1
  change inner ℂ (physical : BurnolL2) (R (barC c) seed) = actualSeedRightPrice (barC c) physical at seedPrice
  change star (c).value*GapEuler.gapMean q c * (inner ℂ (physical : BurnolL2) seed -
    (1-star (c).value)/2 * inner ℂ (physical : BurnolL2) (R (barC c) seed)) =
      inner ℂ (physical : BurnolL2) (K c : BurnolL2) at source
  rw [seedPrice] at source
  apply (eq_div_iff coef).mpr
  change ((1-star (c).value)*actualSeedRightPrice (barC c) physical - 2*inner ℂ (physical : BurnolL2) seed)*
      (star (c).value*GapEuler.gapMean q c) = _
  linear_combination -2*source

/-- Both compact B drives and the complete independent seed response constitute the original matrix. -/
def oppositeBMatrix (c : BurnolCompletedMellinCoordinate) : ℂ :=
  Kernel.beta (barC c)*actualCompactTailCoefficient (barC c) U -
    Kernel.A (barC c)*actualCompactTailCoefficient (barC c) V +
      Kernel.A (barC c)/(star (c).value*GapEuler.gapMean q c)

/-- Literal original two full R drives, before their Fourier top is priced. -/
def oppositeForcing (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  fourierL2 (OriginalKCrossParameterRAdjointSource.sourcePlusDrive (barC c) (barC c) +
    OriginalKCrossParameterRAdjointSource.sourceMinusDrive (barC c) (barC c))

private theorem drive_price (c : BurnolCompletedMellinCoordinate) (physical : BurnolPaAmbientCarrier) :
    inner ℂ (physical : BurnolL2)
      (OriginalKCrossParameterRAdjointSource.sourcePlusDrive (barC c) (barC c) +
        OriginalKCrossParameterRAdjointSource.sourceMinusDrive (barC c) (barC c)) =
      4*inner ℂ (physical : BurnolL2) (K (barC c) : BurnolL2) -
        4*oppositeBMatrix c*inner ℂ (physical : BurnolL2) (K c : BurnolL2) := by
  have muU := actual_quarter_mean_zero_source Response.u
  have muV := actual_quarter_mean_zero_source Response.v
  have prices := actual_two_forcing_R_right_prices (barC c) physical
  have seedRead := actual_seed_right_input physical
  have compactU := compact_zero_mean_price (barC c) U muU physical
  have compactV := compact_zero_mean_price (barC c) V muV physical
  have barBar : barC (barC c) = c := by cases c; simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
  rw [barBar] at compactU compactV
  have full : OriginalKCrossParameterRAdjointSource.sourcePlusDrive (barC c) (barC c) +
      OriginalKCrossParameterRAdjointSource.sourceMinusDrive (barC c) (barC c) =
      R (barC c) (actualPlusForcing (barC c)) + R (barC c) (actualMinusForcing (barC c)) +
        (4 : ℂ) • (K (barC c) : BurnolL2) - (4*Kernel.A (barC c)) • seed +
          (4*Kernel.beta (barC c)) • fourierL2 seed := by
    unfold OriginalKCrossParameterRAdjointSource.sourcePlusDrive OriginalKCrossParameterRAdjointSource.sourceMinusDrive
      OriginalKCrossParameterRAdjointSource.sourcePlusForcing OriginalKCrossParameterRAdjointSource.sourceMinusForcing
      OriginalKCrossParameterRAdjointSource.Base.sourcePlusCorrected OriginalKCrossParameterRAdjointSource.Base.sourceMinusCorrected
    simp only [sub_self,zero_smul,add_zero,OriginalKSourceResolventReconstruction.generatedK_eq_original]
    module
  rw [full]
  simp only [inner_add_right,inner_sub_right,inner_smul_right]
  change inner ℂ (physical : BurnolL2) (R (barC c) (actualPlusForcing (barC c))) = _ ∧
    inner ℂ (physical : BurnolL2) (R (barC c) (actualMinusForcing (barC c))) = _ at prices
  rw [prices.1,prices.2]
  unfold actualPlusRightForcingPrice actualMinusRightForcingPrice
  rw [compactU,compactV]
  have scalar : (barC c).value ≠ 0 := ne_of_apply_ne Complex.re (by
    have positive := (barC c).rightHalf
    simp only [Complex.zero_re]
    linarith)
  have seedIdentity := seed_combination c physical
  have fourierSeed : (barC c).value*actualFourierSeedRightPrice (barC c) physical =
      -2*inner ℂ (physical : BurnolL2) (fourierL2 seed) := by
    unfold actualFourierSeedRightPrice
    rw [seedRead.2]
    field_simp [scalar]
  unfold oppositeBMatrix
  linear_combination 2*Kernel.A (barC c)*seedIdentity+2*Kernel.beta (barC c)*fourierSeed

/-- The complete opposite forcing has two original K Fourier columns and the full computed B matrix. -/
theorem actual_opposite_physical_source (c : BurnolCompletedMellinCoordinate) :
    P (oppositeForcing c) = (4 : ℂ) • evenFaceFourierEquiv burnolUnscaledCommonGapRadius (K (barC c)) -
      (4*oppositeBMatrix c) • evenFaceFourierEquiv burnolUnscaledCommonGapRadius (K c) := by
  apply ext_inner_left ℂ
  intro physical
  have projected := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left physical (oppositeForcing c)
  change inner ℂ physical (P (oppositeForcing c)) = inner ℂ (physical : BurnolL2) (oppositeForcing c) at projected
  rw [projected]
  have moved := fourierL2.inner_map_map (fourierL2 (physical : BurnolL2))
    (OriginalKCrossParameterRAdjointSource.sourcePlusDrive (barC c) (barC c) +
      OriginalKCrossParameterRAdjointSource.sourceMinusDrive (barC c) (barC c))
  have even : fourierL2 (fourierL2 (physical : BurnolL2)) = (physical : BurnolL2) := by
    rw [fourierL2_fourierL2]
    exact mem_evenL2ClosedFace_iff.mp physical.property.2
  rw [even] at moved
  change inner ℂ (physical : BurnolL2) (oppositeForcing c) = _ at moved
  rw [moved]
  have priced := drive_price c (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical)
  change inner ℂ (fourierL2 (physical : BurnolL2)) _ = _ at priced
  rw [priced]
  have transfer (value : BurnolPaAmbientCarrier) :
      inner ℂ (fourierL2 (physical : BurnolL2)) (value : BurnolL2) =
        inner ℂ physical (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value) := by
    have same := fourierL2.inner_map_map (physical : BurnolL2) (fourierL2 (value : BurnolL2))
    rw [fourierL2_fourierL2,mem_evenL2ClosedFace_iff.mp value.property.2] at same
    exact same
  change 4*inner ℂ (fourierL2 (physical : BurnolL2)) (K (barC c) : BurnolL2) -
    4*oppositeBMatrix c*inner ℂ (fourierL2 (physical : BurnolL2)) (K c : BurnolL2) = _
  rw [transfer,transfer]
  simp only [inner_sub_right,inner_smul_right]

private theorem opposite_adjoint_pair (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    inner ℂ (fourierL2 (K (barC coordinate) : BurnolL2)) (R coordinate value) =
      inner ℂ (fourierL2 (burnolDirectRightResolvent ((barC coordinate).value/2)
        (K (barC coordinate) : BurnolL2))) value := by
  have right : 1/4<(coordinate.value/2).re := by
    rw [Complex.div_re]; norm_num; linarith [coordinate.rightHalf]
  have conjugateRight : 1/4<((barC coordinate).value/2).re := by
    rw [Complex.div_re]; norm_num; linarith [(barC coordinate).rightHalf]
  have source := actual_original_R_adjoint (coordinate.value/2) right
    (fourierL2 (K (barC coordinate) : BurnolL2)) value
  change inner ℂ (fourierL2 (K (barC coordinate) : BurnolL2))
    (burnolDirectRightResolvent (coordinate.value/2) value) = _
  rw [FiniteMobiusResolventFlux.fourier_R _ conjugateRight]
  simpa only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_div₀,star_ofNat] using source

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : ℕ, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
include nontrivial

/-- The physical m-1 Unit field consumes both complete conjugate B columns and the original Xi top. -/
theorem actual_opposite_forcing_original_top :
    inner ℂ (oppositeForcing c) (unitPower observation half (m-1)) =
      -4*star (oppositeBMatrix c)*e := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  let value : BurnolPaAmbientCarrier := ⟨unitPower observation half (m-1),
    unitPower_physical observation nontrivial half (m-1) (by omega)⟩
  have projected := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right value (oppositeForcing c)
  change inner ℂ (P (oppositeForcing c)) value =
    inner ℂ (oppositeForcing c) (unitPower observation half (m-1)) at projected
  rw [actual_opposite_physical_source,inner_sub_left,inner_smul_left,inner_smul_left] at projected
  have low := actual_conjugate_FK_unit_low observation nontrivial half (m-1) (by omega)
  have top := unitPower_fourier_top observation nontrivial half
  change inner ℂ (fourierL2 (K (barC c) : BurnolL2)) (unitPower observation half (m-1)) = 0 at low
  change inner ℂ (evenFaceFourierEquiv burnolUnscaledCommonGapRadius (K (barC c))) value = 0 at low
  change inner ℂ (evenFaceFourierEquiv burnolUnscaledCommonGapRadius (K c)) value = e at top
  rw [low,top,mul_zero,zero_sub] at projected
  rw [←projected]
  change -(star (4*oppositeBMatrix c)*e) = _
  rw [star_mul,star_ofNat]
  ring

/-- The unprojected m-th Unit keeps its complete opposite-parameter matrix price. -/
theorem actual_conjugate_fourier_original_top_source :
    star (2*((c).value-(barC c).value))*
        inner ℂ (fourierL2 (K (barC c) : BurnolL2)) (unitPower observation half m) =
      -4*star (oppositeBMatrix c)*e := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  have source := congrArg fourierL2 ((OriginalKCrossParameterRAdjointSource.cross_parameter_weighted_fields
    (barC c) (barC c)).1)
  simp only [map_smul,OriginalPrimitiveRankBalance.conjugateCoordinate,star_star] at source
  have read := congrArg (fun field : BurnolL2 => inner ℂ field (unitPower observation half (m-1))) source
  rw [inner_smul_left] at read
  have step : unitPower observation half m = R c (unitPower observation half (m-1)) := by
    have same : m = (m-1)+1 := by omega
    conv_lhs => rw [same]
    simp only [unitPower,CombSource.Division.rawIterate,pow_succ',mul_apply_eq_comp,CombSource.Division.rawAction]
  rw [step,opposite_adjoint_pair]
  change star (2*((c).value-(barC c).value))*
    inner ℂ (fourierL2 (burnolDirectRightResolvent ((barC c).value/2) (K (barC c) : BurnolL2)))
      (unitPower observation half (m-1)) = inner ℂ (oppositeForcing c) (unitPower observation half (m-1)) at read
  rw [read,actual_opposite_forcing_original_top observation nontrivial half]

/-- Both conjugate coordinates remain distinct while the actual top is expressed in the original Xi fee. -/
theorem actual_conjugate_fourier_original_top :
    inner ℂ (fourierL2 (K (barC c) : BurnolL2)) (unitPower observation half m) =
      (-2*star (oppositeBMatrix c)/((barC c).value-(c).value))*e := by
  have apart : (barC c).value-(c).value ≠ 0 := by
    intro zero
    have same := sub_eq_zero.mp zero
    have nonreal := OriginalKRealCoordinateSourceUnit.actual_original_zero_coordinate_im_ne_zero observation nontrivial half
    have part := congrArg Complex.im same
    change (star observation.coordinate).im = observation.coordinate.im at part
    rw [Complex.star_def,Complex.conj_im] at part
    exact nonreal (by linarith)
  have source := actual_conjugate_fourier_original_top_source observation nontrivial half
  have coefficient : star (2*((c).value-(barC c).value)) = 2*((barC c).value-(c).value) := by
    change star (2*(observation.coordinate-star observation.coordinate)) =
      2*(star observation.coordinate-observation.coordinate)
    simp only [star_mul,star_ofNat,star_sub,star_star]
    ring
  rw [coefficient] at source
  rw [show (-2*star (oppositeBMatrix c)/((barC c).value-(c).value))*e =
    (-2*star (oppositeBMatrix c)*e)/((barC c).value-(c).value) by ring]
  apply (eq_div_iff apart).mpr
  linear_combination source/2

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.OppositeForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
