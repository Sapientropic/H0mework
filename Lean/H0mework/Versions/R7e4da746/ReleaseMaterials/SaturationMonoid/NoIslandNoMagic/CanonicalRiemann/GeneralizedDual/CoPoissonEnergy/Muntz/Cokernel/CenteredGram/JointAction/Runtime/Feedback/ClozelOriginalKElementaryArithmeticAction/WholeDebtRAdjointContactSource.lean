import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKContactClosureSourceData
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRQuarterUnitSettlementSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.Generator.Resolvent.Gram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DilationWard

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRAdjointContactSource
open Complex Filter MeasureTheory Set FourierTransform BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource
open OriginalKPairedBEulerJunctionSource.BandFullStockEuler
open OriginalKFiniteOrderRelease.UnitPowerSource
open scoped InnerProductSpace Topology FourierTransform
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1/4 : ℝ)
local notation "p" => junctionPoint
local notation "C" => correctionRaw
local notation "DT" => TemperedDistribution ℝ ℂ
local notation "F" => fourierL2
local notation "R" => burnolDirectRightResolventCLM
local notation "P" => burnolEvenAmbientProjection
open private strong_pair from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.Generator.Resolvent.Gram
open private power_succ_left from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource

/-- The actual adjoint parameter remains independent of the source parameter. -/
def T (d : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 := (R d).adjoint

def sigma (c d : BurnolCompletedMellinCoordinate) : ℂ := star c.value+star d.value-1


private def positionCorners (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  sourceJump c 0 • step p-sourceTrace c 0 • step q

private def fourierCorners (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  sourceJump c 1 • F (step p)-sourceTrace c 1 • F (step q)

/-- These columns realize the actual delta contacts through L² source actions. -/
def positionContact (d : BurnolCompletedMellinCoordinate) (radius : ℝ) : BurnolL2 :=
  (1-star d.value) • T d (step radius)-(2 : ℂ) • step radius

def fourierContact (d : BurnolCompletedMellinCoordinate) (radius : ℝ) : BurnolL2 :=
  star d.value • T d (F (step radius))+(2 : ℂ) • F (step radius)

def contactLift (c d : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  sourceJump c 0 • positionContact d p-sourceTrace c 0 • positionContact d q-
  sourceJump c 1 • fourierContact d p+sourceTrace c 1 • fourierContact d q

def sourceEffect (c d : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  T d (regularSource c)+contactLift c d

def sourceField (c d : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (sigma c d)⁻¹ • (sourceEffect c d-(2 : ℂ) • C c)

private def regularCarrier (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  C c+positionCorners c+fourierCorners c

private def regularVelocity (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  regularSource c-(star c.value-1/2) • C c+
    (1/2 : ℂ) • positionCorners c-(1/2 : ℂ) • fourierCorners c

private theorem step_euler (radius : ℝ) (positive : 0<radius) :
    GapEuler.euler (step radius : DT)=
      (1/2 : ℂ) • (step radius : DT)-
        (radius : ℂ) • (TemperedDistribution.delta radius+TemperedDistribution.delta (-radius)) := by
  have nonzero : ((2*radius : ℝ) : ℂ)≠0 := by exact_mod_cast (mul_pos (by norm_num : (0 : ℝ)<2) positive).ne'
  have source : (step radius : DT)=((2*radius : ℝ) : ℂ) •
      (burnolAmbientGapRieszVector radius : DT) := by
    change Lp.toTemperedDistributionCLM ℂ volume 2 (_ • _) = _
    rw [map_smul,Lp.toTemperedDistributionCLM_apply]
  have derivative : TemperedDistribution.derivCLM ℂ (step radius : DT)=
      TemperedDistribution.delta (-radius)-TemperedDistribution.delta radius := by
    rw [source,map_smul,burnolGapRiesz_distribution_derivative radius positive,
      smul_smul,mul_inv_cancel₀ nonzero,one_smul]
  unfold GapEuler.euler
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    smul_apply,ContinuousLinearMap.id_apply]
  rw [derivative,map_sub,GapEuler.position_delta,GapEuler.position_delta]
  simp only [Complex.ofReal_neg]
  module

private theorem fourier_step_euler (radius : ℝ) (positive : 0<radius) :
    GapEuler.euler (F (step radius) : DT)=
      -(1/2 : ℂ) • (F (step radius) : DT)+
        (radius : ℂ) • 𝓕 (TemperedDistribution.delta radius+TemperedDistribution.delta (-radius)) := by
  have actual : 𝓕 (step radius : DT)=(F (step radius) : DT) := Lp.fourier_toTemperedDistribution_eq _
  rw [←actual,GapEuler.euler_fourier,step_euler radius positive]
  change -(fourierCLM ℂ DT) ((1/2 : ℂ) • (step radius : DT)-
      (radius : ℂ) • (TemperedDistribution.delta radius+TemperedDistribution.delta (-radius))) = _
  rw [map_sub,map_smul,map_smul]
  change -((1/2 : ℂ) • 𝓕 (step radius : DT)-
      (radius : ℂ) • 𝓕 (TemperedDistribution.delta radius+TemperedDistribution.delta (-radius))) = _
  module

private theorem actual_regular_euler (c : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (regularCarrier c : DT)=(regularVelocity c : DT) := by
  have native:=correction_euler_source c
  change GapEuler.euler (C c : DT)=(regularSource c : DT)-
    (star c.value-1/2) • (C c : DT)+contactSource c at native
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (regularCarrier c))=
    Lp.toTemperedDistributionCLM ℂ volume 2 (regularVelocity c)
  unfold regularCarrier regularVelocity positionCorners fourierCorners
  simp only [map_add,map_sub,map_smul,Lp.toTemperedDistributionCLM_apply]
  rw [native,step_euler p junctionPoint_bounds.1,step_euler q (by norm_num),
    fourier_step_euler p junctionPoint_bounds.1,fourier_step_euler q (by norm_num)]
  unfold contactSource
  simp only [map_sub,map_smul,fourierCLM_apply]
  module

private theorem actual_regular_action (c d : BurnolCompletedMellinCoordinate) :
    T d (regularVelocity c)=(2 : ℂ) • regularCarrier c+
      (star d.value-1/2) • T d (regularCarrier c) := by
  have strong:=DilationWard.strong_derivative _ _ (actual_regular_euler c)
  have scaled : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h/2) (regularCarrier c))
      ((-1/2 : ℂ) • regularVelocity c) 0 := by
    have chart : HasDerivAt (fun h : ℝ => -h/2) (-1/2 : ℝ) 0 := by
      convert! (hasDerivAt_id (0 : ℝ)).neg.div_const 2 using 1
    have moved : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation h (regularCarrier c))
        (regularVelocity c) (-0/2) := by simpa only [neg_zero,zero_div] using strong
    have composed:=moved.scomp 0 chart
    change HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h/2) (regularCarrier c))
      ((-1/2 : ℝ) • regularVelocity c) 0 at composed
    rw [←IsScalarTower.algebraMap_smul ℂ (-1/2 : ℝ) (regularVelocity c)] at composed
    convert! composed using 1
    norm_num
  apply ext_inner_right ℂ
  intro test
  have right : 1/4<(d.value/2).re := by rw [Complex.div_re];norm_num;linarith [d.rightHalf]
  have zero:=strong_pair scaled (burnolDirectRightResolventOrbit_hasDerivAt (d.value/2) right test)
  change inner ℂ (regularCarrier c) ((d.value/2-1/4) • R d test+test)+
    inner ℂ ((-1/2 : ℂ) • regularVelocity c) (R d test)=0 at zero
  simp only [inner_add_right,inner_smul_right,inner_smul_left] at zero
  unfold T
  rw [inner_add_left,inner_smul_left,inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left]
  simp only [map_neg,map_div₀,map_one,map_ofNat] at zero
  simp only [map_sub,map_div₀,map_one,map_ofNat]
  have conjugate : (starRingEnd ℂ) (star d.value)=d.value := star_star _
  rw [conjugate]
  linear_combination -2*zero

private theorem sigma_ne_zero (c d : BurnolCompletedMellinCoordinate) : sigma c d≠0 := by
  intro zero
  have realPart:=congrArg Complex.re zero
  simp only [sigma,Complex.sub_re,Complex.add_re,Complex.star_def,Complex.conj_re,Complex.one_re,Complex.zero_re] at realPart
  linarith [c.rightHalf,d.rightHalf]

/-- All four source contacts and both means generate the actual full adjoint field. -/
theorem actual_source_action (c d : BurnolCompletedMellinCoordinate) :
    T d (C c)=sourceField c d := by
  have native:=actual_regular_action c d
  have balance : sigma c d • T d (C c)=
      T d (regularSource c)+contactLift c d-(2 : ℂ) • C c := by
    unfold regularVelocity regularCarrier at native
    simp only [map_add,map_sub,map_smul] at native
    unfold positionCorners fourierCorners at native
    unfold sigma contactLift positionContact fourierContact
    simp only [map_sub,map_smul] at native ⊢
    linear_combination (norm := module) -native
  have result:=congrArg (fun value : BurnolL2 => (sigma c d)⁻¹ • value) balance
  rw [smul_smul,inv_mul_cancel₀ (sigma_ne_zero c d),one_smul] at result
  exact result

private theorem full_source_balance (c d : BurnolCompletedMellinCoordinate) :
    sourceEffect c d=sigma c d • T d (C c)+(2 : ℂ) • C c := by
  have native:=actual_source_action c d
  unfold sourceField at native
  have full:=congrArg (fun value : BurnolL2 => sigma c d • value) native
  rw [smul_smul,mul_inv_cancel₀ (sigma_ne_zero c d),one_smul] at full
  linear_combination (norm := module) -full

/-- The literal R_d source can consume this cotest without changing either occurrence. -/
theorem actual_R_cotest (c d : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    inner ℂ (C c) (R d value)=inner ℂ (sourceField c d) value := by
  rw [←actual_source_action]
  exact (ContinuousLinearMap.adjoint_inner_left (R d) _ _).symm

private theorem correction_physical_price (c : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (physical : value∈evenBurnolClosedFace q) : inner ℂ (C c) value=0 := by
  let state : BurnolPaAmbientCarrier := ⟨value,physical⟩
  have source:=(evenBurnolClosedFace q).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right
    state (sourceAction c)
  change inner ℂ (P (sourceAction c) : BurnolL2) value=inner ℂ (sourceAction c) value at source
  rw [source_action_projection,inner_sub_left] at source
  linear_combination -source

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

/-- The original exact-order Division consumes the complete regular/contact field jointly. -/
theorem original_Pa_contact_effect (test : BurnolPaAmbientCarrier)
    (member : test∈burnolCompactCoPoissonClosedRange) :
    inner ℂ (T c (regularSource c)+contactLift c c) (test : BurnolL2)=0 := by
  have returned:=CombSource.Division.whole_pa_physical observation nontrivial half.down 1
    (generatedRiemannXiZeroOrder_pos observation nontrivial) test member
  change R c (test : BurnolL2)∈evenBurnolClosedFace q at returned
  have acted:=correction_physical_price c _ returned
  have input:=correction_physical_price c (test : BurnolL2) test.property
  have adjoint : inner ℂ (T c (C c)) (test : BurnolL2)=0 := by
    rw [T,ContinuousLinearMap.adjoint_inner_left]
    exact acted
  change inner ℂ (sourceEffect c c) (test : BurnolL2)=0
  rw [full_source_balance,inner_add_left,inner_smul_left,inner_smul_left,adjoint,input,mul_zero,mul_zero,add_zero]

/-- The complete same-source regular/contact word reaches its actual first Pa release. -/
theorem original_Pa_first_release (test : BurnolPaAmbientCarrier)
    (member : test∈burnolCompactCoPoissonClosedRange) :
    let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
    let powers:=CombSource.Division.rawIterate observation half.down
    (∀ k : Nat,k<m → inner ℂ (sourceEffect c c) (powers k (test : BurnolL2))=0) ∧
      inner ℂ (sourceEffect c c) (powers m (test : BurnolL2))=
        star (sigma c c)*burnolPaResolventSourceCoefficient c test*
          inner ℂ (C c) (unitPower observation half m) := by
  dsimp only
  let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
  let powers:=CombSource.Division.rawIterate observation half.down
  have physical (k : Nat) (bound : k≤m) (value : BurnolPaAmbientCarrier)
      (inside : value∈burnolCompactCoPoissonClosedRange) : inner ℂ (C c) (powers k (value : BurnolL2))=0 :=
    correction_physical_price c _ (CombSource.Division.whole_pa_physical observation nontrivial half.down
      k bound value inside)
  have action (k : Nat) : inner ℂ (sourceEffect c c) (powers k (test : BurnolL2))=
      star (sigma c c)*inner ℂ (C c) (powers (k+1) (test : BurnolL2))+
        2*inner ℂ (C c) (powers k (test : BurnolL2)) := by
    rw [full_source_balance,inner_add_left,inner_smul_left,inner_smul_left,T,
      ContinuousLinearMap.adjoint_inner_left]
    change star (sigma c c)*inner ℂ (C c) (R c (powers k (test : BurnolL2)))+_= _
    have next:=power_succ_left observation half k (test : BurnolL2)
    change powers (k+1) (test : BurnolL2)=R c (powers k (test : BurnolL2)) at next
    rw [←next]
    simp only [map_ofNat]
  constructor
  · intro k before
    rw [action,physical k (by omega) test member,physical (k+1) (by omega) test member]
    ring
  · have split:=actual_Pa_power_split observation half test member m
    have corrected:=physical m le_rfl (burnolPaSourceCorrection c ⟨test,member⟩)
      (burnolPaSourceCorrection_mem c _)
    change powers (m+1) (test : BurnolL2)=
      powers m (burnolPaSourceCorrection c ⟨test,member⟩ : BurnolL2)+
        burnolPaResolventSourceCoefficient c test • unitPower observation half m at split
    rw [action,split,inner_add_right,inner_smul_right,corrected,physical m le_rfl test member]
    ring

end OriginalWholeDebtRAdjointContactSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
