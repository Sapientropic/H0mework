import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseCoreJumpMean
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCoreUnitProgramme
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKSourceGramAction OriginalKSourceResolventReconstruction OriginalKFixedBoundarySourceFibre
open OriginalKElementaryArithmeticAction OriginalKCoefficientBFiniteAction OriginalKExteriorCoPoissonAction
open OriginalFullLossRAction OriginalReverseCoreJumpMean
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "F" => fourierL2
local notation "T" => burnolTateReciprocalL2
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

open private gamma conjugate_zero unitCurrent FT boxProgram unitTailProgram
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitRProgram
open private SBWeight SBSlope SB_regular SB_reverse_actual
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FullLossRAction
open private seed_twice pair_raw dilation_raw box_price tail_price unitCurrent_raw forward_actual
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseCoreJumpMean

def unitKernel (i:Fin 2) : BurnolL2 :=
  if i=0 then ConstantDual.seed else F ConstantDual.seed
def unitProfile (i:Fin 2) : ℝ→ℂ :=
  if i=0 then ConstantDual.seedRaw else Constructor.fourierRaw (fun _=>1)
private def flippedProfile (i:Fin 2) : ℝ→ℂ :=
  if i=0 then Constructor.fourierRaw (fun _=>1) else ConstantDual.seedRaw
def reciprocalUnitProfile (i:Fin 2) : ℝ→ℂ :=
  burnolTateReciprocalRaw (flippedProfile i)

private theorem fourier_seed_raw :
    (F ConstantDual.seed:ℝ→ℂ)=ᵐ[volume] Constructor.fourierRaw (fun _=>1) := by
  have actual:=burnolRadiusFourierL2_zeroExtension_ae_eq_raw (intervalConstant q)
  have raw:=Constructor.fourierRaw_congr _ _ (intervalConstant_coeFn q)
  change (F ConstantDual.seed:ℝ→ℂ)=ᵐ[volume] Constructor.fourierRaw (intervalConstant q) at actual
  rwa [raw] at actual

private theorem unit_raw (i:Fin 2) :
    (unitKernel i:ℝ→ℂ)=ᵐ[volume] unitProfile i := by
  fin_cases i
  · exact ConstantDual.seed_coeFn
  · exact fourier_seed_raw

private theorem unit_fourier_twice (i:Fin 2) : F (F (unitKernel i))=unitKernel i := by
  fin_cases i
  · exact seed_twice
  · exact congrArg F seed_twice

private theorem reciprocal_raw (i:Fin 2) :
    (T (F (unitKernel i)):ℝ→ℂ)=ᵐ[volume] reciprocalUnitProfile i := by
  have actual:(F (unitKernel i):ℝ→ℂ)=ᵐ[volume] flippedProfile i := by
    fin_cases i
    · exact fourier_seed_raw
    · simpa only [unitKernel,Fin.isValue,Fin.mk_one,one_ne_zero,ite_false,seed_twice,
        flippedProfile] using ConstantDual.seed_coeFn
  have pulled:=burnolTateReciprocalRaw_ae_congr (Lp.memLp (F (unitKernel i)))
    ((Lp.memLp (F (unitKernel i))).ae_eq actual) actual
  filter_upwards [burnolTateReciprocalL2_coeFn (F (unitKernel i)),pulled] with x source raw
  rw [source,raw]
  rfl

private theorem FT_pair (i:Fin 2) (value:BurnolL2) :
    inner ℂ (unitKernel i) (FT value)=inner ℂ (T (F (unitKernel i))) value := by
  have actual:=fourierL2.inner_map_map (F (unitKernel i)) (T value)
  rw [unit_fourier_twice] at actual
  exact actual.trans (OriginalRieszFiniteSynthesis.tate_pairing _ _).symm

def boundaryUnitPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2)
    (profile:ℝ→ℂ) : ℂ :=
  pairedMellinTranslationCharacter c.value h*rawPair (unitProfile i) profile-
    (1/2:ℂ)*(rawPair (unitProfile i) (dilationProfile h profile)+
      rawPair (unitProfile i) (dilationProfile (-h) profile))

def lossUnitPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2)
    (profile:ℝ→ℂ) : ℂ :=
  boxPrice (unitProfile i) q (q*Real.exp h) (SBWeight c h) (SBSlope c h) profile+
    centeringMean c h 1*rawPair (unitProfile i) profile-
    (boxPrice (reciprocalUnitProfile i) (bandLower h) 4 (positiveWeight c h 0)
        (deriv (positiveWeight c h 0)) profile+
      centeringMean c h 0*tailPrice (reciprocalUnitProfile i) profile)

/-- Both original unit means are calculated from the complete source programme. -/
def coreUnitPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) : ℂ :=
  boundaryUnitPrice c h i (elementaryReverseRaw c)-
    (1/2:ℂ)*lossUnitPrice c h i ConstantDual.sawtoothRaw

def currentUnitPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2) : ℂ :=
  (2*gamma c)*boundaryUnitPrice c h i (elementaryReverseRaw (barC c))-
    (2*gamma (barC c))*boundaryUnitPrice c h i (elementaryReverseRaw c)-
    (((c.value-star c.value)*gamma (barC c))*(1/2:ℂ))*
      lossUnitPrice c h i (unitCurrentProfile c)

private theorem boundary_price (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2)
    (value:BurnolL2) (raw:ℝ→ℂ) (actual:(value:ℝ→ℂ)=ᵐ[volume] raw) :
    inner ℂ (unitKernel i) (finiteBoundaryAction c h value)=boundaryUnitPrice c h i raw := by
  unfold finiteBoundaryAction boundaryUnitPrice
  rw [inner_sub_right,inner_smul_right,inner_smul_right,inner_add_right]
  rw [pair_raw _ _ _ _ (unit_raw i) actual,
    pair_raw _ _ _ _ (unit_raw i) (dilation_raw h value raw actual),
    pair_raw _ _ _ _ (unit_raw i) (dilation_raw (-h) value raw actual)]

private theorem loss_price (c:BurnolCompletedMellinCoordinate) (h:ℝ) (i:Fin 2)
    (value:BurnolL2) (raw:ℝ→ℂ) (actual:(value:ℝ→ℂ)=ᵐ[volume] raw) :
    inner ℂ (unitKernel i)
      (boxProgram q (q*Real.exp h) (SBWeight c h) (SBSlope c h) value+
        centeringMean c h 1 • value-
        FT (boxProgram (bandLower h) 4 (positiveWeight c h 0) (deriv (positiveWeight c h 0)) value+
          centeringMean c h 0 • unitTailProgram value))=lossUnitPrice c h i raw := by
  have regular:ContinuousOn (deriv (positiveWeight c h 0)) (Icc (bandLower h) 4) :=
    (positiveWeight_deriv_continuousOn c h 0).mono (fun _ inside=>(bandLower_pos h).trans_le inside.1)
  unfold lossUnitPrice
  rw [inner_sub_right,inner_add_right,inner_smul_right,FT_pair,inner_add_right,inner_smul_right]
  rw [box_price _ value _ raw (unit_raw i) actual _ _ _ _ (by norm_num) (SB_regular c h).continuousOn,
    pair_raw _ value _ raw (unit_raw i) actual,
    box_price _ value _ raw (reciprocal_raw i) actual _ _ _ _ (bandLower_pos h) regular,
    tail_price _ value _ raw (reciprocal_raw i) actual]

theorem core_unit_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (i:Fin 2) :
    inner ℂ (unitKernel i) (coreReverseSource c zero h)=coreUnitPrice c h i := by
  unfold coreReverseSource coreUnitPrice
  rw [inner_sub_right,inner_smul_right,boundary_price c h i _ _ (elementary_reverse_raw c zero),
    SB_reverse_actual c h nn,forward_actual c h,
    loss_price c h i _ _ ConstantDual.value_coeFn]

theorem current_unit_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (i:Fin 2) :
    inner ℂ (unitKernel i) (completeCoreRCurrent c zero h)=currentUnitPrice c h i := by
  unfold completeCoreRCurrent currentUnitPrice
  rw [inner_sub_right,inner_sub_right,inner_smul_right,inner_smul_right,inner_smul_right,
    boundary_price c h i _ _ (elementary_reverse_raw (barC c) (conjugate_zero c zero)),
    boundary_price c h i _ _ (elementary_reverse_raw c zero),
    loss_price c h i _ _ (unitCurrent_raw c zero)]

end OriginalCoreUnitProgramme
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
