import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFiniteSourcePrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ResponseCountingLimit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantForward
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CenteredCountingDual
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPairedBEulerJunctionSource.ResponseForcing.Source
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "P" => positionSource
local notation "b" => burnolRieszSingleFourierSourceRaw
namespace BF
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPairedBEulerJunctionSource.BandFiniteSourcePrice (sourceColumn forcingDensity boundarySourceRead finiteSourcePrice)
end BF

/-- The first original forcing column retains its entire unit, on the full raw profile. -/
theorem actual_first_raw (x:ℝ) : BF.sourceColumn 0 x=ResponseProfile.vRaw x-1 := by
 simp only [BF.sourceColumn,PsiDrive.psiMean,Matrix.cons_val_zero,
  ResponseProfile.vRaw,burnolMeanZeroFourierRaw]
 ring

/-- The second column is the opposite full analytic response, including its edge and mean. -/
theorem actual_second_raw (x:ℝ) : BF.sourceColumn 1 x= -ResponseProfile.uRaw x := by
 simp only [BF.sourceColumn,PsiDrive.psiMean,Matrix.cons_val_one,Matrix.cons_val_zero,
  ResponseProfile.uRaw,ResponseProfile.etaRaw,ResponseProfile.etaMean,
  Translator.ForcingMeanZero.edgeMean,burnolMeanZeroFourierRaw]
 ring

def quarterColumn (i:Fin 2) : Hq :=
 Constructor.compact (BF.sourceColumn i) (BandFiniteSourcePrice.source_column_continuous i)

theorem actual_first_quarter : quarterColumn 0=(Response.v:Hq)-intervalConstant q := by
 apply Lp.ext
 filter_upwards [Constructor.compact_read (BF.sourceColumn 0)
  (BandFiniteSourcePrice.source_column_continuous 0),ResponseProfile.v_read,
  Lp.coeFn_sub (Response.v:Hq) (intervalConstant q),intervalConstant_coeFn q]
  with x read response difference constant
 rw [difference,Pi.sub_apply,constant,response]
 exact read.trans (actual_first_raw x)

theorem actual_second_quarter : quarterColumn 1= -(Response.u:Hq) := by
 apply Lp.ext
 filter_upwards [Constructor.compact_read (BF.sourceColumn 1)
  (BandFiniteSourcePrice.source_column_continuous 1),ResponseProfile.u_read,
  Lp.coeFn_neg (Response.u:Hq)] with x read response negative
 rw [negative,Pi.neg_apply,response]
 exact read.trans (actual_second_raw x)

def actualSeed (i:Fin 2) : BurnolL2 := E (quarterColumn i)

theorem actual_first_seed : actualSeed 0=Response.wholeV-ConstantDual.seed := by
 rw [actualSeed,actual_first_quarter,map_sub]
 rfl

theorem actual_second_seed : actualSeed 1= -Response.wholeU := by
 rw [actualSeed,actual_second_quarter,map_neg]
 rfl

/-- Same cutoff, independent dual and full constant source; no unit contact is discarded. -/
theorem actual_same_N_reverse (N:ℕ) :
 DualSource.source N (actualSeed 0)=ResponseCounting.finite true N-DualSource.source N ConstantDual.seed ∧
 DualSource.source N (actualSeed 1)= -ResponseCounting.finite false N := by
 constructor
 · rw [actual_first_seed,CountingDual.dual_eq_adjoint,map_sub]
   rw [←CountingDual.dual_eq_adjoint,←CountingDual.dual_eq_adjoint]
   rfl
 · rw [actual_second_seed,CountingDual.dual_eq_adjoint,map_neg,←CountingDual.dual_eq_adjoint]
   rfl

/-- The full response sources have their native strong limits, including the original constant primitive. -/
theorem actual_reverse_source_limits :
 Tendsto (fun N:ℕ=>DualSource.source N (actualSeed 0)) atTop
  (𝓝 (ResponseCounting.value true-ConstantDual.value)) ∧
 Tendsto (fun N:ℕ=>DualSource.source N (actualSeed 1)) atTop
  (𝓝 (-ResponseCounting.value false)) := by
 constructor
 · exact ((ResponseCounting.finite_tendsto true).sub ConstantDual.original_tendsto).congr'
    (Eventually.of_forall (fun N=>(actual_same_N_reverse N).1.symm))
 · exact (ResponseCounting.finite_tendsto false).neg.congr'
    (Eventually.of_forall (fun N=>(actual_same_N_reverse N).2.symm))

open private forward_fourier
 from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CenteredCountingDual in
 theorem actual_same_N_forward (N:ℕ) :
 FiniteForcing.source N (fourierL2 (actualSeed 0))=
  fourierL2 (ResponseCounting.finite true N)-fourierL2 (DualSource.source N ConstantDual.seed) ∧
 FiniteForcing.source N (fourierL2 (actualSeed 1))= -fourierL2 (ResponseCounting.finite false N) := by
 rw [forward_fourier,forward_fourier,(actual_same_N_reverse N).1,(actual_same_N_reverse N).2,
  map_sub,map_neg]
 exact ⟨rfl,rfl⟩

def responseDensity (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
 star (Kernel.A c)*(star (ResponseProfile.vRaw x)*P c (Real.exp h*x)-
  star (ResponseProfile.uRaw x)*b c (Real.exp h*x))+
 star (Kernel.beta c)*(-star (ResponseProfile.uRaw x)*P c (Real.exp h*x)+
  star (ResponseProfile.vRaw x)*b c (Real.exp h*x))+
 Kernel.A c*(star (P c x)*ResponseProfile.vRaw (Real.exp h*x)-
  star (b c x)*ResponseProfile.uRaw (Real.exp h*x))+
 Kernel.beta c*(-star (P c x)*ResponseProfile.uRaw (Real.exp h*x)+
  star (b c x)*ResponseProfile.vRaw (Real.exp h*x))

def unitDensity (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
 star (Kernel.A c)*P c (Real.exp h*x)+star (Kernel.beta c)*b c (Real.exp h*x)+
 Kernel.A c*star (P c x)+Kernel.beta c*star (b c x)

/-- The full two-sided forcing is paid in the original response carrier, with its unit fee visible. -/
theorem actual_complete_forcing (c:BurnolCompletedMellinCoordinate) (h x:ℝ) :
 BF.forcingDensity c h x=responseDensity c h x-unitDensity c h x := by
 unfold BF.forcingDensity
 rw [actual_first_raw,actual_second_raw,actual_first_raw,actual_second_raw]
 simp only [star_sub,star_neg,star_one]
 unfold responseDensity unitDensity
 ring

def responseFinitePrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
 (2:ℂ)*(Real.exp (h/2):ℂ)*
  ((∫ x:ℝ in (q*Real.exp (-h))..q,responseDensity c h x-unitDensity c h x)+BF.boundarySourceRead c h)/
  (c.value+star c.value-1)

theorem actual_finite_price (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
 BF.finiteSourcePrice c h=responseFinitePrice c h := by
 unfold BF.finiteSourcePrice responseFinitePrice
 simp_rw [actual_complete_forcing]

end OriginalKPairedBEulerJunctionSource.ResponseForcing.Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
