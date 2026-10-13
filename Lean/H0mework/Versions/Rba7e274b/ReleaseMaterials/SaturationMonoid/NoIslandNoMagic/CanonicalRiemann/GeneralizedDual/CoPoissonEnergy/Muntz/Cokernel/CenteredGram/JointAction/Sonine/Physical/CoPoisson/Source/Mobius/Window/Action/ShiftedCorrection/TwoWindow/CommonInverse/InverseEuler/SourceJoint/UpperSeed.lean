import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.SourceJoint.CommonField
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Seed
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.SourceJoint
open Complex MeasureTheory Set Filter OriginalRieszSource
open scoped InnerProductSpace Topology
open OriginalTwoWindowInverseForcing OriginalCommonInverseForcing InverseEuler
namespace Seed
export OriginalRieszFinitePairing.CoPoisson (positionSeed fourierSeed bandRaw positionSeed_pairing fourierSeed_pairing)
end Seed
local notation "q" => (1/4:ℝ)

def upperSeedFactor (h : ℝ) : ℂ := -(Real.exp (h/4):ℂ)/2
private def positiveUpperRaw (h : ℝ) (profile : ℝ→ℂ) (x : ℝ) : ℂ :=
  if q≤x ∧ x≤q*Real.exp h then (Real.exp (-h/4):ℂ)*profile (Real.exp (-h)*x) else 0

private theorem positive_upper_band_read (h : ℝ) (nonnegative : 0≤h)
    (field : BurnolL2) (profile : ℝ→ℂ)
    (fieldRead : (field:ℝ→ℂ)=ᵐ[volume] (sourceBand h).indicator (fun y=>profile (Real.exp (-h/2)*y))) :
    (burnolMultiplicativeDilation (-h/2) field:ℝ→ℂ)=ᵐ[volume] positiveUpperRaw h profile := by
  have qmp : Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp (-h/2)*x) volume volume := by
    simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
      (r:=Real.exp (-h/2)) (Real.exp_ne_zero _))
  have lower : lowerRadius h=Real.exp (-h/2)*q := by
    unfold lowerRadius FixedWindowFourierReaction.actualRadius
    rw [show (-h)/2=-h/2 by ring]
    ring
  have upper : upperRadius h=Real.exp (-h/2)*(q*Real.exp h) := by
    unfold upperRadius FixedWindowFourierReaction.actualRadius
    rw [← mul_assoc, mul_comm (Real.exp (-h/2)) q,mul_assoc,← Real.exp_add,show -h/2+h=h/2 by ring]
  have twice (x : ℝ) : Real.exp (-h/2)*(Real.exp (-h/2)*x)=Real.exp (-h)*x := by
    rw [← mul_assoc,← Real.exp_add,show -h/2+-h/2=-h by ring]
  filter_upwards [burnolMultiplicativeDilation_coeFn (-h/2) field,qmp.ae fieldRead] with x dilated actual
  have inside : Real.exp (-h/2)*x∈sourceBand h ↔ q≤x ∧ x≤q*Real.exp h := by
    unfold sourceBand
    rw [uIcc_of_le (source_radii_ordered h nonnegative),mem_Icc,lower,upper]
    constructor
    · intro bounds
      exact ⟨le_of_mul_le_mul_left bounds.1 (Real.exp_pos _),le_of_mul_le_mul_left bounds.2 (Real.exp_pos _)⟩
    · intro bounds
      exact ⟨mul_le_mul_of_nonneg_left bounds.1 (Real.exp_pos _).le,
        mul_le_mul_of_nonneg_left bounds.2 (Real.exp_pos _).le⟩
  rw [dilated]
  unfold burnolL2RawNormalizedDilation
  rw [actual]
  unfold positiveUpperRaw
  rw [show (-h/2)/2=-h/4 by ring]
  by_cases active : q≤x ∧ x≤q*Real.exp h
  · rw [indicator_of_mem (inside.mpr active),if_pos active]
    congr 1
    exact congrArg profile (twice x)
  · rw [indicator_of_notMem (fun member=>active (inside.mp member)),if_neg active,mul_zero]

private theorem even_upper_band_read (h : ℝ) (nonnegative : 0≤h)
    (field : BurnolL2) (profile : ℝ→ℂ)
    (fieldRead : (field:ℝ→ℂ)=ᵐ[volume] (sourceBand h).indicator (fun y=>profile (Real.exp (-h/2)*y))) :
    (burnolAmbientEvenPart (burnolMultiplicativeDilation (-h/2) field):ℝ→ℂ)=ᵐ[volume]
      fun x=>upperSeedFactor h*Seed.bandRaw h profile x := by
  let transformed:=burnolMultiplicativeDilation (-h/2) field
  have actual:=positive_upper_band_read h nonnegative field profile fieldRead
  have notPlus : ∀ᵐ x:ℝ ∂volume,x≠q := by simp [ae_iff,measure_singleton]
  have notMinus : ∀ᵐ x:ℝ ∂volume,x≠-q := by simp [ae_iff,measure_singleton]
  have factor : upperSeedFactor h*(-(Real.exp (-h/2):ℂ))=(Real.exp (-h/4):ℂ)/2 := by
    unfold upperSeedFactor
    have exponential : (Real.exp (h/4):ℂ)*(Real.exp (-h/2):ℂ)=(Real.exp (-h/4):ℂ) := by
      rw [← Complex.ofReal_mul,← Real.exp_add,show h/4+-h/2=-h/4 by ring]
    linear_combination exponential/2
  filter_upwards [Lp.coeFn_smul (1/2:ℂ) (transformed+reflectL2 transformed),
    Lp.coeFn_add transformed (reflectL2 transformed),
    Lp.coeFn_compMeasurePreserving transformed negMeasurePreserving,actual,
    negMeasurePreserving.quasiMeasurePreserving.ae actual,notPlus,notMinus]
    with x scalar addition reflection plus minus plusNe minusNe
  change reflectL2 transformed x=transformed (-x) at reflection
  unfold burnolAmbientEvenPart
  rw [scalar]
  change (1/2:ℂ)*(transformed+reflectL2 transformed:BurnolL2) x=_
  rw [addition]
  change (1/2:ℂ)*(transformed x+reflectL2 transformed x)=_
  rw [reflection,plus,minus]
  unfold positiveUpperRaw Seed.bandRaw
  by_cases positive : 0≤x
  · rw [abs_of_nonneg positive]
    have negativeInactive : ¬(q≤-x ∧ -x≤q*Real.exp h) := by intro inside; linarith [inside.1]
    rw [if_neg negativeInactive,add_zero]
    by_cases active : q<x ∧ x≤q*Real.exp h
    · rw [if_pos ⟨active.1.le,active.2⟩,if_pos active]
      linear_combination -profile (Real.exp (-h)*x)*factor
    · have inactive : ¬(q≤x ∧ x≤q*Real.exp h) := by
        intro inside
        exact active ⟨lt_of_le_of_ne inside.1 plusNe.symm,inside.2⟩
      rw [if_neg inactive,if_neg active,mul_zero,mul_zero]
  · have negative : x≤0 := (lt_of_not_ge positive).le
    rw [abs_of_nonpos negative]
    have positiveInactive : ¬(q≤x ∧ x≤q*Real.exp h) := by intro inside; linarith [inside.1]
    rw [if_neg positiveInactive,zero_add]
    by_cases active : q < -x ∧ -x≤q*Real.exp h
    · rw [if_pos ⟨active.1.le,active.2⟩,if_pos active]
      linear_combination -profile (Real.exp (-h)*(-x))*factor
    · have inactive : ¬(q≤-x ∧ -x≤q*Real.exp h) := by
        intro inside
        apply active
        refine ⟨lt_of_le_of_ne inside.1 ?_,inside.2⟩
        intro equal
        apply minusNe
        linarith
      rw [if_neg inactive,if_neg active,mul_zero,mul_zero]

private theorem seed_from_even_read (field seed : BurnolL2) (profile : ℝ→ℂ) (h : ℝ)
    (fieldRead : (field:ℝ→ℂ)=ᵐ[volume] fun x=>upperSeedFactor h*Seed.bandRaw h profile x)
    (seedRead : ∀ test:BurnolL2,inner ℂ test seed=∫ x:ℝ,inner ℂ (test x) (Seed.bandRaw h profile x)) :
    field=upperSeedFactor h • seed := by
  apply ext_inner_left ℂ
  intro test
  rw [inner_smul_right,seedRead,L2.inner_def,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [fieldRead] with x actual
  rw [actual]
  exact inner_smul_right (test x) (Seed.bandRaw h profile x) (upperSeedFactor h)

theorem actual_upper_seed_fields (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) :
    burnolAmbientEvenPart (burnolMultiplicativeDilation (-h/2) (pBand coordinate h (-h/2)))=
      upperSeedFactor h • Seed.positionSeed coordinate h ∧
    burnolAmbientEvenPart (burnolMultiplicativeDilation (-h/2) (bBand coordinate h (-h/2)))=
      upperSeedFactor h • Seed.fourierSeed coordinate h := by
  constructor
  · apply seed_from_even_read _ _ (p coordinate) h
    · exact even_upper_band_read h nonnegative _ _ (pBand_raw coordinate h (-h/2))
    · exact Seed.positionSeed_pairing coordinate h nonnegative
  · apply seed_from_even_read _ _ (b coordinate) h
    · exact even_upper_band_read h nonnegative _ _ (bBand_raw coordinate h (-h/2))
    · exact Seed.fourierSeed_pairing coordinate h nonnegative

theorem actual_upper_common_seed (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) :
    upperSourceField coordinate h=upperSeedFactor h •
      (Seed.positionSeed coordinate h+fourierL2 (Seed.fourierSeed coordinate h)) := by
  obtain ⟨position,fourier⟩:=actual_upper_seed_fields coordinate h nonnegative
  unfold upperSourceField burnolAmbientEvenPart at *
  rw [map_add]
  have distributed : (1/2:ℂ) •
      ((burnolMultiplicativeDilation (-h/2) (pBand coordinate h (-h/2))+
        fourierL2 (burnolMultiplicativeDilation (-h/2) (bBand coordinate h (-h/2))))+
       (reflectL2 (burnolMultiplicativeDilation (-h/2) (pBand coordinate h (-h/2)))+
        reflectL2 (fourierL2 (burnolMultiplicativeDilation (-h/2) (bBand coordinate h (-h/2))))))=
      (1/2:ℂ) • (burnolMultiplicativeDilation (-h/2) (pBand coordinate h (-h/2))+
        reflectL2 (burnolMultiplicativeDilation (-h/2) (pBand coordinate h (-h/2))))+
      fourierL2 ((1/2:ℂ) • (burnolMultiplicativeDilation (-h/2) (bBand coordinate h (-h/2))+
        reflectL2 (burnolMultiplicativeDilation (-h/2) (bBand coordinate h (-h/2))))) := by
    rw [map_smul,map_add,fourierL2_reflectL2_commute]
    module
  rw [distributed,position,fourier,map_smul,← smul_add]

end OriginalCommonInverseForcing.SourceJoint
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
