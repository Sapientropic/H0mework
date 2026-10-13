import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.Profiles
import H0mework.Versions.V2.Arithmetic.RiemannSourceGreen.ProbeCutoffValue
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing
open Complex MeasureTheory Set Filter OriginalRieszSource OriginalPaPhysicalGreen
open scoped Topology InnerProductSpace ENNReal
open OriginalTwoWindowInverseForcing
local notation "q" => (1/4:ℝ)
private def positiveCut (h : ℝ) (field : BurnolL2) : BurnolL2 :=
  ((Lp.memLp field).indicator (show MeasurableSet (sourceBand h) from measurableSet_uIcc)).toLp
    ((sourceBand h).indicator (field:ℝ→ℂ))
private theorem positiveCut_raw (h : ℝ) (field : BurnolL2) :
    (positiveCut h field:ℝ→ℂ)=ᵐ[volume] (sourceBand h).indicator (field:ℝ→ℂ) := MemLp.coeFn_toLp _

private theorem positive_cut_even (h : ℝ) (nonnegative : 0≤h) (field : BurnolL2)
    (even : reflectL2 field=field) :
    burnolAmbientEvenPart (positiveCut h field)=(1/2:ℂ)•
      (originalPhysicalCutoff (upperRadius h) field-originalPhysicalCutoff (lowerRadius h) field) := by
  have ordered:=source_radii_ordered h nonnegative
  have lowerPositive : 0<lowerRadius h := by unfold lowerRadius FixedWindowFourierReaction.actualRadius; positivity
  have sourceEven : ∀ᵐ x:ℝ ∂volume,field (-x)=field x := by
    filter_upwards [Lp.coeFn_compMeasurePreserving field negMeasurePreserving] with x reflected
    change reflectL2 field x=field (-x) at reflected
    rw [even] at reflected
    exact reflected.symm
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (1/2:ℂ) (positiveCut h field+reflectL2 (positiveCut h field)),
    Lp.coeFn_add (positiveCut h field) (reflectL2 (positiveCut h field)),
    Lp.coeFn_compMeasurePreserving (positiveCut h field) negMeasurePreserving,
    positiveCut_raw h field,negMeasurePreserving.quasiMeasurePreserving.ae (positiveCut_raw h field),
    sourceEven,Lp.coeFn_smul (1/2:ℂ)
      (originalPhysicalCutoff (upperRadius h) field-originalPhysicalCutoff (lowerRadius h) field),
    Lp.coeFn_sub (originalPhysicalCutoff (upperRadius h) field) (originalPhysicalCutoff (lowerRadius h) field),
    originalPhysicalCutoff_coeFn (upperRadius h) field,originalPhysicalCutoff_coeFn (lowerRadius h) field,
    volume.ae_ne (lowerRadius h),volume.ae_ne (-lowerRadius h)]
    with x leftScalar leftAdd reflected direct negative fieldEven rightScalar rightSub upper lower notLower notNegativeLower
  change reflectL2 (positiveCut h field) x=positiveCut h field (-x) at reflected
  unfold burnolAmbientEvenPart
  rw [leftScalar,rightScalar]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [leftAdd,rightSub]
  simp only [Pi.add_apply,Pi.sub_apply]
  rw [reflected,direct,negative,upper,lower]
  have bandBounds (y : ℝ) : y∈sourceBand h ↔ lowerRadius h≤y ∧ y≤upperRadius h := by
    unfold sourceBand
    rw [uIcc_of_le ordered]
    rfl
  have upperBounds (y : ℝ) : y∈symmetricInterval (upperRadius h) ↔ -upperRadius h≤y ∧ y≤upperRadius h := Iff.rfl
  have lowerBounds (y : ℝ) : y∈symmetricInterval (lowerRadius h) ↔ -lowerRadius h≤y ∧ y≤lowerRadius h := Iff.rfl
  by_cases positive : x∈sourceBand h
  · have bx:=(bandBounds x).mp positive
    have negativeOutside : -x∉sourceBand h := by
      intro inside
      have bn:=(bandBounds (-x)).mp inside
      linarith
    have upperInside : x∈symmetricInterval (upperRadius h) := (upperBounds x).mpr ⟨by linarith,bx.2⟩
    have lowerOutside : x∉symmetricInterval (lowerRadius h) := by
      intro inside
      have bl:=(lowerBounds x).mp inside
      exact notLower (le_antisymm bl.2 bx.1)
    rw [indicator_of_mem positive,indicator_of_notMem negativeOutside,
      indicator_of_mem upperInside,indicator_of_notMem lowerOutside,add_zero,sub_zero]
  · by_cases negativeInside : -x∈sourceBand h
    · have bn:=(bandBounds (-x)).mp negativeInside
      have upperInside : x∈symmetricInterval (upperRadius h) := (upperBounds x).mpr ⟨by linarith,by linarith⟩
      have lowerOutside : x∉symmetricInterval (lowerRadius h) := by
        intro inside
        have bl:=(lowerBounds x).mp inside
        exact notNegativeLower (by linarith)
      rw [indicator_of_notMem positive,indicator_of_mem negativeInside,
        indicator_of_mem upperInside,indicator_of_notMem lowerOutside,zero_add,sub_zero,fieldEven]
    · have sameWindow : x∈symmetricInterval (upperRadius h) ↔ x∈symmetricInterval (lowerRadius h) := by
        constructor
        · intro inside
          have bu:=(upperBounds x).mp inside
          apply (lowerBounds x).mpr
          constructor
          · by_contra below
            have negInside : -x∈sourceBand h := (bandBounds (-x)).mpr ⟨by linarith,by linarith⟩
            exact negativeInside negInside
          · by_contra above
            have posInside : x∈sourceBand h := (bandBounds x).mpr ⟨by linarith,bu.2⟩
            exact positive posInside
        · intro inside
          have bl:=(lowerBounds x).mp inside
          exact (upperBounds x).mpr ⟨by linarith,by linarith⟩
      rw [indicator_of_notMem positive,indicator_of_notMem negativeInside,add_zero]
      by_cases outer : x∈symmetricInterval (upperRadius h)
      · rw [indicator_of_mem outer,indicator_of_mem (sameWindow.mp outer),sub_self]
      · rw [indicator_of_notMem outer,indicator_of_notMem (fun inner=>outer (sameWindow.mpr inner)),sub_self]

private theorem evenPart_dilation (scale : ℝ) (field : BurnolL2) :
    burnolAmbientEvenPart (burnolMultiplicativeDilation scale field)=
      burnolMultiplicativeDilation scale (burnolAmbientEvenPart field) := by
  unfold burnolAmbientEvenPart
  rw [reflectL2_burnolMultiplicativeDilation,map_smul,map_add]
private theorem evenPart_smul (scalar : ℂ) (field : BurnolL2) :
    burnolAmbientEvenPart (scalar•field)=scalar•burnolAmbientEvenPart field := by
  unfold burnolAmbientEvenPart
  rw [map_smul]
  module

def windowKernelColumn (state : BurnolQuarterMeanZeroCarrier) (h testScale leg : ℝ) :
    BurnolQuarterMeanZeroCarrier := Constructor.zeroMean (burnolQuarterRestriction
      (fourierL2 (burnolMultiplicativeDilation (-testScale)
        (originalPhysicalCutoff (upperRadius h) (burnolMultiplicativeDilation leg (fourierL2 (whole state)))-
         originalPhysicalCutoff (lowerRadius h) (burnolMultiplicativeDilation leg (fourierL2 (whole state)))))))

theorem source_cotest_window_sandwich (state : BurnolQuarterMeanZeroCarrier)
    (even : reflectRestricted q (state:BurnolQuarterIntervalL2)=state)
    (h testScale leg : ℝ) (nonnegative : 0≤h) :
    cotestColumn testScale (sourceFourierBand state h leg)=
      ((Real.exp (-leg/2):ℂ)/2)•windowKernelColumn state h testScale leg := by
  have nativeEven : reflectL2 (burnolMultiplicativeDilation leg (fourierL2 (whole state)))=
      burnolMultiplicativeDilation leg (fourierL2 (whole state)) := by
    rw [reflectL2_burnolMultiplicativeDilation,← fourierL2_reflectL2_commute,whole_even state even]
  have source : sourceFourierBand state h leg=(Real.exp (-leg/2):ℂ)•
      positiveCut h (burnolMultiplicativeDilation leg (fourierL2 (whole state))) := rfl
  rw [source]
  unfold cotestColumn
  rw [← fourierL2_burnolAmbientEvenPart,evenPart_dilation,evenPart_smul,
    positive_cut_even h nonnegative _ nativeEven]
  unfold windowKernelColumn Constructor.zeroMean
  simp only [map_smul,smul_smul]
  congr 1
  ring


end OriginalCommonInverseForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
