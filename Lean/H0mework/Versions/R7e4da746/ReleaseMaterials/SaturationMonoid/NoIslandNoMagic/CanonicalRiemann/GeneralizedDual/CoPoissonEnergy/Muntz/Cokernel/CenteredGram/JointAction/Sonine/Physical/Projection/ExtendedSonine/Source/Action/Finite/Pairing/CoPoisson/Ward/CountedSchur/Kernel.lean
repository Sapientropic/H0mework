import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.Crossing


set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
open Complex Filter MeasureTheory Set
open OriginalRieszSource OriginalPaPhysicalGreen
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "D" => burnolMultiplicativeDilation
local notation "F" => fourierL2
local notation "cut" => originalPhysicalCutoff
open private sqrt_exp from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.InverseAction

def innerWindow (a:ℝ) (state:Hq) : Hq := Rq (cut (q/a) (E state))

def crossRaw (a:ℝ) (state:Hq) (x:ℝ) : ℂ :=
  (symmetricInterval (q/a)).indicator (fun t=>Constructor.fourierRaw state (a*t)) x-
    Constructor.fourierRaw (innerWindow a state) (a*x)

private theorem innerWindow_extension (a:ℝ) (state:Hq) :
    E (innerWindow a state)=cut (q/a) (E state) := by
  change cut q (cut (q/a) (E state))=cut (q/a) (E state)
  apply Lp.ext
  filter_upwards [originalPhysicalCutoff_coeFn q (cut (q/a) (E state)),
    originalPhysicalCutoff_coeFn (q/a) (E state),burnolQuarterZeroExtension_coe state]
    with x outer inner extended
  rw [outer]
  by_cases inside:x∈symmetricInterval q
  · exact indicator_of_mem inside _
  · rw [indicator_of_notMem inside,inner]
    by_cases innerInside:x∈symmetricInterval (q/a)
    · rw [indicator_of_mem innerInside,extended,indicator_of_notMem inside]
    · rw [indicator_of_notMem innerInside]

private theorem innerWindow_read (a:ℝ) (state:Hq) :
    (innerWindow a state:ℝ→ℂ)=ᵐ[μq] (symmetricInterval (q/a)).indicator state := by
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (cut (q/a) (E state)),
    ae_restrict_of_ae (originalPhysicalCutoff_coeFn (q/a) (E state)),
    ae_restrict_of_ae (burnolQuarterZeroExtension_coe state),
    ae_restrict_mem (measurableSet_symmetricInterval q)] with x restricted clipped extended inside
  change innerWindow a state x=cut (q/a) (E state) x at restricted
  rw [restricted,clipped]
  by_cases innerInside:x∈symmetricInterval (q/a)
  · rw [indicator_of_mem innerInside,indicator_of_mem innerInside,extended,indicator_of_mem inside]
  · rw [indicator_of_notMem innerInside,indicator_of_notMem innerInside]

/-- The literal inverse-square-root source weight cancels the actual normalized dilation amplitude. -/
private theorem normalized_dilation_raw (a:ℝ) (positive:0<a) (value:BurnolL2) (raw:ℝ→ℂ)
    (represents:(value:ℝ→ℂ)=ᵐ[volume] raw) :
    ((Real.sqrt a:ℂ)⁻¹ • D (Real.log a) value:BurnolL2)=ᵐ[volume] (fun x=>raw (a*x)) := by
  have qmp:=Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
    (r:=Real.exp (Real.log a)) (Real.exp_ne_zero _)
  have moved:∀ᵐ x:ℝ ∂volume,value (Real.exp (Real.log a)*x)=raw (Real.exp (Real.log a)*x) := by
    simpa only [smul_eq_mul] using qmp.ae represents
  have scale : (Real.sqrt a:ℂ)⁻¹*(Real.exp (Real.log a/2):ℂ)=1 := by
    rw [←sqrt_exp a positive,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr positive).ne')]
  filter_upwards [Lp.coeFn_smul (Real.sqrt a:ℂ)⁻¹ (D (Real.log a) value),
    burnolMultiplicativeDilation_coeFn (Real.log a) value,moved] with x scaled dilated actual
  rw [scaled]
  change (Real.sqrt a:ℂ)⁻¹*D (Real.log a) value x=raw (a*x)
  rw [dilated]
  change (Real.sqrt a:ℂ)⁻¹*((Real.exp (Real.log a/2):ℂ)*value (Real.exp (Real.log a)*x))=_
  rw [actual,←mul_assoc,scale,one_mul,Real.exp_log positive]

private theorem restriction_read (value:BurnolL2) (raw:ℝ→ℂ)
    (represents:(value:ℝ→ℂ)=ᵐ[volume] raw) :
    (Rq value:ℝ→ℂ)=ᵐ[μq] raw := by
  exact (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) value).trans (ae_restrict_of_ae represents)

private theorem restricted_cut_read (radius:ℝ) (value:BurnolL2) (raw:ℝ→ℂ)
    (represents:(value:ℝ→ℂ)=ᵐ[volume] raw) :
    (Rq (cut radius value):ℝ→ℂ)=ᵐ[μq] (symmetricInterval radius).indicator raw := by
  apply restriction_read
  filter_upwards [originalPhysicalCutoff_coeFn radius value,represents] with x clipped actual
  rw [clipped]
  by_cases inside:x∈symmetricInterval radius
  · rw [indicator_of_mem inside,indicator_of_mem inside,actual]
  · rw [indicator_of_notMem inside,indicator_of_notMem inside]

/-- Exact raw source on the quarter carrier; no projection margin or counted response is supplied. -/
theorem crossWindow_raw (a:ℝ) (positive:0<a) (state:Hq) :
    (crossWindow a state:ℝ→ℂ)=ᵐ[μq] crossRaw a state := by
  have firstFourier : (F (E state):ℝ→ℂ)=ᵐ[volume] Constructor.fourierRaw state :=
    burnolRadiusFourierL2_zeroExtension_ae_eq_raw state
  have secondFourier : (F (E (innerWindow a state)):ℝ→ℂ)=ᵐ[volume]
      Constructor.fourierRaw (innerWindow a state) := burnolRadiusFourierL2_zeroExtension_ae_eq_raw _
  let first:BurnolL2 := (Real.sqrt a:ℂ)⁻¹ • D (Real.log a) (F (E state))
  let second:BurnolL2 := (Real.sqrt a:ℂ)⁻¹ • D (Real.log a) (F (E (innerWindow a state)))
  have firstRead:=restricted_cut_read (q/a) first _ (normalized_dilation_raw a positive _ _ firstFourier)
  have secondRead:=restriction_read second _ (normalized_dilation_raw a positive _ _ secondFourier)
  have expression:crossWindow a state=Rq (cut (q/a) first)-Rq second := by
    rw [crossWindow,←innerWindow_extension a state]
    simp only [first,second,originalPhysicalCutoff,map_sub,map_smul,smul_sub]
  rw [expression]
  filter_upwards [Lp.coeFn_sub (Rq (cut (q/a) first)) (Rq second),firstRead,secondRead]
    with x difference left right
  rw [difference]
  change Rq (cut (q/a) first) x-Rq second x=crossRaw a state x
  rw [left,right]
  rfl

/-- Both literal window restrictions enter the original finite Fourier integral. -/
theorem crossRaw_integral (a:ℝ) (state:Hq) (x:ℝ) :
    crossRaw a state x=
      (symmetricInterval (q/a)).indicator
        (fun t=>∫ y:ℝ in (-q)..q,Constructor.phase (a*t) y*state y) x-
      ∫ y:ℝ in (-q)..q,Constructor.phase (a*x) y*((symmetricInterval (q/a)).indicator state) y := by
  have inner:=Constructor.fourierRaw_congr (innerWindow a state)
    ((symmetricInterval (q/a)).indicator state) (innerWindow_read a state)
  unfold crossRaw
  rw [inner,Constructor.fourierRaw_integral]
  congr 1
  apply congrArg (fun f:ℝ→ℂ=>(symmetricInterval (q/a)).indicator f x)
  funext t
  exact Constructor.fourierRaw_integral state (a*t)

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
