import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.Columns
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing
open Complex MeasureTheory Set Filter OriginalRieszSource
open scoped Topology InnerProductSpace ENNReal
open OriginalTwoWindowInverseForcing
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "L" => burnolMeanZeroOneMinusSquare
local notation "q" => (1/4:ℝ)

def inversePartner (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    BurnolQuarterMeanZeroCarrier×BurnolQuarterMeanZeroCarrier :=
  (S (inverseCotest coordinate h).1-(sourceColumns coordinate h).1.2,
   S (inverseCotest coordinate h).2-(sourceColumns coordinate h).2.2)

private theorem full_inverse_pair (cb cp x : BurnolQuarterMeanZeroCarrier)
    (inverse : L x=cb-S cp) :
    x-S (S x-cp)=cb ∧ (S x-cp)-S x=-cp := by
  change x-S (S x)=cb-S cp at inverse
  constructor
  · rw [map_sub]
    calc
      x-(S (S x)-S cp)=(x-S (S x))+S cp := by abel
      _=(cb-S cp)+S cp := by rw [inverse]
      _=cb := by abel
  · abel

theorem actual_inverse_pair (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (inverseCotest coordinate h).1-S (inversePartner coordinate h).1=(sourceColumns coordinate h).1.1 ∧
    (inversePartner coordinate h).1-S (inverseCotest coordinate h).1=-(sourceColumns coordinate h).1.2 ∧
    (inverseCotest coordinate h).2-S (inversePartner coordinate h).2=(sourceColumns coordinate h).2.1 ∧
    (inversePartner coordinate h).2-S (inverseCotest coordinate h).2=-(sourceColumns coordinate h).2.2 := by
  obtain ⟨lower,upper⟩:=actual_inverse_cotest coordinate h
  obtain ⟨lowerB,lowerP⟩:=full_inverse_pair _ _ _ lower
  obtain ⟨upperB,upperP⟩:=full_inverse_pair _ _ _ upper
  exact ⟨lowerB,lowerP,upperB,upperP⟩

private theorem fourier_pairing_even_left (state field : BurnolQuarterMeanZeroCarrier)
    (even : reflectRestricted q (state:BurnolQuarterIntervalL2)=state) :
    inner ℂ state (S field)=inner ℂ (S state) field := by
  have paired:=congrArg (starRingEnd ℂ)
    (OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection field state even)
  simpa only [inner_conj_symm] using paired

private theorem actual_response_pair (cb cp x y : BurnolQuarterMeanZeroCarrier)
    (bEquation : x-S y=cb) (pEquation : y-S x=-cp) :
    inner ℂ Response.u cb-inner ℂ Response.v cp=inner ℂ Response.eta x ∧
    inner ℂ Response.v cb-inner ℂ Response.u cp=inner ℂ Response.eta y := by
  have cpEquation : cp=S x-y := by
    have reflected:=congrArg Neg.neg pEquation
    simpa only [neg_sub,neg_neg] using reflected.symm
  have uX:=fourier_pairing_even_left Response.u x Response.u_reflection
  have uY:=fourier_pairing_even_left Response.u y Response.u_reflection
  have vX:=fourier_pairing_even_left Response.v x Response.v_reflection
  have vY:=fourier_pairing_even_left Response.v y Response.v_reflection
  change inner ℂ Response.u (S x)=inner ℂ Response.v x at uX
  change inner ℂ Response.u (S y)=inner ℂ Response.v y at uY
  have etaX:=congrArg (fun state:BurnolQuarterMeanZeroCarrier=>inner ℂ state x) Response.source_pair_equation
  have etaY:=congrArg (fun state:BurnolQuarterMeanZeroCarrier=>inner ℂ state y) Response.source_pair_equation
  rw [inner_sub_left] at etaX etaY
  change inner ℂ Response.u x-inner ℂ (S Response.v) x=inner ℂ Response.eta x at etaX
  change inner ℂ Response.u y-inner ℂ (S Response.v) y=inner ℂ Response.eta y at etaY
  rw [← bEquation,cpEquation,inner_sub_right,inner_sub_right,inner_sub_right,inner_sub_right]
  constructor
  · linear_combination etaX-uY-vX
  · linear_combination etaY-uX-vY

theorem actual_response_inverse_read (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    inner ℂ Response.u (sourceColumns coordinate h).1.1-
      inner ℂ Response.v (sourceColumns coordinate h).1.2=inner ℂ Response.eta (inverseCotest coordinate h).1 ∧
    inner ℂ Response.v (sourceColumns coordinate h).1.1-
      inner ℂ Response.u (sourceColumns coordinate h).1.2=inner ℂ Response.eta (inversePartner coordinate h).1 ∧
    inner ℂ Response.u (sourceColumns coordinate h).2.1-
      inner ℂ Response.v (sourceColumns coordinate h).2.2=inner ℂ Response.eta (inverseCotest coordinate h).2 ∧
    inner ℂ Response.v (sourceColumns coordinate h).2.1-
      inner ℂ Response.u (sourceColumns coordinate h).2.2=inner ℂ Response.eta (inversePartner coordinate h).2 := by
  obtain ⟨lowerB,lowerP,upperB,upperP⟩:=actual_inverse_pair coordinate h
  obtain ⟨lowerU,lowerV⟩:=actual_response_pair _ _ _ _ lowerB lowerP
  obtain ⟨upperU,upperV⟩:=actual_response_pair _ _ _ _ upperB upperP
  exact ⟨lowerU,lowerV,upperU,upperV⟩

end OriginalCommonInverseForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
