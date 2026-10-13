import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Endpoint
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.InverseEuler
open Complex OriginalRieszSource
open scoped InnerProductSpace
open OriginalTwoWindowInverseForcing OriginalCommonInverseForcing
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "L" => burnolMeanZeroOneMinusSquare

private theorem joint_euler_resolvent
    (X Cb Cp EX EY ECb ECp BX BY : BurnolQuarterMeanZeroCarrier) (weight : ℂ)
    (inverse : L X=Cb-S Cp)
    (first : EX+S EY=ECb+BY) (second : EY+S EX=BX-ECp) :
    L (EX+weight • X)=(ECb+weight • Cb)+S (ECp-weight • Cp)+BY-S BX := by
  have unshifted : L EX=ECb+S ECp+BY-S BX := by
    change EX-S (S EX)=_
    calc
      _=(EX+S EY)-S (EY+S EX) := by rw [map_add]; module
      _=(ECb+BY)-S (BX-ECp) := by rw [first,second]
      _=_ := by rw [map_sub]; module
  rw [map_add,map_smul,unshifted,inverse,map_sub,map_smul]
  module

def fullBandDrive (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    BurnolQuarterMeanZeroCarrier×BurnolQuarterMeanZeroCarrier :=
  (bandEndpoint h (-h/2) (bLeg coordinate (h/2))+
    S (bandEndpoint h (-h/2) (pLeg coordinate (h/2)))-
    (forceBColumn coordinate h (-h/2) (h/2)+S (forcePColumn coordinate h (-h/2) (h/2)))+
    endpointReaction (yProfile coordinate h).1-S (endpointReaction (xProfile coordinate h).1),
   bandEndpoint h (h/2) (bLeg coordinate (-h/2))+
    S (bandEndpoint h (h/2) (pLeg coordinate (-h/2)))-
    (forceBColumn coordinate h (h/2) (-h/2)+S (forcePColumn coordinate h (h/2) (-h/2)))+
    endpointReaction (yProfile coordinate h).2-S (endpointReaction (xProfile coordinate h).2))

theorem actual_common_inverse_euler_action (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) :
    L ((xEuler coordinate h).1+lambda coordinate • (inverseCotest coordinate h).1)=
      (fullBandDrive coordinate h).1 ∧
    L ((xEuler coordinate h).2+lambda coordinate • (inverseCotest coordinate h).2)=
      (fullBandDrive coordinate h).2 := by
  obtain ⟨lowerInverse,upperInverse⟩:=actual_inverse_cotest coordinate h
  obtain ⟨lowerB,lowerP,upperB,upperP⟩:=actual_two_euler_actions coordinate h nonnegative
  have lower:=joint_euler_resolvent _ _ _ _ _ _ _ _ _ (lambda coordinate) lowerInverse lowerB lowerP
  have upper:=joint_euler_resolvent _ _ _ _ _ _ _ _ _ (lambda coordinate) upperInverse upperB upperP
  have pLower : pCotestEuler coordinate h (-h/2) (h/2)-lambda coordinate •
      cotestColumn (-h/2) (pBand coordinate h (h/2))=
      bandEndpoint h (-h/2) (pLeg coordinate (h/2))-forcePColumn coordinate h (-h/2) (h/2) := by
    simpa only [neg_smul,sub_eq_add_neg] using source_p_cotest_action coordinate h (-h/2) (h/2) nonnegative
  have pUpper : pCotestEuler coordinate h (h/2) (-h/2)-lambda coordinate •
      cotestColumn (h/2) (pBand coordinate h (-h/2))=
      bandEndpoint h (h/2) (pLeg coordinate (-h/2))-forcePColumn coordinate h (h/2) (-h/2) := by
    simpa only [neg_smul,sub_eq_add_neg] using source_p_cotest_action coordinate h (h/2) (-h/2) nonnegative
  change L ((xEuler coordinate h).1+lambda coordinate • (inverseCotest coordinate h).1)=
    (bCotestEuler coordinate h (-h/2) (h/2)+lambda coordinate •
      cotestColumn (-h/2) (bBand coordinate h (h/2)))+
    S (pCotestEuler coordinate h (-h/2) (h/2)-lambda coordinate •
      cotestColumn (-h/2) (pBand coordinate h (h/2)))+
    endpointReaction (yProfile coordinate h).1-S (endpointReaction (xProfile coordinate h).1) at lower
  change L ((xEuler coordinate h).2+lambda coordinate • (inverseCotest coordinate h).2)=
    (bCotestEuler coordinate h (h/2) (-h/2)+lambda coordinate •
      cotestColumn (h/2) (bBand coordinate h (-h/2)))+
    S (pCotestEuler coordinate h (h/2) (-h/2)-lambda coordinate •
      cotestColumn (h/2) (pBand coordinate h (-h/2)))+
    endpointReaction (yProfile coordinate h).2-S (endpointReaction (xProfile coordinate h).2) at upper
  rw [source_b_cotest_action coordinate h (-h/2) (h/2) nonnegative,pLower,map_sub] at lower
  rw [source_b_cotest_action coordinate h (h/2) (-h/2) nonnegative,pUpper,map_sub] at upper
  constructor
  · rw [lower]
    unfold fullBandDrive
    module
  · rw [upper]
    unfold fullBandDrive
    module

end OriginalCommonInverseForcing.InverseEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
