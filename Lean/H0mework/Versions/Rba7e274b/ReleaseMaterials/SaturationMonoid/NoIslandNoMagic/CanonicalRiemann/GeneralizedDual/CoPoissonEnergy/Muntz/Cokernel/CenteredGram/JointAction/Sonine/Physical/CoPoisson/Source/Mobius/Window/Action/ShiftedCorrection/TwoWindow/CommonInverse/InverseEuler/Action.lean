import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Ward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.InverseEuler
open Complex Filter FourierTransform MeasureTheory Set OriginalRieszSource
open scoped ENNReal InnerProductSpace Topology
open OriginalTwoWindowInverseForcing OriginalCommonInverseForcing
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "L" => burnolMeanZeroOneMinusSquare

def returnEulerRaw (state : BurnolQuarterMeanZeroCarrier) : ℝ→ℂ :=
  eulerRaw (burnolMeanZeroFourierRaw state)
    (Constructor.fourierDerivative (state:BurnolQuarterIntervalL2))
theorem returnEulerRaw_continuous (state : BurnolQuarterMeanZeroCarrier) :
    Continuous (returnEulerRaw state) :=
  eulerRaw_continuous _ _ (meanZeroRaw_continuous state) (state_derivative_continuous state)
def returnEuler (state : BurnolQuarterMeanZeroCarrier) : BurnolQuarterMeanZeroCarrier :=
  eulerState (burnolMeanZeroFourierRaw state)
    (Constructor.fourierDerivative (state:BurnolQuarterIntervalL2))
    (meanZeroRaw_continuous state) (state_derivative_continuous state)

def endpointReaction (raw : ℝ→ℂ) : BurnolQuarterMeanZeroCarrier :=
  raw q • Constructor.endpointColumn q+raw (-q) • Constructor.endpointColumn (-q)

private theorem compact_congr (left right : ℝ→ℂ)
    (hl : Continuous left) (hr : Continuous right) (same : left=right) :
    Constructor.compact left hl=Constructor.compact right hr := by
  subst right
  rfl
private theorem compact_fourier (raw : ℝ→ℂ) (continuous : Continuous raw) :
    Constructor.compact (Constructor.fourierRaw raw) (Constructor.fourierRaw_continuous raw continuous)=
      burnolTruncatedFourier (Constructor.compact raw continuous) := by
  have same:=Constructor.fourierRaw_congr _ _ (Constructor.compact_read raw continuous)
  apply Lp.ext
  filter_upwards [Constructor.compact_read (Constructor.fourierRaw raw)
    (Constructor.fourierRaw_continuous raw continuous),
    Constructor.truncatedFourier_read (Constructor.compact raw continuous)] with x left right
  rw [left,right]
  exact (congrFun same x).symm

theorem meanZero_source_ward (state : BurnolQuarterMeanZeroCarrier) (raw derivative : ℝ→ℂ)
    (rawContinuous : Continuous raw) (derivativeContinuous : Continuous derivative)
    (actualDerivative : ∀ x:ℝ,HasDerivAt raw (derivative x) x)
    (stateRead : (state:BurnolQuarterIntervalL2)=ᵐ[μq] raw) :
    returnEuler state+S (eulerState raw derivative rawContinuous derivativeContinuous)=
      endpointReaction raw := by
  let mean:=burnolQuarterMeanCoefficient (burnolTruncatedFourier (state:BurnolQuarterIntervalL2))
  have FourierSame:=Constructor.fourierRaw_congr _ _ stateRead
  have derivativeSame (x : ℝ) :
      Constructor.fourierDerivative (state:BurnolQuarterIntervalL2) x=
        Constructor.fourierDerivative raw x := by
    have source:=state_fourier_hasDerivAt state x
    rw [FourierSame] at source
    exact source.unique (Constructor.fourierRaw_hasDerivAt raw rawContinuous x)
  let rhs:=((q:ℂ)*raw q) • Constructor.phase q+
    ((q:ℂ)*raw (-q)) • Constructor.phase (-q)-(mean/2) • (fun _:ℝ=>(1:ℂ))
  have rhsContinuous : Continuous rhs := by
    have plus:=Constructor.phaseContinuous q
    have minus:=Constructor.phaseContinuous (-q)
    dsimp only [rhs]
    fun_prop
  have rawEquation : returnEulerRaw state+Constructor.fourierRaw (eulerRaw raw derivative)=rhs := by
    funext x
    have ward:=raw_fourier_ward raw derivative rawContinuous derivativeContinuous actualDerivative x
    change (x:ℂ)*Constructor.fourierDerivative (state:BurnolQuarterIntervalL2) x+
      (1/2:ℂ)*(Constructor.fourierRaw (state:BurnolQuarterIntervalL2) x-mean)+
      Constructor.fourierRaw (eulerRaw raw derivative) x=rhs x
    rw [derivativeSame,FourierSame]
    dsimp only [rhs,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_one]
    rw [Constructor.phase_symm q x,Constructor.phase_symm (-q) x]
    linear_combination ward
  have fullState:=compact_congr
    (returnEulerRaw state+Constructor.fourierRaw (eulerRaw raw derivative)) rhs
    ((returnEulerRaw_continuous state).add (Constructor.fourierRaw_continuous _
      (eulerRaw_continuous raw derivative rawContinuous derivativeContinuous))) rhsContinuous rawEquation
  rw [Constructor.compact_add _ _ (returnEulerRaw_continuous state)
    (Constructor.fourierRaw_continuous _
      (eulerRaw_continuous raw derivative rawContinuous derivativeContinuous)),
    compact_fourier _ (eulerRaw_continuous raw derivative rawContinuous derivativeContinuous)] at fullState
  have rhsState : Constructor.compact rhs rhsContinuous=
      ((q:ℂ)*raw q) • Constructor.compact (Constructor.phase q) (Constructor.phaseContinuous q)+
      ((q:ℂ)*raw (-q)) • Constructor.compact (Constructor.phase (-q)) (Constructor.phaseContinuous (-q))-
      (mean/2) • intervalConstant q := by
    change Constructor.compact
      (((q:ℂ)*raw q) • Constructor.phase q+((q:ℂ)*raw (-q)) • Constructor.phase (-q)-
        (mean/2) • (fun _:ℝ=>(1:ℂ))) rhsContinuous=_
    rw [Constructor.compact_sub _ _
      (((Constructor.phaseContinuous q).const_smul ((q:ℂ)*raw q)).add
        ((Constructor.phaseContinuous (-q)).const_smul ((q:ℂ)*raw (-q))))
      (continuous_const.const_smul (mean/2)),
      Constructor.compact_add _ _
        ((Constructor.phaseContinuous q).const_smul ((q:ℂ)*raw q))
        ((Constructor.phaseContinuous (-q)).const_smul ((q:ℂ)*raw (-q))),
      Constructor.compact_smul _ _ (Constructor.phaseContinuous q),
      Constructor.compact_smul _ _ (Constructor.phaseContinuous (-q)),
      Constructor.compact_smul _ _ continuous_const,Constructor.compact_one]
  rw [rhsState] at fullState
  have full:=congrArg Constructor.zeroMean fullState
  simp only [map_add,map_sub,map_smul,Constructor.zeroMean_constant,smul_zero,sub_zero] at full
  change returnEuler state+Constructor.zeroMean
    (burnolTruncatedFourier (eulerAmbient raw derivative rawContinuous derivativeContinuous))=_ at full
  have returned : S (eulerState raw derivative rawContinuous derivativeContinuous)=
      Constructor.zeroMean (burnolTruncatedFourier
        (eulerAmbient raw derivative rawContinuous derivativeContinuous))-
      burnolQuarterMeanCoefficient (eulerAmbient raw derivative rawContinuous derivativeContinuous) •
        Constructor.zeroMean (burnolTruncatedFourier (intervalConstant q)) := by
    change Constructor.zeroMean (burnolTruncatedFourier
      (eulerState raw derivative rawContinuous derivativeContinuous:BurnolQuarterIntervalL2))=_
    unfold eulerState
    rw [Constructor.zeroMean_read,map_sub,map_smul,map_sub,map_smul]
  rw [eulerAmbient_mean state raw derivative rawContinuous derivativeContinuous actualDerivative stateRead]
    at returned
  rw [returned]
  calc
    _=(returnEuler state+Constructor.zeroMean (burnolTruncatedFourier
      (eulerAmbient raw derivative rawContinuous derivativeContinuous)))-
      ((raw q+raw (-q))/2) • Constructor.zeroMean (burnolTruncatedFourier (intervalConstant q)) := by module
    _=(((q:ℂ)*raw q) • Constructor.zeroMean
      (Constructor.compact (Constructor.phase q) (Constructor.phaseContinuous q))+
      ((q:ℂ)*raw (-q)) • Constructor.zeroMean
      (Constructor.compact (Constructor.phase (-q)) (Constructor.phaseContinuous (-q))))-
      ((raw q+raw (-q))/2) • Constructor.zeroMean (burnolTruncatedFourier (intervalConstant q)) := by rw [full]
    _=_ := by
      unfold endpointReaction Constructor.endpointColumn
      simp only [map_sub,map_smul]
      module

theorem eulerState_add (f g df dg : ℝ→ℂ)
    (hf : Continuous f) (hg : Continuous g) (hdf : Continuous df) (hdg : Continuous dg) :
    eulerState (f+g) (df+dg) (hf.add hg) (hdf.add hdg)=
      eulerState f df hf hdf+eulerState g dg hg hdg := by
  have same : eulerRaw (f+g) (df+dg)=eulerRaw f df+eulerRaw g dg := by
    funext x
    simp only [eulerRaw,Pi.add_apply]
    ring
  unfold eulerState eulerAmbient
  rw [compact_congr _ _ _ ((eulerRaw_continuous f df hf hdf).add
    (eulerRaw_continuous g dg hg hdg)) same,Constructor.compact_add,map_add]
theorem eulerState_sub (f g df dg : ℝ→ℂ)
    (hf : Continuous f) (hg : Continuous g) (hdf : Continuous df) (hdg : Continuous dg) :
    eulerState (f-g) (df-dg) (hf.sub hg) (hdf.sub hdg)=
      eulerState f df hf hdf-eulerState g dg hg hdg := by
  have same : eulerRaw (f-g) (df-dg)=eulerRaw f df-eulerRaw g dg := by
    funext x
    simp only [eulerRaw,Pi.sub_apply]
    ring
  unfold eulerState eulerAmbient
  rw [compact_congr _ _ _ ((eulerRaw_continuous f df hf hdf).sub
    (eulerRaw_continuous g dg hg hdg)) same,Constructor.compact_sub,map_sub]

def xEuler (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    BurnolQuarterMeanZeroCarrier×BurnolQuarterMeanZeroCarrier :=
  (eulerState (xProfile coordinate h).1 (xDerivative coordinate h).1
      (xProfile_continuous coordinate h).1 (actual_derivatives_continuous coordinate h).1,
   eulerState (xProfile coordinate h).2 (xDerivative coordinate h).2
      (xProfile_continuous coordinate h).2 (actual_derivatives_continuous coordinate h).2.2.1)
def yEuler (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    BurnolQuarterMeanZeroCarrier×BurnolQuarterMeanZeroCarrier :=
  (eulerState (yProfile coordinate h).1 (yDerivative coordinate h).1
      (yProfile_continuous coordinate h).1 (actual_derivatives_continuous coordinate h).2.1,
   eulerState (yProfile coordinate h).2 (yDerivative coordinate h).2
      (yProfile_continuous coordinate h).2 (actual_derivatives_continuous coordinate h).2.2.2)
def bCotestEuler (coordinate : BurnolCompletedMellinCoordinate) (h scale leg : ℝ) :
    BurnolQuarterMeanZeroCarrier :=
  eulerState (bCotestRaw coordinate h scale leg) (evenBandDerivative h scale (bLeg coordinate leg))
    (bCotestRaw_continuous coordinate h scale leg)
    (evenBandDerivative_continuous h scale _ (bLeg_continuousOn coordinate h leg))
def pCotestEuler (coordinate : BurnolCompletedMellinCoordinate) (h scale leg : ℝ) :
    BurnolQuarterMeanZeroCarrier :=
  eulerState (pCotestRaw coordinate h scale leg) (evenBandDerivative h scale (pLeg coordinate leg))
    (pCotestRaw_continuous coordinate h scale leg)
    (evenBandDerivative_continuous h scale _ (pLeg_continuousOn coordinate h leg))

theorem actual_two_euler_actions (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) :
    (xEuler coordinate h).1+S (yEuler coordinate h).1=
      bCotestEuler coordinate h (-h/2) (h/2)+endpointReaction (yProfile coordinate h).1 ∧
    (yEuler coordinate h).1+S (xEuler coordinate h).1=
      endpointReaction (xProfile coordinate h).1-pCotestEuler coordinate h (-h/2) (h/2) ∧
    (xEuler coordinate h).2+S (yEuler coordinate h).2=
      bCotestEuler coordinate h (h/2) (-h/2)+endpointReaction (yProfile coordinate h).2 ∧
    (yEuler coordinate h).2+S (xEuler coordinate h).2=
      endpointReaction (xProfile coordinate h).2-pCotestEuler coordinate h (h/2) (-h/2) := by
  obtain ⟨lowerX,lowerY,upperX,upperY⟩:=actual_inverse_profiles coordinate h nonnegative
  have exLower : (xEuler coordinate h).1=bCotestEuler coordinate h (-h/2) (h/2)+
      returnEuler (inversePartner coordinate h).1 := eulerState_add _ _ _ _ _ _ _ _
  have eyLower : (yEuler coordinate h).1=returnEuler (inverseCotest coordinate h).1-
      pCotestEuler coordinate h (-h/2) (h/2) := eulerState_sub _ _ _ _ _ _ _ _
  have exUpper : (xEuler coordinate h).2=bCotestEuler coordinate h (h/2) (-h/2)+
      returnEuler (inversePartner coordinate h).2 := eulerState_add _ _ _ _ _ _ _ _
  have eyUpper : (yEuler coordinate h).2=returnEuler (inverseCotest coordinate h).2-
      pCotestEuler coordinate h (h/2) (-h/2) := eulerState_sub _ _ _ _ _ _ _ _
  have wardLowerX:=meanZero_source_ward _ _ _ (xProfile_continuous coordinate h).1
    (actual_derivatives_continuous coordinate h).1
    (fun x=>(xProfile_hasDerivAt coordinate h x).1) lowerX
  have wardLowerY:=meanZero_source_ward _ _ _ (yProfile_continuous coordinate h).1
    (actual_derivatives_continuous coordinate h).2.1
    (fun x=>(yProfile_hasDerivAt coordinate h x).1) lowerY
  have wardUpperX:=meanZero_source_ward _ _ _ (xProfile_continuous coordinate h).2
    (actual_derivatives_continuous coordinate h).2.2.1
    (fun x=>(xProfile_hasDerivAt coordinate h x).2) upperX
  have wardUpperY:=meanZero_source_ward _ _ _ (yProfile_continuous coordinate h).2
    (actual_derivatives_continuous coordinate h).2.2.2
    (fun x=>(yProfile_hasDerivAt coordinate h x).2) upperY
  change returnEuler (inverseCotest coordinate h).1+S (xEuler coordinate h).1=_ at wardLowerX
  change returnEuler (inversePartner coordinate h).1+S (yEuler coordinate h).1=_ at wardLowerY
  change returnEuler (inverseCotest coordinate h).2+S (xEuler coordinate h).2=_ at wardUpperX
  change returnEuler (inversePartner coordinate h).2+S (yEuler coordinate h).2=_ at wardUpperY
  constructor
  · rw [exLower,add_assoc,wardLowerY]
  constructor
  · rw [eyLower]
    calc
      _=(returnEuler (inverseCotest coordinate h).1+S (xEuler coordinate h).1)-
        pCotestEuler coordinate h (-h/2) (h/2) := by module
      _=_ := by rw [wardLowerX]
  constructor
  · rw [exUpper,add_assoc,wardUpperY]
  · rw [eyUpper]
    calc
      _=(returnEuler (inverseCotest coordinate h).2+S (xEuler coordinate h).2)-
        pCotestEuler coordinate h (h/2) (-h/2) := by module
      _=_ := by rw [wardUpperX]

end OriginalCommonInverseForcing.InverseEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
