import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeForwardCore
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiForwardDriftTransport
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussNativeEnergy GaussNativeForm SourceQuantumConfigurationHilbert
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeDilation SourceCoframeVolumeCurrent
open SourceClockPhiCoframeForwardCore
open Set Filter
open scoped Topology ContDiff
private theorem scale_comp (a b:ℝ)(z:SourceCoordinateSlice):scale a (scale b z)=scale (a*b) z:=by
  simp only [scale,smul_smul]

private theorem backward_comp (s t:ℝ)(hs:0 ≤ s)(ht:0 ≤ t)
    (z:SourceCoordinateSlice)(hz:18*(s+t)<GaussNativeEnergy.volume z):
    backwardPoint t (backwardPoint s z)=backwardPoint (s+t) z := by
  have hzs:18*s<GaussNativeEnergy.volume z:=by linarith
  have hzt:18*t<GaussNativeEnergy.volume (backwardPoint s z):=by
    rw [backward_volume s hs z hzs];linarith
  have hrs:=backward_ratio_pos s hs z hzs
  have hrt:=backward_ratio_pos t ht _ hzt
  have hr:backwardRatio t (backwardPoint s z)*backwardRatio s z=backwardRatio (s+t) z:=by
    unfold backwardRatio
    rw [backward_volume s hs z hzs]
    field_simp [show GaussNativeEnergy.volume z≠0 by linarith,
      show GaussNativeEnergy.volume z-18*s≠0 by linarith]
    ring
  change scale ((backwardRatio t (backwardPoint s z))^(1/3:ℝ))
    (scale ((backwardRatio s z)^(1/3:ℝ)) z)=scale ((backwardRatio (s+t) z)^(1/3:ℝ)) z
  rw [scale_comp,←Real.mul_rpow hrt.le hrs.le,hr]

private theorem forward_value_add (s t:ℝ)(hs:0 ≤ s)(ht:0 ≤ t)(f:QuantumTest)
    (z:SourceCoordinateSlice)(word:Occupation):
    forwardValue s (sourceForwardCore t ht f) z word=forwardValue (s+t) f z word := by
  by_cases hzs:18*s<GaussNativeEnergy.volume z
  · have hv:=backward_volume s hs z hzs
    by_cases hzt:18*t<GaussNativeEnergy.volume (backwardPoint s z)
    · have hsum:18*(s+t)<GaussNativeEnergy.volume z:=by rw [hv] at hzt;linarith
      simp only [forwardValue,if_pos hzs,if_pos hsum]
      change _*forwardValue t f (backwardPoint s z) word=_
      simp only [forwardValue,if_pos hzt]
      have hr:backwardRatio s z*backwardRatio t (backwardPoint s z)=backwardRatio (s+t) z:=by
        unfold backwardRatio
        rw [hv]
        field_simp [show GaussNativeEnergy.volume z≠0 by linarith,
          show GaussNativeEnergy.volume z-18*s≠0 by linarith]
        ring
      rw [backward_comp s t hs ht z hsum,←mul_assoc,←Complex.ofReal_mul]
      have hp:=Real.mul_rpow (z:=((word.card+3:ℝ)/2)) (backward_ratio_pos s hs z hzs).le
        (backward_ratio_pos t ht _ hzt).le
      change Real.rpow (backwardRatio s z*backwardRatio t (backwardPoint s z)) _=
        Real.rpow (backwardRatio s z) _*Real.rpow (backwardRatio t (backwardPoint s z)) _ at hp
      rw [←hp,hr]
    · have hsum:¬18*(s+t)<GaussNativeEnergy.volume z:=by rw [hv] at hzt;linarith
      simp only [forwardValue,if_pos hzs,if_neg hsum]
      change _*forwardValue t f (backwardPoint s z) word=0
      simp only [forwardValue,if_neg hzt,PiLp.zero_apply,mul_zero]
  · have hsum:¬18*(s+t)<GaussNativeEnergy.volume z:=by linarith
    simp only [forwardValue,if_neg hzs,if_neg hsum,PiLp.zero_apply]

theorem actual_forward_add (s t:ℝ)(hs:0 ≤ s)(ht:0 ≤ t):
    sourceForwardCore s hs*sourceForwardCore t ht=sourceForwardCore (s+t) (by linarith) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  exact forward_value_add s t hs ht f z word

private theorem actual_forward_commute_point (t:ℝ)(ht:0 ≤ t)(f:QuantumTest)
    (z:physicalChart)(word:Occupation):
    forwardGenerator (sourceForwardCore t ht f) z.val word=
      sourceForwardCore t ht (forwardGenerator f) z.val word := by
  let h:ℝ→ℂ:=fun s=>if 18*t<GaussNativeEnergy.volume z.val then
    (Real.rpow (backwardRatio t z.val) ((word.card+3:ℝ)/2):ℂ)*
      forwardValue s f (backwardPoint t z.val) word else 0
  have hd:HasDerivAt h (sourceForwardCore t ht (forwardGenerator f) z.val word) 0 := by
    by_cases hz:18*t<GaussNativeEnergy.volume z.val
    · let hb:physicalChart:=⟨backwardPoint t z.val,backward_chart t ht z hz⟩
      have hd:=(forward_value_zero_jet f hb word).const_mul
        (Real.rpow (backwardRatio t z.val) ((word.card+3:ℝ)/2):ℂ)
      dsimp only [h]
      simp only [if_pos hz]
      change HasDerivAt (fun s=>_*forwardValue s f (backwardPoint t z.val) word)
        (forwardValue t (forwardGenerator f) z.val word) 0
      rw [forwardValue,if_pos hz]
      change HasDerivAt (fun s=>(Real.rpow (backwardRatio t z.val) ((word.card+3:ℝ)/2):ℂ)*
        forwardValue s f (backwardPoint t z.val) word)
        ((Real.rpow (backwardRatio t z.val) ((word.card+3:ℝ)/2):ℂ)*
          forwardGenerator f (backwardPoint t z.val) word) 0
      simpa only [hb] using! hd
    · simp only [h,if_neg hz]
      change HasDerivAt (fun _ :ℝ=>0) (forwardValue t (forwardGenerator f) z.val word) 0
      simp only [forwardValue,if_neg hz,PiLp.zero_apply]
      exact hasDerivAt_const (0:ℝ) (0:ℂ)
  have he:∀s∈Ici (0:ℝ),forwardValue s (sourceForwardCore t ht f) z.val word=h s := by
    intro s hs
    have ha:=forward_value_add s t hs ht f z.val word
    have hb:=forward_value_add t s ht hs f z.val word
    rw [add_comm t s] at hb
    rw [←hb] at ha
    dsimp only [h]
    change _=if _ then _ else _
    rw [ha]
    change forwardValue t (sourceForwardCore s hs f) z.val word=_
    by_cases hz:18*t<GaussNativeEnergy.volume z.val
    · simp only [forwardValue,if_pos hz]
      rfl
    · simp only [forwardValue,if_neg hz,PiLp.zero_apply]
  have hleft:=(forward_value_zero_jet (sourceForwardCore t ht f) z word).hasDerivWithinAt (s:=Ici 0)
  have hright:=hd.hasDerivWithinAt (s:=Ici 0)
  have hleft':HasDerivWithinAt h (forwardGenerator (sourceForwardCore t ht f) z.val word) (Ici 0) 0:=
    hleft.congr (fun s hs=>(he s hs).symm) (he 0 self_mem_Ici).symm
  have hud:UniqueDiffWithinAt ℝ (Ici (0:ℝ)) 0:=uniqueDiffOn_Ici 0 0 self_mem_Ici
  exact (hleft'.derivWithin hud).symm.trans (hright.derivWithin hud)

theorem actual_forward_drift_commute (t:ℝ)(ht:0 ≤ t):
    Commute forwardGenerator (sourceForwardCore t ht) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  by_cases hz:z∈physicalChart
  · exact actual_forward_commute_point t ht f ⟨z,hz⟩ word
  · have hl:forwardGenerator (sourceForwardCore t ht f) z=0:=
      image_eq_zero_of_notMem_tsupport (fun h=>hz ((forwardGenerator (sourceForwardCore t ht f)).tsupport_subset h))
    have hr:sourceForwardCore t ht (forwardGenerator f) z=0:=
      image_eq_zero_of_notMem_tsupport (fun h=>hz ((sourceForwardCore t ht (forwardGenerator f)).tsupport_subset h))
    change (forwardGenerator (sourceForwardCore t ht f) z) word=(sourceForwardCore t ht (forwardGenerator f) z) word
    rw [hl,hr]

end LowEnergy.SourceClockPhiForwardDriftTransport
