import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineRateBlocks

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
noncomputable section
variable {nu : Viscosity}

private theorem unit_coupling_cancel {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) (x a y c : E)
    (green : inner ℝ x a+inner ℝ c y=0) :
    inner ℝ a (A x)+inner ℝ x (A a)+inner ℝ c (A y)+inner ℝ y (A c)=
      inner ℝ a ((A-ContinuousLinearMap.id ℝ E) x)+
      inner ℝ x ((A-ContinuousLinearMap.id ℝ E) a)+
      inner ℝ c ((A-ContinuousLinearMap.id ℝ E) y)+
      inner ℝ y ((A-ContinuousLinearMap.id ℝ E) c) := by
  have canceled : inner ℝ a x+inner ℝ x a+inner ℝ c y+inner ℝ y c=0 := by
    linarith only [green,real_inner_comm a x,real_inner_comm y c]
  simp only [sub_apply,ContinuousLinearMap.id_apply,inner_sub_right]
  linarith only [canceled]

def wordCoupling (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (word : List Coordinate) (time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) : ℝ :=
  let h:=NativeWindowHistorySpatialWords.history seed M word time
  let u:=NativeWindowHistoryAllOrderWord.value seed M word time
  let q:=NativeWindowHistoryMeanProjection.residual h
  let x:=NativeWindowHistoryMeanProjection.embed u
  let a:=NativeWindowHistoryMeanProjection.embed
    (NativeWindowHistoryMeanBlocks.annihilation seed M time h)
  let c:=NativeWindowHistoryMeanAction.creation seed M time u
  let B:=fullMetricAction seed time M F radius
  inner ℝ a (B x)+inner ℝ x (B a)+inner ℝ c (B q)+inner ℝ q (B c)

theorem wordCoupling_defect (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (word : List Coordinate) (time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) :
    let h:=NativeWindowHistorySpatialWords.history seed M word time
    let u:=NativeWindowHistoryAllOrderWord.value seed M word time
    let q:=NativeWindowHistoryMeanProjection.residual h
    let x:=NativeWindowHistoryMeanProjection.embed u
    let a:=NativeWindowHistoryMeanProjection.embed
      (NativeWindowHistoryMeanBlocks.annihilation seed M time h)
    let c:=NativeWindowHistoryMeanAction.creation seed M time u
    let B:=fullMetricAction seed time M F radius
    wordCoupling seed M word time F radius=
      inner ℝ a ((B-ContinuousLinearMap.id ℝ NativeWindowTraceWholeHistory.H) x)+
      inner ℝ x ((B-ContinuousLinearMap.id ℝ NativeWindowTraceWholeHistory.H) a)+
      inner ℝ c ((B-ContinuousLinearMap.id ℝ NativeWindowTraceWholeHistory.H) q)+
      inner ℝ q ((B-ContinuousLinearMap.id ℝ NativeWindowTraceWholeHistory.H) c) := by
  intro h u q x a c B
  have ann : NativeWindowHistoryMeanBlocks.annihilation seed M time h=
      NativeWindowHistoryMeanBlocks.annihilation seed M time q := by
    dsimp only [NativeWindowHistoryMeanBlocks.annihilation,
      ContinuousLinearMap.comp_apply,q]
    rw [NativeWindowHistoryBathResolvent.residual_square]
  have green:=NativeWindowHistoryMeanBlocks.coupling_green seed M time u q
  rw [←ann] at green
  have identity : inner ℝ x a+inner ℝ c q=0 := by
    dsimp only [x,a]
    rw [NativeWindowHistoryMeanProjection.embed_inner]
    exact green
  change inner ℝ a (B x)+inner ℝ x (B a)+inner ℝ c (B q)+inner ℝ q (B c)=_
  exact unit_coupling_cancel B x a q c identity

def twoLeg (B : NativeWindowTraceWholeHistory.H →L[ℝ]
    NativeWindowTraceWholeHistory.H) (x y : NativeWindowTraceWholeHistory.H) : ℝ :=
  inner ℝ y (B x)+inner ℝ x (B y)

private theorem twoLeg_add (B : NativeWindowTraceWholeHistory.H →L[ℝ]
    NativeWindowTraceWholeHistory.H)
    (x y z : NativeWindowTraceWholeHistory.H) :
    twoLeg B x (y+z)=twoLeg B x y+twoLeg B x z := by
  simp only [twoLeg,map_add,inner_add_left,inner_add_right]
  ring

theorem wordCoupling_twoLeg (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (word : List Coordinate) (time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) :
    let h:=NativeWindowHistorySpatialWords.history seed M word time
    let u:=NativeWindowHistoryAllOrderWord.value seed M word time
    let q:=NativeWindowHistoryMeanProjection.residual h
    let B:=fullMetricAction seed time M F radius
    wordCoupling seed M word time F radius=
      twoLeg B (NativeWindowHistoryMeanProjection.embed u)
        (NativeWindowHistoryMeanProjection.embed
          (NativeWindowHistoryMeanBlocks.annihilation seed M time h))+
      twoLeg B q (NativeWindowHistoryMeanAction.creation seed M time u) := by
  intro h u q B
  dsimp only [wordCoupling,twoLeg]
  ring

theorem centered_word_spatial_blocks (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (word : List Coordinate) (time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) :
    let h:=NativeWindowHistorySpatialWords.history seed M word time
    let r:=NativeWindowHistorySpatialWords.rate seed M word time
    let u:=NativeWindowHistoryAllOrderWord.value seed M word time
    let q:=NativeWindowHistoryMeanProjection.residual h
    let load:=NativeWindowHistoryAllOrderCausal.load seed M word time
    let B:=fullMetricAction seed time M F radius
    twoLeg B q (NativeWindowHistoryMeanProjection.residual r)=
      twoLeg B q (NativeWindowHistoryMeanBlocks.bath seed M time q)+
      twoLeg B q (NativeWindowHistoryMeanAction.creation seed M time u)+
      twoLeg B q (NativeWindowHistoryMeanProjection.residual load) := by
  intro h r u q load B
  have source : NativeWindowHistoryMeanProjection.residual r=
      NativeWindowHistoryMeanBlocks.bath seed M time q+
      NativeWindowHistoryMeanAction.creation seed M time u+
      NativeWindowHistoryMeanProjection.residual load :=
    centered_word_rate_original seed M word time
  have paired:=congrArg (twoLeg B q) source
  rw [twoLeg_add,twoLeg_add] at paired
  exact paired

theorem mean_word_spatial_blocks (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (word : List Coordinate) (time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) :
    let h:=NativeWindowHistorySpatialWords.history seed M word time
    let r:=NativeWindowHistorySpatialWords.rate seed M word time
    let u:=NativeWindowHistoryAllOrderWord.value seed M word time
    let load:=NativeWindowHistoryAllOrderCausal.load seed M word time
    let B:=fullMetricAction seed time M F radius
    twoLeg B (NativeWindowHistoryMeanProjection.projection h)
      (NativeWindowHistoryMeanProjection.projection r)=
      twoLeg B (NativeWindowHistoryMeanProjection.embed u)
        (NativeWindowHistoryMeanProjection.embed
          (NativeWindowHistoryMeanAction.meanOperator seed M time u))+
      twoLeg B (NativeWindowHistoryMeanProjection.embed u)
        (NativeWindowHistoryMeanProjection.embed
          (NativeWindowHistoryMeanBlocks.annihilation seed M time h))+
      twoLeg B (NativeWindowHistoryMeanProjection.embed u)
        (NativeWindowHistoryMeanProjection.embed
          (NativeWindowHistoryMeanProjection.mean load)) := by
  intro h r u load B
  have first : NativeWindowHistoryMeanProjection.projection h=
      NativeWindowHistoryMeanProjection.embed u :=
    congrArg NativeWindowHistoryMeanProjection.embed
      (NativeWindowHistoryAllOrderWord.value_original seed M word time).symm
  have rate:=mean_word_rate_original seed M word time
  have lifted := congrArg NativeWindowHistoryMeanProjection.embed rate
  simp only [map_add] at lifted
  have second : NativeWindowHistoryMeanProjection.projection r=
      NativeWindowHistoryMeanProjection.embed
        (NativeWindowHistoryMeanAction.meanOperator seed M time u)+
      NativeWindowHistoryMeanProjection.embed
        (NativeWindowHistoryMeanBlocks.annihilation seed M time h)+
      NativeWindowHistoryMeanProjection.embed
        (NativeWindowHistoryMeanProjection.mean load) := lifted
  have paired := congrArg₂ (twoLeg B) first second
  rw [twoLeg_add,twoLeg_add] at paired
  exact paired
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
