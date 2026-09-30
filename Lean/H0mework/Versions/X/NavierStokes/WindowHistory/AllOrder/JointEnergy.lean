import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.CausalEnergy
import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.CreationEnergy

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderJointEnergy
open Set Filter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (H gradient)
open NativeWindowHistorySpatialWords (history)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowHistoryAllOrderWord (value)
open NativeWindowHistoryAllOrderCausal (created remaining load)
open NativeWindowHistoryMeanBlocks (annihilation)
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}
local notation "Q" => NativeWindowHistoryMeanProjection.residual

private theorem centered_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (x y : E) (px : P (P x)=P x) (py : P y=y) : P (P x-y)=P x-y := by
  rw [map_sub,px,py]

theorem remaining_centered (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List ThreeDimensionalPeriodicCoarseFilterCore.Coordinate)
    (a B : ℝ) (aB : a ≤ B) (t : ℝ) (inside : t∈Icc a B) :
    Q (remaining seed M word a B aB t)=remaining seed M word a B aB t := by
  simpa only [] using! centered_sub (E := H) Q (NativeWindowHistorySpatialWords.history seed M word t)
    (created seed M word a B aB t) (NativeWindowHistoryBathResolvent.residual_square _)
    (NativeWindowHistoryCausalCreationEnergy.centered seed M (value seed M word)
      (NativeWindowHistoryAllOrderCausal.value_continuous seed M word) a B aB t inside)

open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)

def energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a ≤ B) (t : ℝ) : ℝ :=
  NativeWindowHistoryAllOrderCausalEnergy.energy seed M word a B aB t+‖remaining seed M word a B aB t‖^2

def mixedLoad (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a ≤ B) (t : ℝ) : ℝ :=
  2*inner ℝ (value seed M word t) (mean (load seed M word t))+
    2*inner ℝ (remaining seed M word a B aB t) (Q (load seed M word t))

set_option backward.isDefEq.respectTransparency false in
theorem source_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a ≤ B) (t : ℝ) (inside : t∈Icc a B) :
    HasDerivWithinAt (energy seed M word a B aB)
      (-2*nu.coeff*(NativeWindowHistoryAllOrderCausalEnergy.dissipation seed M word a B aB t+
        gradient M (remaining seed M word a B aB t))+
        2*inner ℝ (value seed M word t) (annihilation seed M t (remaining seed M word a B aB t))+
        mixedLoad seed M word a B aB t) (Icc a B) t := by
  have first:=NativeWindowHistoryAllOrderCausalEnergy.source_derivative seed M word a B aB t inside
  have last:=HasDerivWithinAt.norm_sq (F := H)
    (NativeWindowHistoryAllOrderCausal.remaining_derivative seed M word a B aB t inside)
  apply (first.add last).congr_deriv
  simp only [inner_add_right,NativeWindowHistoryBathResolvent.bath_energy,
    remaining_centered seed M word a B aB t inside]
  dsimp only [mixedLoad,NativeWindowHistoryAllOrderCausalEnergy.work,NativeWindowHistoryAllOrderCausal.remainder]
  rw [inner_add_right]
  ring

private theorem mixed_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →L[ℝ] E) (symmetric : ∀u v,inner ℝ (P u) v=inner ℝ u (P v))
    (x y f : E) (centered : P y=y) :
    inner ℝ x f+inner ℝ y (P f)=inner ℝ (x+y) f := by
  rw [← symmetric,centered,inner_add_left]

theorem mixedLoad_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a ≤ B) (t : ℝ) (inside : t∈Icc a B) :
    mixedLoad seed M word a B aB t=2*inner ℝ
      (NativeWindowHistorySpatialWords.history seed M word t-created seed M word a B aB t) (load seed M word t) := by
  have first:=NativeWindowHistoryMeanProjection.embed_pairing (value seed M word t) (load seed M word t)
  have pair:=mixed_pair (E := H) Q NativeWindowHistoryMeanProjection.residual_symmetric
    (embed (value seed M word t)) (remaining seed M word a B aB t) (load seed M word t)
    (remaining_centered seed M word a B aB t inside)
  have carrier : embed (value seed M word t)+remaining seed M word a B aB t=
      NativeWindowHistorySpatialWords.history seed M word t-created seed M word a B aB t := by
    rw [NativeWindowHistoryAllOrderWord.value_original]
    change NativeWindowHistoryMeanProjection.projection (NativeWindowHistorySpatialWords.history seed M word t)+
      (Q (NativeWindowHistorySpatialWords.history seed M word t)-created seed M word a B aB t)=_
    rw [← add_sub_assoc,NativeWindowHistoryMeanProjection.split]
  have split:=congrArg (fun q : ℝ => 2*q) (pair.trans (congrArg (fun z : H => inner ℝ z (load seed M word t)) carrier))
  dsimp only [mixedLoad]
  linarith only [first,split]

def dissipation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) (t : ℝ) : ℝ :=
  NativeWindowHistoryAllOrderCausalEnergy.dissipation seed M word a B aB t+
    gradient M (remaining seed M word a B aB t)

private theorem norm_sum_square {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) : ‖u+v‖^2≤2*‖u‖^2+2*‖v‖^2 := by
  rw [norm_add_sq_real]
  nlinarith only [real_inner_le_norm u v,sq_nonneg (‖u‖-‖v‖)]

theorem whole_mass (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) (t : ℝ) :
    ‖NativeWindowHistorySpatialWords.history seed M word t‖^2≤2*energy seed M word a B aB t := by
  let x:=NativeWindowHistorySpatialWords.history seed M word t
  have projected : NativeWindowHistoryMeanProjection.projection x=embed (value seed M word t) := by
    change embed (mean x)=_
    rw [← NativeWindowHistoryAllOrderWord.value_original]
  have residual : Q x=created seed M word a B aB t+remaining seed M word a B aB t := by
    dsimp only [remaining,x]
    abel
  have split:=NativeWindowHistoryMeanProjection.energy_split x
  rw [projected,NativeWindowHistoryMeanProjection.embed_norm,residual] at split
  have bounded:=norm_sum_square (E := H) (created seed M word a B aB t) (remaining seed M word a B aB t)
  dsimp only [energy,NativeWindowHistoryAllOrderCausalEnergy.energy]
  nlinarith only [split,bounded,sq_nonneg ‖value seed M word t‖]

private theorem gradient_neg (_seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (v : H) :
    gradient M (-v)=gradient M v := by
  rw [← NativeWindowMetricGraphHistory.history_gradient nu M,
    ← NativeWindowMetricGraphHistory.history_gradient nu M]
  simp only [map_neg]
  simpa only [] using! (inner_neg_neg (𝕜 := ℝ) (E := H) v
    (NativeWindowHistoryAnnihilationControl.laplacianAction nu M v))

theorem whole_word_cost (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) (t : ℝ) :
    gradient M (history seed M word t)≤
      gradient M (embed (value seed M word t))+
        2*gradient M (created seed M word a B aB t)+
        2*gradient M (remaining seed M word a B aB t) := by
  have split := NativeWindowHistoryMeanGradient.gradient_split seed M (history seed M word t)
  have projected : NativeWindowHistoryMeanProjection.projection (history seed M word t)=
      embed (value seed M word t) := by
    change embed (mean (history seed M word t))=_
    rw [← NativeWindowHistoryAllOrderWord.value_original]
  have same : Q (history seed M word t)=created seed M word a B aB t-(-remaining seed M word a B aB t) := by
    dsimp only [remaining]
    abel
  have pair := NativeWindowHistoryCausalDissipation.gradient_sub seed M
    (created seed M word a B aB t) (-remaining seed M word a B aB t)
  rw [gradient_neg seed M] at pair
  rw [← same] at pair
  rw [split,projected]
  linarith only [pair]

theorem whole_gradient (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) (t : ℝ) (inside : t∈Icc a B) :
    gradient M (NativeWindowHistorySpatialWords.history seed M word t)≤2*dissipation seed M word a B aB t := by
  have paid:=whole_word_cost seed M word a B aB t
  have centered:=NativeWindowHistoryCausalCreationEnergy.centered seed M (value seed M word)
    (NativeWindowHistoryAllOrderCausal.value_continuous seed M word) a B aB t inside
  change Q (created seed M word a B aB t)=created seed M word a B aB t at centered
  dsimp only [dissipation,NativeWindowHistoryAllOrderCausalEnergy.dissipation]
  rw [centered]
  linarith only [paid,NativeWindowHistoryMeanGradient.gradient_nonnegative seed M (embed (value seed M word t))]

theorem prepared_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (B : ℝ) (horizon : -2≤B) : energy seed M word (-2) B horizon (-2)=‖value seed M word (-2)‖^2 := by
  rw [energy,NativeWindowHistoryAllOrderCausalEnergy.energy_initial,
    NativeWindowHistoryAllOrderCausalEnergy.remaining_prepared,norm_zero,zero_pow (by decide),add_zero]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem source_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (a B : ℝ) (aB : a≤B) (a0 : 0≤a) (t : ℝ) (inside : t∈Icc a B) :
    (energy seed M word (step.2.clockAdvance+a) (step.2.clockAdvance+B) (add_le_add_right aB _) (step.2.clockAdvance+t),
     dissipation seed M word (step.2.clockAdvance+a) (step.2.clockAdvance+B) (add_le_add_right aB _) (step.2.clockAdvance+t),
     mixedLoad seed M word (step.2.clockAdvance+a) (step.2.clockAdvance+B) (add_le_add_right aB _) (step.2.clockAdvance+t))=
    (energy step.1 M word a B aB t,dissipation step.1 M word a B aB t,mixedLoad step.1 M word a B aB t) := by
  have old:=NativeWindowHistoryAllOrderCausalEnergy.source_next seed M word step generated a B aB a0 t inside
  have e:=congrArg Prod.fst old
  have d:=congrArg (fun triple => triple.2.1) old
  dsimp only at e d
  simp only [energy,dissipation,mixedLoad,e,d,
    NativeWindowHistoryAllOrderCausal.remaining_next seed M word step generated a B aB a0 t inside,
    NativeWindowHistoryAllOrderWord.value_next seed M word step generated t (a0.trans inside.1),
    NativeWindowHistoryAllOrderCausal.load_next seed M word step generated t (a0.trans inside.1)]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderJointEnergy
