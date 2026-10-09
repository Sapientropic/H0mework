import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceMatterForceAbsorption
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceShiftedBulkTimeBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceMatterForceTimeBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory GaussNativeEnergy
open SourceBulkTwoTime SourceBulkParseval SourceInverseNoetherChannelGap SourceInverseNoetherEnergy
open SourceScalarPositiveBulkWard SourceFourPoleEnergyClosed SourceShiftedBulkTimeBudget SourceMatterForceAbsorption
open SourceScalarInverseRetardedBudget SourceScalarSignedInverseReturn SourceInverseNeutralRemainderClosed
open SourceScalarBalancedForce SourceElectricCompletedSquare SourceElectricColumns SourcePhysicalKineticSquare GaussNativeForm
open SourceJointResidualEnergy
open SourceScalarPairedTransport SourceMovingJetFlux SourceEscapeCurrent SourceScalarInverseNativeEnergy
open FullYSourceResolventGraphSplice SourceResolventBandLimit
open Filter MeasureTheory
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair bulkAction coreTime closedJointCost

private def coefficient (F : Index) (g : diagonal.domain) (A B : End) (i j : Channel F) : ℂ :=
  sourcePair (A (channelTest F g i)) (B (channelTest F g j))
private def timeSum (F : Index) (μ : ℝ) (c : Channel F → Channel F → ℂ) (t : ℝ) : ℂ :=
  ∑ i,∑ j,Complex.exp (-gap μ (channelValue F i) (channelValue F j)*(t : ℂ))*c i j
private theorem time_factor (μ a b t : ℝ) :
    Complex.exp (-gap μ a b*(t : ℂ))=(Real.exp (-2*μ*t) : ℂ)*star (phase a t)*phase b t := by
  simp only [gap,phase,Complex.star_def,←Complex.exp_conj,Complex.ofReal_exp]
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal]
  push_cast
  ring

private theorem pair_sum (F : Index) (g : diagonal.domain) (A B : End) (c : Channel F → ℂ) :
    sourcePair (A (∑ i,c i • channelTest F g i)) (B (∑ j,c j • channelTest F g j))=
      ∑ i,∑ j,star (c i)*c j*coefficient F g A B i j := by
  simp only [coefficient,sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,
    inner_smul_right,starRingEnd_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem pair_time (F : Index) (μ : ℝ) (g : diagonal.domain) (A B : End) (t : ℝ) :
    timeSum F μ (coefficient F g A B) t=(Real.exp (-2*μ*t) : ℂ)*
      sourcePair (A (coreTime F g t)) (B (coreTime F g t)) := by
  unfold timeSum
  simp_rw [time_factor]
  rw [coreTime,pair_sum]
  simp only [Finset.mul_sum,phase]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem decay_integrable (μ a b : ℝ) (hμ : 0 < μ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-gap μ a b*(t : ℂ))) (Set.Ioi 0) := by
  apply integrableOn_exp_mul_complex_Ioi
  simp [gap]
  linarith

private theorem sum_integrable (F : Index) (μ : ℝ) (hμ : 0 < μ) (c : Channel F → Channel F → ℂ) :
    IntegrableOn (timeSum F μ c) (Set.Ioi 0) :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (decay_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _))

private theorem pair_integrable (F : Index) (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) (A B : End) :
    IntegrableOn (fun t : ℝ => (Real.exp (-2*μ*t) : ℂ)*
      sourcePair (A (coreTime F g t)) (B (coreTime F g t))) (Set.Ioi 0) :=
  (sum_integrable F μ hμ (coefficient F g A B)).congr (Eventually.of_forall (pair_time F μ g A B))

private theorem pair_im_integrable (F : Index) (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) (A B : End) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*
      (sourcePair (A (coreTime F g t)) (B (coreTime F g t))).im) (Set.Ioi 0) := by
  have h := (pair_integrable F μ hμ g A B).im
  change IntegrableOn (fun t : ℝ => ((Real.exp (-2*μ*t) : ℂ)*sourcePair (A (coreTime F g t)) (B (coreTime F g t))).im) (Set.Ioi 0) at h
  simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using h


private theorem pair_re_integrable (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (A B : End) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*
      (sourcePair (A (coreTime F g t)) (B (coreTime F g t))).re) (Set.Ioi 0) := by
  have h := (pair_integrable F μ hμ g A B).re
  change IntegrableOn (fun t : ℝ => ((Real.exp (-2*μ*t) : ℂ)*sourcePair (A (coreTime F g t)) (B (coreTime F g t))).re) (Set.Ioi 0) at h
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using h

/-- All full defects and other physical currents remain, with the one paid matter current removed. -/
def otherRaised (F : Index) (T : End) (q : QuantumTest) : ℝ :=
  remainingRaised F T q+(sourcePair (T q) (matterBulkCurrent (T q))).im/2

def otherTime (F : Index) (μ : ℝ) (T : End) (g : diagonal.domain) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*otherRaised F T (coreTime F g t)

def contactTime (F : Index) (μ : ℝ) (T : End) (g : diagonal.domain) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*contactEnergy (T (coreTime F g t))

private theorem contact_integrable (F : Index) (μ : ℝ) (hμ : 0<μ) (T : End) (g : diagonal.domain) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*contactEnergy (T (coreTime F g t))) (Set.Ioi 0) := by
  have h (a : LieIndex) (i j : Fin 3) := pair_re_integrable F μ hμ g
    (matterContact (gaugeDirection i a)*inverseRootAction*T)
    (metricColumn i j*matterContact (gaugeDirection j a)*inverseRootAction*T)
  have hs := integrable_finsetSum Finset.univ (fun a _ =>
    integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => h a i j)))
  simpa only [contactEnergy,gaugePair,Complex.re_sum,Finset.mul_sum,Module.End.mul_apply] using! hs

/-- The complete first-order matter force is paid in time by one lapse of the original bulk and its actual zeroth-order contact moment. -/
theorem actual_matter_time_absorption (F : Index) (μ : ℝ) (hμ : 0<μ) (T : End) (g : diagonal.domain) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*contactEnergy (T (coreTime F g t))) (Set.Ioi 0) ∧
    remainingTimeComplete F μ T g ≤ otherTime F μ T g+
      sourceTime 0*timeEnergy F μ T g+(9/(2*sourceTime 0))*contactTime F μ T g := by
  have hr := (actual_shifted_time_absorption F μ hμ T g).1
  have hm := (pair_im_integrable F μ hμ g T (matterBulkCurrent*T)).div_const 2
  have ho : IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*otherRaised F T (coreTime F g t)) (Set.Ioi 0) := by
    have h := hr.add hm
    simpa only [otherRaised,Module.End.mul_apply,Pi.add_apply,mul_add,mul_div_assoc] using! h
  have he := (actual_bulk_parseval F μ hμ T g).2.1
  have hc := contact_integrable F μ hμ T g
  refine ⟨hc,?_⟩
  have hup := (ho.add (he.const_mul (sourceTime 0))).add (hc.const_mul (9/(2*sourceTime 0)))
  have hle := integral_mono hr hup (fun t => by
    have h := original_matter_force_absorption (T (coreTime F g t))
    have hl := neg_abs_le ((sourcePair (T (coreTime F g t)) (matterBulkCurrent (T (coreTime F g t)))).im/2)
    have hi : remainingRaised F T (coreTime F g t) ≤ otherRaised F T (coreTime F g t)+
        sourceTime 0*inverseForm (T (coreTime F g t))+(9/(2*sourceTime 0))*contactEnergy (T (coreTime F g t)) := by
      dsimp only [otherRaised]
      linarith
    have hf := mul_le_mul_of_nonneg_left hi (Real.exp_pos (-2*μ*t)).le
    dsimp only [Pi.add_apply]
    nlinarith only [hf])
  have h1 := integral_add ho (he.const_mul (sourceTime 0))
  have h2 := integral_add (ho.add (he.const_mul (sourceTime 0))) (hc.const_mul (9/(2*sourceTime 0)))
  simp only [Pi.add_apply] at hle h1 h2
  rw [h2,h1,integral_const_mul,integral_const_mul] at hle
  exact hle

/-- Only geometry, full compression defect and the explicit contact moment remain after source scalar and matter absorption. -/
theorem actual_matter_time_energy_budget (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (μ-3*sourceTime 0)*timeEnergy F μ (theta m ell) g ≤ ε+
          otherTime F μ (theta m ell) g+(9/(2*sourceTime 0))*contactTime F μ (theta m ell) g := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_shifted_time_energy_budget μ hμ g ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  have h := (actual_matter_time_absorption F μ hμ (theta m ell) g).2
  nlinarith only [hF,h]

open SourceBulkTimeEnergyBudget

/-- The original complete cost consumes the paid matter force with the source gap mu minus 3n. -/
theorem actual_original_matter_time_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (hgap : 3*sourceTime 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        closedJointCost sharp m ell F μ (g : H) (k : H) ≤ ε+
          (4*Real.pi*formPrice sharp*μ⁻¹^2*‖(k : H)‖^2/(μ-3*sourceTime 0))*
            (otherTime F μ (theta m ell) g+(9/(2*sourceTime 0))*contactTime F μ (theta m ell) g) := by
  intro ε hε
  let P : ℝ := 4*Real.pi*formPrice sharp*μ⁻¹^2*‖(k : H)‖^2
  let v : ℝ := μ-3*sourceTime 0
  have hv : 0<v := sub_pos.mpr hgap
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hp : 0 ≤ P := by
    have hc : 0 ≤ coefficientCost sharp := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    dsimp only [P,formPrice]
    positivity
  let δ := v*(ε/2)/(P+1)
  have hδ : 0<δ := div_pos (mul_pos hv (by positivity)) (by positivity)
  obtain ⟨NC,hC⟩ := actual_original_time_energy_budget sharp μ hμ g k (ε/2) (by positivity)
  obtain ⟨NE,hE⟩ := actual_matter_time_energy_budget μ hμ g δ hδ
  refine ⟨max NC NE,fun m hm ell hell => ?_⟩
  filter_upwards [hC m ((le_max_left _ _).trans hm) ell hell,
    hE m ((le_max_right _ _).trans hm) ell hell] with F hFC hFE
  have hc := mul_le_mul_of_nonneg_left hFC hv.le
  have hFEa := hFE
  simp only [add_assoc] at hFEa
  have he := mul_le_mul_of_nonneg_left hFEa hp
  have hd : P*δ ≤ v*(ε/2) := by
    dsimp [δ]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<P+1)).mpr
    nlinarith only [mul_nonneg hv.le (le_of_lt hε)]
  change v*closedJointCost sharp m ell F μ (g : H) (k : H) ≤ v*(ε/2+P*timeEnergy F μ (theta m ell) g) at hc
  change P*(v*timeEnergy F μ (theta m ell) g) ≤ P*(δ+(otherTime F μ (theta m ell) g+(9/(2*sourceTime 0))*contactTime F μ (theta m ell) g)) at he
  have hfinal : closedJointCost sharp m ell F μ (g : H) (k : H)*v ≤
      v*ε+P*(otherTime F μ (theta m ell) g+(9/(2*sourceTime 0))*contactTime F μ (theta m ell) g) := by nlinarith only [hc,he,hd]
  have hb := (le_div_iff₀ hv).mpr hfinal
  calc
    _ ≤ (v*ε+P*(otherTime F μ (theta m ell) g+(9/(2*sourceTime 0))*contactTime F μ (theta m ell) g))/v := hb
    _ = _ := by change _=ε+(P/v)*_;field_simp

end LowEnergy.SourceMatterForceTimeBudget
