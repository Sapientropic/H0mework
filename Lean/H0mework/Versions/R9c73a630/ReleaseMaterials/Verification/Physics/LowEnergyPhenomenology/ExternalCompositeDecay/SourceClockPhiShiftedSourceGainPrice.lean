import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalNormalizerRadialDebit
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCompleteHeatGainPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.OriginalRMatchedCofinal
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourcePhysicalKineticSquare
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource SourceClockPhiNormalizedScalarBudget
open SourceClockPhiMatchedDiffusionSource SourceClockPhiWholeSignedWorkIntegrable
open SourceClockPhiActualCovarianceStep ClockPhiConservativeHeatSource SourceClockPhiCompleteHeatGainPayment
open SourceLocalizedInverseFormPayment SourceResolventBandLimit FirstCurrentJointBudget FirstCurrentElectricSuccessor
open FirstCurrentGeometricPayer ClockPhiHeatCorrectedCovarianceSource
open FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier FirstCurrentPayerNext MeasureTheory Filter
open scoped Topology InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev X:End:=weightedElectricCurrent
private abbrev U:End:=inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev G(s:ℝ):End:=sourceGain (Real.sqrt s)
attribute [local irreducible] sourcePair embed diagonalAction matchedTester correctedCompleteCore combinedGenerator
  normalizedState normalizedForcing sourceGain driftClock inverseVolumeAction weightedElectricCurrent sourceTime wholeSourceMap wholeStep wholeGraphPrice wholeNormPrice wholeSlope wholeCurvature wholeFraction frequencyState
private theorem n_pos:0 < sourceTime 0:=by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem mu_pos(half:Bool):0 < sourceNoetherFrequency half:=by
  linarith [n_pos,actual_source_noether_gap half]

def shiftedSourceSquare(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):ℝ:=
  ∫q:ℝ,‖embed (actualFrequency advanced (sourceNoetherFrequency half) q •
    L (frequencyState half advanced m ell F g q))‖^2

def shiftedSourceGraph(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):ℝ:=
  ∫q:ℝ,comparisonEnergy (actualFrequency advanced (sourceNoetherFrequency half) q •
    L (frequencyState half advanced m ell F g q))
private theorem square_nonneg(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    0 ≤ shiftedSourceSquare half advanced m ell F g L:=integral_nonneg (fun _=>sq_nonneg _)
private theorem energy_nonneg(w:QuantumTest):0 ≤ comparisonEnergy w:=by unfold comparisonEnergy;positivity
private theorem graph_nonneg(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    0 ≤ shiftedSourceGraph half advanced m ell F g L:=integral_nonneg (fun _=>energy_nonneg _)
private theorem shifted_graph_integrable(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>comparisonEnergy (actualFrequency advanced (sourceNoetherFrequency half) q •
      L (frequencyState half advanced m ell F g q))):=by
  have h1:=actual_whole_carrier_shifted_square half advanced m ell F g (driftClock*L)
  have h2:=actual_whole_carrier_shifted_square half advanced m ell F g (U*D*L)
  simpa only [comparisonEnergy,map_smul,Module.End.mul_apply,Pi.add_apply] using! h1.add (h2.const_mul (1/2:ℝ))

private theorem gain_energy(s:ℝ)(hs:0 < s)(f:QuantumTest):
    ‖embed (G s f)‖^2 ≤ ‖embed f‖^2+s*(comparisonEnergy f+‖embed f‖^2):=by
  have h:=actual_complete_heat_gain_payment s hs s hs 0 f
  change ‖embed (sourceHeatCore s hs 0 (G s f))‖^2 ≤ _ at h
  rw [sourceHeat_norm] at h
  have he:s^2/s=s:=by field_simp [hs.ne']
  rw [he] at h
  linarith only [h]
private theorem two_square(x y:H):‖x+y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2:=by
  have h:=pow_le_pow_left₀ (norm_nonneg (x+y)) (norm_add_le x y) 2
  nlinarith [sq_nonneg (‖x‖-‖y‖)]
private theorem two_real_square(x y:H)(h:ℝ):‖x+(h:ℂ) • y‖^2 ≤ 2*‖x‖^2+2*h^2*‖y‖^2:=by
  have hp:=two_square x ((h:ℂ) • y)
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs] at hp
  nlinarith only [hp]
private theorem source_map_square(s:ℝ)(hs:0 < s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(B:End)(q:ℝ):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let w:=frequencyState half advanced m ell F g q
    let h:=wholeStep s hs half advanced m ell F g
    ‖embed (z • B (wholeSourceMap s hs half advanced m ell F g w))‖^2 ≤
      2*‖embed (z • B w)‖^2+2*h^2*‖embed (z • B (X w))‖^2:=by
  dsimp only
  simp only [wholeSourceMap,LinearMap.add_apply,Module.End.one_apply,LinearMap.smul_apply,
    map_add,map_smul,smul_add]
  rw [smul_comm (actualFrequency advanced (sourceNoetherFrequency half) q)
    (wholeStep s hs half advanced m ell F g:ℂ)]
  exact two_real_square _ _ _
private theorem shifted_square_map_price(s:ℝ)(hs:0 < s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(B:End):
    shiftedSourceSquare half advanced m ell F g (B*wholeSourceMap s hs half advanced m ell F g) ≤
      2*shiftedSourceSquare half advanced m ell F g B+
      2*(wholeStep s hs half advanced m ell F g)^2*shiftedSourceSquare half advanced m ell F g (B*X):=by
  have hL:=actual_whole_carrier_shifted_square half advanced m ell F g (B*wholeSourceMap s hs half advanced m ell F g)
  have h1:=actual_whole_carrier_shifted_square half advanced m ell F g B
  have h2:=actual_whole_carrier_shifted_square half advanced m ell F g (B*X)
  have h:=integral_mono hL ((h1.const_mul 2).add (h2.const_mul (2*(wholeStep s hs half advanced m ell F g)^2)))
    (source_map_square s hs half advanced m ell F g B)
  erw [integral_add (h1.const_mul 2) (h2.const_mul _)] at h
  simpa only [integral_const_mul,shiftedSourceSquare] using h
private theorem shifted_graph_square(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    shiftedSourceGraph half advanced m ell F g L=
      shiftedSourceSquare half advanced m ell F g (driftClock*L)+
      (1/2:ℝ)*shiftedSourceSquare half advanced m ell F g (U*D*L):=by
  unfold shiftedSourceGraph comparisonEnergy
  simp only [map_smul]
  have h1:=actual_whole_carrier_shifted_square half advanced m ell F g (driftClock*L)
  have h2:=actual_whole_carrier_shifted_square half advanced m ell F g (U*D*L)
  simpa only [shiftedSourceSquare,Module.End.mul_apply,map_smul,Pi.add_apply,integral_const_mul] using! integral_add h1 (h2.const_mul (1/2:ℝ))
private theorem shifted_graph_map_price(s:ℝ)(hs:0 < s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    shiftedSourceGraph half advanced m ell F g (wholeSourceMap s hs half advanced m ell F g) ≤
      2*shiftedSourceGraph half advanced m ell F g 1+
      2*(wholeStep s hs half advanced m ell F g)^2*shiftedSourceGraph half advanced m ell F g X:=by
  simp only [shifted_graph_square,mul_one]
  have h1:=shifted_square_map_price s hs half advanced m ell F g driftClock
  have h2:=shifted_square_map_price s hs half advanced m ell F g (U*D)
  linarith only [h1,h2]

private theorem cap_small(A C W P:ℝ)(hW:0 ≤ W)(hP:0 ≤ P):
    |(-A/(2*(|C|+1)))*(W/((|A|+1)*(W+P+|A|+|C|+1)))| ≤ 1/2:=by
  have hD:0 < (|A|+1)*(W+P+|A|+|C|+1):=by positivity
  have hE:0 < 2*(|C|+1):=by positivity
  have hp:W ≤ W+P+|A|+|C|+1:=by linarith [abs_nonneg A,abs_nonneg C]
  have hq:W/((|A|+1)*(W+P+|A|+|C|+1)) ≤ 1/(|A|+1):=by
    apply (div_le_div_iff₀ hD (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hp (by positivity:0 ≤ |A|+1)]
  rw [abs_mul,abs_div,abs_neg,abs_of_pos hE,abs_div,abs_of_nonneg hW,abs_of_pos hD]
  calc
    _ ≤ (|A|/(2*(|C|+1)))*(1/(|A|+1)):=mul_le_mul_of_nonneg_left hq (by positivity)
    _ ≤ 1/2:=by
      field_simp [ne_of_gt (show 0 < |A|+1 by positivity),ne_of_gt (show 0 < |C|+1 by positivity)]
      nlinarith [mul_nonneg (abs_nonneg A) (abs_nonneg C),abs_nonneg C]
private theorem step_small(s:ℝ)(hs:0 < s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    (wholeStep s hs half advanced m ell F g)^2 ≤ 1/4:=by
  have hW:0 ≤ wholeNormPrice half advanced m ell F g:=by
    unfold wholeNormPrice
    exact integral_nonneg (fun _=>sq_nonneg _)
  have hP:0 ≤ wholeGraphPrice half advanced m ell F g:=by
    unfold wholeGraphPrice
    exact integral_nonneg (fun q=>by
    unfold wholeGraphDensity
    have h:=energy_nonneg (X (frequencyState half advanced m ell F g q))
    positivity)
  have h:=cap_small (wholeSlope s hs half advanced m ell F g) (wholeCurvature s hs half advanced m ell F g)
    (wholeNormPrice half advanced m ell F g) (wholeGraphPrice half advanced m ell F g) hW hP
  have hh:|wholeStep s hs half advanced m ell F g| ≤ 1/2:=by
    simpa only [wholeStep,wholeFraction] using h
  calc
    _=|wholeStep s hs half advanced m ell F g|^2:=(sq_abs _).symm
    _ ≤ (1/2:ℝ)^2:=pow_le_pow_left₀ (abs_nonneg _) hh 2
    _=1/4:=by norm_num

def shiftedGainRemainder(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):ℝ:=
  2*(shiftedSourceGraph half advanced m ell F g 1+shiftedSourceGraph half advanced m ell F g X+
    shiftedSourceSquare half advanced m ell F g 1+shiftedSourceSquare half advanced m ell F g X)

/-- Its finite coefficient is generated entirely from the original shifted source and its actual electric direction, before the clock is selected. -/
theorem actual_shifted_gain_remainder_nonnegative(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    0 ≤ shiftedGainRemainder half advanced m ell F g:=by
  unfold shiftedGainRemainder
  exact mul_nonneg (by norm_num) (add_nonneg (add_nonneg (add_nonneg
    (graph_nonneg half advanced m ell F g 1) (graph_nonneg half advanced m ell F g X))
    (square_nonneg half advanced m ell F g 1)) (square_nonneg half advanced m ell F g X))

attribute [local irreducible] shiftedSourceSquare shiftedSourceGraph shiftedGainRemainder

/-- The clock-dependent source map has a clock-independent finite gain error, while its zeroth shifted price is paid by the actual source-generated electric graph step. -/
theorem actual_whole_shifted_gain_price(s:ℝ)(hs:0 < s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    let L:=wholeSourceMap s hs half advanced m ell F g
    Integrable (fun q:ℝ=>‖embed (G s (actualFrequency advanced (sourceNoetherFrequency half) q •
      L (frequencyState half advanced m ell F g q)))‖^2) ∧
    (∫q:ℝ,‖embed (G s (actualFrequency advanced (sourceNoetherFrequency half) q •
      L (frequencyState half advanced m ell F g q)))‖^2) ≤
      2*shiftedSourceSquare half advanced m ell F g 1+wholeNormPrice half advanced m ell F g/2+
        s*shiftedGainRemainder half advanced m ell F g:=by
  dsimp only
  let L:=wholeSourceMap s hs half advanced m ell F g
  let h:=wholeStep s hs half advanced m ell F g
  have hG:Integrable (fun q:ℝ=>‖embed (G s (actualFrequency advanced (sourceNoetherFrequency half) q •
      L (frequencyState half advanced m ell F g q)))‖^2):=by
    simpa only [Module.End.mul_apply,map_smul] using! actual_whole_carrier_shifted_square half advanced m ell F g (G s*L)
  refine ⟨hG,?_⟩
  have hS:=actual_whole_carrier_shifted_square half advanced m ell F g L
  have hE:=shifted_graph_integrable half advanced m ell F g L
  have hg:=integral_mono hG (hS.add ((hE.add hS).const_mul s)) (fun q=>gain_energy s hs _)
  erw [integral_add hS ((hE.add hS).const_mul s),integral_const_mul,integral_add hE hS] at hg
  have hgg:(∫q:ℝ,‖embed (G s (actualFrequency advanced (sourceNoetherFrequency half) q •
      L (frequencyState half advanced m ell F g q)))‖^2) ≤
      shiftedSourceSquare half advanced m ell F g L+s*(shiftedSourceGraph half advanced m ell F g L+
        shiftedSourceSquare half advanced m ell F g L):=by
    unfold shiftedSourceSquare shiftedSourceGraph
    exact hg
  have hN:=shifted_square_map_price s hs half advanced m ell F g 1
  simp only [one_mul] at hN
  have hNE:=shifted_graph_map_price s hs half advanced m ell F g
  have hh:=step_small s hs half advanced m ell F g
  have hR:=square_nonneg half advanced m ell F g X
  have hRE:=graph_nonneg half advanced m ell F g X
  have h1:=square_nonneg half advanced m ell F g 1
  have hE1:=graph_nonneg half advanced m ell F g 1
  have hcap:shiftedSourceGraph half advanced m ell F g L+shiftedSourceSquare half advanced m ell F g L ≤
      shiftedGainRemainder half advanced m ell F g:=by
    unfold shiftedGainRemainder
    change _ ≤ _ at hN hNE
    dsimp only [L]
    nlinarith [mul_le_mul_of_nonneg_right hh hR,mul_le_mul_of_nonneg_right hh hRE]
  have hGX:shiftedSourceSquare half advanced m ell F g X ≤ wholeGraphPrice half advanced m ell F g:=by
    have hi:=integral_mono (actual_whole_carrier_shifted_square half advanced m ell F g X)
      (actual_whole_electric_graph_payment s hs half advanced m ell F g).1 (fun q=>by
        unfold wholeGraphDensity
        have he:=energy_nonneg (X (frequencyState half advanced m ell F g q))
        linarith [sq_nonneg (‖embed (X (frequencyState half advanced m ell F g q))‖)])
    unfold shiftedSourceSquare wholeGraphPrice
    exact hi
  have hpaid:shiftedSourceSquare half advanced m ell F g L ≤
      2*shiftedSourceSquare half advanced m ell F g 1+wholeNormPrice half advanced m ell F g/2:=by
    have hp:=(actual_whole_electric_graph_payment s hs half advanced m ell F g).2
    have hm:=mul_le_mul_of_nonneg_left hGX (sq_nonneg h)
    change h^2*wholeGraphPrice half advanced m ell F g ≤ _ at hp
    change _ ≤ 2*shiftedSourceSquare half advanced m ell F g 1+2*h^2*shiftedSourceSquare half advanced m ell F g X at hN
    linarith only [hN,hp,hm]
  linarith only [hgg,hpaid,mul_le_mul_of_nonneg_left hcap hs.le]
end LowEnergy.OriginalRMatchedCofinal
