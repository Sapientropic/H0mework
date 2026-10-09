import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorRadiusPrice
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeFixedEnergyTail
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeScalarInverseEnergyBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ActualTwoResolventCascade
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory SourceQuantumScalarChart
open SourceMixedNativeReturn SourceScalarInverseNativeEnergy SourceScalarInverseEnergyBudget
open SourceInverseFixedEnergyTail SourceHardyRetardedTail SourceRelativePowerTail
open SourceCutoffDilationWard SourceRetardedGraph
open scoped InnerProductSpace Matrix
private abbrev n : ℝ := sourceTime 0
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev theta := SourceNativeCutoffContact.thetaAction

private theorem n_pos : 0 < n := by
  change 0 < sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem mu_pos : 0 < sourceMu := lt_of_lt_of_le (by norm_num) source_mu_large
private theorem coefficient_nonnegative (sharp:Bool) : 0 ≤ coefficientCost sharp :=
  Finset.sum_nonneg (fun _ _=>sq_nonneg _)

/-- The coefficients are the original full-Y primitive price, scaled by the
actual damping. The final norm term supplies a strict nonnegative reserve. -/
def bulkCoefficient (sharp:Bool) : ℝ := coefficientCost sharp/(8*n*sourceMu^2)
def normCoefficient (sharp:Bool) : ℝ :=
  (2*‖constantBounded sharp vacuum‖^2+coefficientCost sharp*‖vacuum‖^2)/(4*sourceMu^2)+1

def sourceQ (sharp:Bool) (m ell:ℕ) (f:QuantumTest) : ℝ :=
  bulkCoefficient sharp*inverseForm (theta m ell f)+
    normCoefficient sharp*‖embed (theta m ell f)‖^2

def sourceL (sharp:Bool) (m ell:ℕ) : End :=
  (((1/(2*sourceMu):ℝ):ℂ)) • literalIncrementAction sharp m ell

def initialStorage (sharp:Bool) (m ell:ℕ) (f:QuantumTest) : ℝ :=
  ‖embed (sourceL sharp m ell f)‖^2+sourceQ sharp m ell f

private theorem bulk_nonnegative (sharp:Bool) : 0 ≤ bulkCoefficient sharp := by
  unfold bulkCoefficient
  exact div_nonneg (coefficient_nonnegative sharp) (by have hn:=n_pos; positivity)
private theorem norm_nonnegative (sharp:Bool) : 0 ≤ normCoefficient sharp := by
  unfold normCoefficient
  have hc:=coefficient_nonnegative sharp
  positivity

theorem actual_increment_core (sharp:Bool) (m ell:ℕ) (f:QuantumTest) :
    literalIncrementAction sharp m ell f=fullAction sharp (theta m ell f) := by
  rw [literal_full_return]
  change fullAction sharp (SourceMixedNativeReturn.thetaAction m ell f)=_
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]

theorem actual_sourceL_norm (sharp:Bool) (m ell:ℕ) (f:QuantumTest) :
    ‖embed (sourceL sharp m ell f)‖^2=
      ‖embed (fullAction sharp (theta m ell f))‖^2/(4*sourceMu^2) := by
  unfold sourceL
  rw [LinearMap.smul_apply,map_smul,norm_smul,actual_increment_core]
  simp only [Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  field_simp
  ring

/-- This source-owned Q dominates the squared actual off-diagonal storage.
No positivity certificate or finite-dimensional table is supplied. -/
theorem actual_primitive_storage_price (sharp:Bool) (m ell:ℕ) (f:QuantumTest) :
    ‖embed (sourceL sharp m ell f)‖^2+‖embed (theta m ell f)‖^2 ≤ sourceQ sharp m ell f := by
  have hy:=original_full_inverse sharp (theta m ell f)
  rw [actual_sourceL_norm]
  unfold fullPrice at hy
  unfold sourceQ bulkCoefficient normCoefficient
  have hn:=n_pos
  have hm:=mu_pos
  have hs : (2*n)*‖embed (fullAction sharp (theta m ell f))‖^2 ≤
      coefficientCost sharp*inverseForm (theta m ell f)+
        (4*n*‖constantBounded sharp vacuum‖^2+2*n*coefficientCost sharp*‖vacuum‖^2)*
          ‖embed (theta m ell f)‖^2 := by
    convert mul_le_mul_of_nonneg_left hy (show 0 ≤ 2*n by positivity) using 1 <;>
      first | rfl | (field_simp [n_pos.ne']; ring)
  apply (mul_le_mul_iff_right₀ (show 0 < 8*n*sourceMu^2 by positivity)).mp
  field_simp
  nlinarith only [hs]

theorem actual_sourceQ_nonnegative (sharp:Bool) (m ell:ℕ) (f:QuantumTest) :
    0 ≤ sourceQ sharp m ell f :=
  (add_nonneg (sq_nonneg _) (sq_nonneg _)).trans (actual_primitive_storage_price sharp m ell f)

/-- The input storage is paid by the original fixed theta energy and norm tails.
This is the true initial (0,g) price for the cascade, before any positivity test. -/
theorem actual_initial_storage_tail (sharp:Bool) (f:QuantumTest) :
    ∀ ε:ℝ, 0 < ε → ∃ N:ℕ, ∀ m, N  ≤  m → ∀ ell, m  ≤  ell →
      initialStorage sharp m ell f ≤ ε := by
  intro ε hε
  let a:=bulkCoefficient sharp
  let b:=normCoefficient sharp
  have ha:0 ≤ a:=bulk_nonnegative sharp
  have hb:0 ≤ b:=norm_nonnegative sharp
  let δ:=ε/(2*(a+b+1))
  have hd:0 < δ:=by dsimp only [δ]; positivity
  obtain ⟨N1,h1⟩:=original_fixed_energy_tail f δ hd
  obtain ⟨N2,h2⟩:=original_relative_tail (embed f) (Real.sqrt δ) (Real.sqrt_pos.mpr hd)
  refine ⟨max N1 N2,fun m hm ell hml=>?_⟩
  have hi:inverseForm (theta m ell f) ≤ δ:=h1 m (by omega) ell hml
  have ht:=h2 m (by omega) ell hml
  have he:=SourceNativeCutoffContact.theta_core m ell f
  rw [←he] at ht
  have hn:‖embed (theta m ell f)‖^2 ≤ δ:=by
    have hs:=Real.sq_sqrt hd.le
    nlinarith [norm_nonneg (embed (theta m ell f)),Real.sqrt_nonneg δ]
  have hq:sourceQ sharp m ell f ≤ (a+b)*δ := by
    exact (add_le_add (mul_le_mul_of_nonneg_left hi ha)
      (mul_le_mul_of_nonneg_left hn hb)).trans_eq (by ring)
  have hs:=actual_primitive_storage_price sharp m ell f
  have hstorage:initialStorage sharp m ell f ≤ 2*sourceQ sharp m ell f := by
    unfold initialStorage
    nlinarith only [hs,sq_nonneg ‖embed (theta m ell f)‖]
  apply hstorage.trans
  apply (mul_le_mul_of_nonneg_left hq (by norm_num: (0:ℝ) ≤ 2)).trans
  dsimp only [δ]
  rw [←mul_div_assoc,←mul_div_assoc]
  apply (div_le_iff₀ (by positivity:0 < 2*(a+b+1))).mpr
  nlinarith only [hε]

end LowEnergy.ActualTwoResolventCascade
