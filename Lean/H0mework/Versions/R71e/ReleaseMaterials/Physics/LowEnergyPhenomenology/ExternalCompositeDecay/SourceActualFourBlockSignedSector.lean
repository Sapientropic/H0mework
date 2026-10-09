import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorSignedSectorRetarded
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ActualFourBlockSignedSector
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open QuantizationCheck.Fermion ActiveMatterSectorCharge MixedSpectatorCandidate
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussDensityCore
open ActualFourBlockSource ActualFourBlockRetarded ActualSignedSector MixedSpectatorSignedSectorRetarded
open FullYDynamicSource FullYDynamicResponse GeneralThreeParticleResponse
open MeasureTheory Filter Set
open scoped BigOperators ENNReal
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

private theorem scalar_occupation (p : MixedSpectatorScalar61Exchange.RegularMomentum) :
    ActiveMatterSectorCharge.occupation * MixedSpectatorScalar61Exchange.actualScalar61Tree p =
      MixedSpectatorScalar61Exchange.actualScalar61Tree p * ActiveMatterSectorCharge.occupation := by
  rw [MixedSpectatorScalar61Exchange.actualScalar61Tree_source]
  simp only [sourceCoherentTree,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,
    smul_mul_assoc,actual_source_tree_occupation_commutes]

/-- The actual coefficient-level sum retains the source charge. Inverse
denominators and momenta do not supply a preservation premise. -/
theorem actual_coherent_occupation (p : Kinematics) :
    ActiveMatterSectorCharge.occupation * coherentTree p = coherentTree p * ActiveMatterSectorCharge.occupation := by
  have each (b : Fin 4) : ActiveMatterSectorCharge.occupation * block p b = block p b * ActiveMatterSectorCharge.occupation := by
    fin_cases b
    · exact MixedSpectatorContactExchange.actual_contact_occupation _ _ _
    · exact MixedSpectatorCanonical79Exchange.actual_canonical_occupation
        p.x p.k p.pLeft p.pRight p.canonicalRegular
    · exact MixedSpectatorDual24Exchange.actual_dual_occupation
        p.x p.k p.pLeft p.pRight p.dualRegular
    · exact scalar_occupation _
  simp only [coherentTree,Finset.mul_sum,Finset.sum_mul,each]

private theorem fixed_piece_charge (s : ℝ) (v : FockFiber) (hv : fiberPiece s v = v) :
    ActiveMatterSectorCharge.occupation (fiberCoordinates v) = (s : ℂ) • fiberCoordinates v := by
  funext word
  change (∑i ∈ word,(modeWeight i : ℂ))*v word = (s : ℂ)*v word
  rw [←cast_value]
  by_cases h : value word = s
  · rw [h]
  · have hz := congrArg (fun w : FockFiber => w word) hv
    rw [fiberPiece_apply,if_neg h] at hz
    rw [←hz,mul_zero,mul_zero]

private theorem neutral_basis_charge (word : Occupation) (neutral : value word = 0) :
    ActiveMatterSectorCharge.occupation (occupationBasis word) = (0 : ℂ) • occupationBasis word := by
  have h := SourceFockRaising.basis_eigenstate (fun i => (modeWeight i : ℂ)) word
  have hc : (∑i ∈ word,(modeWeight i : ℂ)) = 0 := by rw [←cast_value,neutral];rfl
  simpa only [ActiveMatterSectorCharge.occupation,hc] using h

theorem actual_coherent_neutral_point (p : Kinematics) (dual : Bool) (u : QuantumTest)
    (hu : ActualSignedSector.project (signedValue dual) u = u)
    (word : Occupation) (neutral : value word = 0) (z : SourceCoordinateSlice) :
    coherentSource p u z word = 0 := by
  have hv : fiberPiece (signedValue dual) (u z) = u z :=
    congrArg (fun q : QuantumTest => q z) hu
  have h := LowEnergy.Fermion.occupationCharge_selection modeWeight _
    (actual_coherent_occupation p) (fiberCoordinates (u z)) (occupationBasis word)
    (signedValue dual) 0
    (by cases dual <;> norm_num [signedValue])
    (fixed_piece_charge _ _ hv) (neutral_basis_charge word neutral)
  rw [LowEnergy.Fermion.pairing_occupation] at h
  change fiberCoordinates (coherentSource p u z) word = 0
  rw [actual_coherent_source_point]
  exact h

/-- The original fullY and independent-sharp response is followed by the
complete actual four-block exchange, on the generated cofinal finite range. -/
theorem actual_neutral_frequency_point (p : Kinematics) (dual : Bool) (f : ScalarTest)
    (F : Index) (sharp advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (ω : ℝ)
    (word : Occupation) (neutral : value word = 0) (z : SourceCoordinateSlice) :
    coherentSource p (literalResponse (saturate (signedValue dual) F) sharp
      (candidateTest dual f) advanced μ hμ ω) z word = 0 :=
  actual_coherent_neutral_point p dual _
    (actual_response_sector _ F _ (actual_candidate_core dual f) sharp advanced μ hμ ω)
    word neutral z

theorem actual_neutral_time_point (p : Kinematics) (dual : Bool) (f : ScalarTest)
    (F : Index) (sharp : Bool) (t : ℝ) (word : Occupation)
    (neutral : value word = 0) (z : SourceCoordinateSlice) :
    coherentSource p (literalCoreTime (saturate (signedValue dual) F) sharp
      (candidateTest dual f) t) z word = 0 :=
  actual_coherent_neutral_point p dual _
    (actual_time_sector _ F _ (actual_candidate_core dual f) sharp t) word neutral z

def neutralFrequency (p : Kinematics) (dual : Bool) (f : ScalarTest) (F : Index)
    (sharp advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (word : Occupation) (ω : ℝ) :
    GaussHistoryHilbert.SectorHilbert word.card :=
  output (saturate (signedValue dual) F) sharp (candidateTest dual f) p advanced μ hμ ω word

def neutralMeasure (p : Kinematics) (dual : Bool) (f : ScalarTest) (F : Index)
    (sharp advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (word : Occupation) : Measure ℝ :=
  volume.withDensity (fun ω => ENNReal.ofReal (‖neutralFrequency p dual f F sharp advanced μ hμ word ω‖^2))

private theorem embed_component_zero (u : QuantumTest) (word : Occupation)
    (hu : ∀z : SourceCoordinateSlice,u z word = 0) : embed u word = 0 := by
  apply Lp.ext
  filter_upwards [embed_ae u word,Lp.coeFn_zero ℂ 2 (GaussHistoryHilbert.numberMeasure word.card)] with z he hz
  rw [he,hu]
  exact hz.symm

theorem actual_neutral_frequency (p : Kinematics) (dual : Bool) (f : ScalarTest)
    (F : Index) (sharp advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (word : Occupation) (neutral : value word = 0) (ω : ℝ) :
    neutralFrequency p dual f F sharp advanced μ hμ word ω = 0 :=
  embed_component_zero _ word (actual_neutral_frequency_point p dual f F sharp advanced μ hμ ω word neutral)

/-- Every Borel channel band is zero because its literal propagated output
vanishes; no scalar width or lifetime is used to obtain this conclusion. -/
theorem actual_neutral_measure (p : Kinematics) (dual : Bool) (f : ScalarTest)
    (F : Index) (sharp advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (word : Occupation) (neutral : value word = 0) :
    neutralMeasure p dual f F sharp advanced μ hμ word = 0 := by
  simp only [neutralMeasure,actual_neutral_frequency p dual f F sharp advanced μ hμ word neutral,
    norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),ENNReal.ofReal_zero]
  exact withDensity_zero

/-- Strictly positive original-Y response and zero neutral four-block channels
belong to the same generated source profile and the same cofinal carrier. -/
theorem actual_generated_source_dynamic_selection (dual : Bool) :
    Tendsto (saturate (signedValue dual)) (sourceFilter : Filter Index) atTop ∧
    ∃f : ScalarTest,f GaussHistoryHilbert.sourcePoint.val = 1 ∧
      (∀F : Index,∀advanced : Bool,∀μ : ℝ,∀hμ : 0 < μ,
        0 < correctionMeasure (saturate (signedValue dual) F) (candidateTest dual f) advanced μ hμ Set.univ) ∧
      (∀p : Kinematics,∀F : Index,∀sharp advanced : Bool,∀μ : ℝ,∀hμ : 0 < μ,
        ∀word : Occupation,value word = 0 →
          (∀ω : ℝ,neutralFrequency p dual f F sharp advanced μ hμ word ω = 0) ∧
          neutralMeasure p dual f F sharp advanced μ hμ word = 0) ∧
      (∀p : Kinematics,∀F : Index,∀sharp : Bool,∀t : ℝ,∀word : Occupation,value word = 0 →
        ∀z : SourceCoordinateSlice,coherentSource p (literalCoreTime (saturate (signedValue dual) F)
          sharp (candidateTest dual f) t) z word = 0) := by
  obtain ⟨f,hf,hY⟩ := YukawaResolventDetection.actual_generated_candidate_Y_excess dual
  exact ⟨saturate_cofinal _,f,hf,
    fun F advanced μ hμ => (hY (saturate (signedValue dual) F) advanced μ hμ).1,
    fun p F sharp advanced μ hμ word neutral =>
      ⟨actual_neutral_frequency p dual f F sharp advanced μ hμ word neutral,
        actual_neutral_measure p dual f F sharp advanced μ hμ word neutral⟩,
    fun p F sharp t word neutral => actual_neutral_time_point p dual f F sharp t word neutral⟩

end LowEnergy.ActualFourBlockSignedSector
