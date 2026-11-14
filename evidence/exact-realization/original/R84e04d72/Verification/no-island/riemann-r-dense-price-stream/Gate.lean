import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.RelationInventory

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace PrefixImageCertificate

open SourceGeneratedFiniteGram Filter Set
open scoped InnerProductSpace Topology BigOperators lp ENNReal
open private prefix_projection from SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixImage

private theorem finite_exact_readings_and_bounded_energy_characterize_the_source_image
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (source : Nat → H) (data : Nat → ℂ) :
    ((∀ n, PrefixImage.residual source data n = 0) ∧ BddAbove (range (PrefixImage.energy source data))) ↔
      ∃ x : H, PrefixImage.read source x = data :=
  PrefixImage.admitted_iff_image source data

#eval IO.println "CP617_CONTROL + finite_exact_readings_and_bounded_energy_characterize_the_source_image"

private theorem nested_actual_finite_inverses_pay_the_innovation_and_give_a_Cauchy_limit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (source : Nat → H) (data : PrefixImage.Admitted source) {m n : Nat} (within : m ≤ n) :
    PrefixImage.approximate source data.val m =
      (Projection.sourceSpan (fun i : Fin m => source i.val)).starProjection
        (PrefixImage.approximate source data.val n) ∧
    PrefixImage.energy source data.val n = PrefixImage.energy source data.val m +
      ‖PrefixImage.approximate source data.val n-PrefixImage.approximate source data.val m‖^2 ∧
    CauchySeq (PrefixImage.approximate source data.val) ∧
    PrefixImage.read source (PrefixImage.realize source data) = data.val :=
  ⟨prefix_projection source data.val within (data.property.1 n),
    PrefixImage.energy_increment source data.val within (data.property.1 n),
    PrefixImage.cauchy_from_budget source data,PrefixImage.read_realized source data⟩

#eval IO.println "CP617_CONTROL + nested_actual_finite_inverses_pay_the_innovation_and_give_a_Cauchy_limit"

private abbrev TestSpace := lp (fun _ : Nat => ℂ) 2

private def unitTest (i : Nat) : TestSpace := lp.single 2 i 1

private def ones (_ : Nat) : ℂ := 1

private def finiteField (n : Nat) : TestSpace := ∑ j ∈ Finset.range n, unitTest j

private theorem unit_read (x : TestSpace) (i : Nat) : PrefixImage.read unitTest x i = x i := by
  change inner ℂ (lp.single 2 i (1 : ℂ)) x = x i
  rw [lp.inner_single_left]
  simp only [RCLike.inner_apply,map_one,mul_one]

private theorem finite_field_reads_one {n i : Nat} (within : i < n) : finiteField n i = 1 := by
  have measured := lp.coeFn_sum unitTest (Finset.range n)
  have coordinate := congrFun measured i
  rw [Finset.sum_apply] at coordinate
  calc
    finiteField n i = ∑ j ∈ Finset.range n, unitTest j i := coordinate
    _ = unitTest i i := by
      apply Finset.sum_eq_single i
      · intro j _ other
        exact lp.single_apply_ne 2 j 1 other.symm
      · intro omitted
        exact (omitted (Finset.mem_range.mpr within)).elim
    _ = 1 := lp.single_apply_self 2 i 1

private theorem every_finite_prefix_of_ones_has_a_real_source (n : Nat) :
    PrefixImage.residual unitTest ones n = 0 := by
  have same : PrefixImage.sample ones n =
      PrefixImage.sample (PrefixImage.read unitTest (finiteField n)) n := by
    ext i
    change 1 = PrefixImage.read unitTest (finiteField n) i.val
    exact ((unit_read (finiteField n) i.val).trans (finite_field_reads_one i.isLt)).symm
  unfold PrefixImage.residual PrefixImage.approximate
  rw [same]
  exact PrefixImage.residual_original unitTest (finiteField n) n

private theorem finite_exact_ones_have_unbounded_energy_and_no_whole_l2_source :
    (∀ n, PrefixImage.residual unitTest ones n = 0) ∧
    (¬ BddAbove (range (PrefixImage.energy unitTest ones))) ∧
    ¬ ∃ x : TestSpace, PrefixImage.read unitTest x = ones := by
  have outside : ¬ ∃ x : TestSpace, PrefixImage.read unitTest x = ones := by
    rintro ⟨x,same⟩
    have every : (fun i : Nat => x i) = ones := by
      funext i
      exact (unit_read x i).symm.trans (congrFun same i)
    have member : Memℓp ones 2 := by
      rw [← every]
      exact lp.memℓp x
    have cost := member.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    have constant : Summable (fun _ : Nat => (1 : ℝ)) := by
      simpa only [ones,norm_one,Real.one_rpow] using cost
    have impossible : (0 : ℝ) = 1 :=
      tendsto_nhds_unique constant.tendsto_atTop_zero tendsto_const_nhds
    exact zero_ne_one impossible
  exact ⟨every_finite_prefix_of_ones_has_a_real_source,
    fun budget => outside ((PrefixImage.admitted_iff_image unitTest ones).mp
      ⟨every_finite_prefix_of_ones_has_a_real_source,budget⟩),outside⟩

#eval IO.println "CP617_CONTROL - finite_exact_ones_have_unbounded_energy_and_no_whole_l2_source"

end PrefixImageCertificate

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace DivisionPriceStreamCertificate

open BurnolPhysicalState Filter Set SourceGeneratedFiniteGram
open scoped InnerProductSpace Topology
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.DivisionPriceStream
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock.SingleSlot
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
open private price_read cotests from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream

attribute [local instance] OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock.SingleSlot.wideInner

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2*(k+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "Data" => DivisionPriceStream.Stream observation nontrivial half depth
local notation "priceAt" => DivisionPriceStream.prices observation nontrivial half depth
local notation "measured" => DivisionPriceStream.capture observation nontrivial half depth
local notation "decoded" => DivisionPriceStream.graph observation nontrivial half depth
local notation "nextOf" => DivisionPriceStream.advance observation nontrivial half depth
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down

private def secondSlots : Wide →L[ℂ] SecondSlots :=
  (WithLp.sndL 2 ℂ Base SecondSlots).comp unitGap.subtypeL

private theorem the_original_full_P_prices_restore_the_same_Gamma_squared_graph (x : Wide) (data : Data) :
    type_of% (original_price_image observation nontrivial half depth data.val) ∧
    priceAt x = PrefixImage.read (cotests observation nontrivial half depth) x ∧
    decoded (measured x) = x ∧
    secondSlots (decoded (measured x)) = secondSlots x ∧ priceAt (decoded data) = data.val := by
  have graph := graph_capture observation nontrivial half depth x
  exact ⟨original_price_image observation nontrivial half depth data.val,
    price_read observation nontrivial half depth x,graph,congrArg secondSlots graph,
    prices_graph observation nontrivial half depth data⟩

#eval IO.println "CP617_CONTROL + the_original_full_P_prices_restore_the_same_Gamma_squared_graph"

private def LiteralWholeNext (ordinal : Nat) : Prop :=
  type_of% (actual_relation_stock_next observation nontrivial half depth ordinal) ∧
  type_of% (actual_division_action_same_root observation nontrivial half depth ordinal)

private theorem literal_whole_next (ordinal : Nat) :
    LiteralWholeNext observation nontrivial half depth ordinal :=
  ⟨actual_relation_stock_next observation nontrivial half depth ordinal,
    actual_division_action_same_root observation nontrivial half depth ordinal⟩

private theorem the_recovered_stream_executes_original_R_and_its_original_relations_whole_next
    (data : Data) (ordinal : Nat) :
    (nextOf data).val = priceAt (advanceWide c observation.mathlibZero (decoded data)) ∧
    type_of% (exact_write observation nontrivial half depth data) ∧
    type_of% (actual_current_and_next observation nontrivial half depth ordinal) ∧
    LiteralWholeNext observation nontrivial half depth ordinal :=
  ⟨rfl,exact_write observation nontrivial half depth data,
    actual_current_and_next observation nontrivial half depth ordinal,
    literal_whole_next observation nontrivial half depth ordinal⟩

#eval IO.println "CP617_CONTROL + the_recovered_stream_executes_original_R_and_its_original_relations_whole_next"
#eval IO.println "CP617_GATE_PASS positive=4 negative=1"

end DivisionPriceStreamCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
