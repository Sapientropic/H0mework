import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.InnovationInsert
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DelayedLiteralRead

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead

open BurnolPhysicalState Finset
open scoped InnerProductSpace

open private literal_price_horizon_kernel actual_price_window_write from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DelayedLiteralRead
open private raw_power from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FixedFourierKFeedback

namespace PriceGram
export SourceGeneratedFiniteGram.Projection (sourceSpan innovationCLM innovation_ne_zero_of_new_column insertedCoefficient insertion_read)
end PriceGram

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "cols" => literalPriceColumn observation nontrivial half depth
local notation "read" => readPriceWindow observation half

/-- The original enlarged prefix chooses the common window for old and newborn columns. -/
def birthPriceWidth (start ordinal : Nat) : Nat :=
  literalPriceHorizon observation nontrivial half depth start (range (ordinal+2))

local notation "width" => birthPriceWidth observation nontrivial half depth

def oldPriceColumns (start ordinal : Nat) (j : range (ordinal+1)) :
    PriceGram.Coordinates (Fin (width start ordinal)) :=
  cols start (range (ordinal+1)) (width start ordinal) j

def bornPriceColumn (start ordinal : Nat) : PriceGram.Coordinates (Fin (width start ordinal)) :=
  cols start (range (ordinal+2)) (width start ordinal)
    ⟨ordinal+1, mem_range.mpr (Nat.lt_succ_self _)⟩

local notation "old" => oldPriceColumns observation nontrivial half depth
local notation "born" => bornPriceColumn observation nontrivial half depth

private def enlargedIndex (ordinal : Nat) : Option (range (ordinal+1)) → range (ordinal+2)
  | none => ⟨ordinal+1,mem_range.mpr (Nat.lt_succ_self _)⟩
  | some j => ⟨j.val,mem_range.mpr ((mem_range.mp j.property).trans (Nat.lt_succ_self _))⟩

private theorem enlargedIndex_injective (ordinal : Nat) : Function.Injective (enlargedIndex ordinal) := by
  intro i j same
  have values := congrArg Subtype.val same
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j =>
      change ordinal+1=j.val at values
      exact ((ne_of_lt (mem_range.mp j.property)) values.symm).elim
  | some i =>
    cases j with
    | none =>
      change i.val=ordinal+1 at values
      exact ((ne_of_lt (mem_range.mp i.property)) values).elim
    | some j =>
      exact congrArg Option.some (Subtype.ext values)

private def augmented (start ordinal : Nat) (j : Option (range (ordinal+1))) :
    PriceGram.Coordinates (Fin (width start ordinal)) :=
  cols start (range (ordinal+2)) (width start ordinal) (enlargedIndex ordinal j)

private theorem augmented_independent (start ordinal : Nat) :
    LinearIndependent ℂ (augmented observation nontrivial half depth start ordinal) := by
  classical
  let full := cols start (range (ordinal+2)) (width start ordinal)
  have kernel : (PriceGram.synthesis full).ker = ⊥ :=
    literal_price_horizon_kernel observation nontrivial half depth start (range (ordinal+2))
  have independent : LinearIndependent ℂ full := by
    apply Fintype.linearIndependent_iff.mpr
    intro a erased i
    let coordinates : PriceGram.Coordinates (range (ordinal+2)) := WithLp.toLp 2 a
    have unseen : coordinates ∈ (PriceGram.synthesis full).ker := erased
    rw [kernel] at unseen
    have same : coordinates = 0 := unseen
    exact congrArg (fun v : PriceGram.Coordinates (range (ordinal+2)) => v i) same
  exact independent.comp (enlargedIndex ordinal) (enlargedIndex_injective ordinal)

private theorem old_columns_faithful (start ordinal : Nat) :
    Function.Injective (PriceGram.synthesis (old start ordinal)) := by
  classical
  have independent : LinearIndependent ℂ (old start ordinal) :=
    (augmented_independent observation nontrivial half depth start ordinal).comp
      Option.some (Option.some_injective (range (ordinal+1)))
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro a erased
  have gone := (Fintype.linearIndependent_iff.mp independent) (fun i => a i) erased
  change a = 0
  ext i
  exact gone i

private theorem born_not_old (start ordinal : Nat) : born start ordinal ∉ PriceGram.sourceSpan (old start ordinal) := by
  classical
  rintro ⟨a, paid⟩
  let test : Option (range (ordinal+1)) → ℂ := fun i => i.elim (-1) (fun j => a j)
  have collapse : ∑ i : Option (range (ordinal+1)),
      test i • augmented observation nontrivial half depth start ordinal i = 0 := by
    rw [Fintype.sum_option]
    change (-1:ℂ) • born start ordinal + PriceGram.synthesis (old start ordinal) a = 0
    rw [paid, neg_one_smul, neg_add_cancel]
  have gone := (Fintype.linearIndependent_iff.mp
    (augmented_independent observation nontrivial half depth start ordinal)) test collapse none
  norm_num [test] at gone

/-- The new literal column generates a nonzero residual against the complete old prefix. -/
theorem actual_born_price_innovation (start ordinal : Nat) :
    PriceGram.innovationCLM (old start ordinal) (born start ordinal) ≠ 0 :=
  PriceGram.innovation_ne_zero_of_new_column _ (born_not_old observation nontrivial half depth start ordinal)

private theorem born_column_read (start ordinal : Nat) :
    read (width start ordinal) (raw (start+ordinal+1)) = born start ordinal := by
  ext n
  change inner ℂ (fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2))
      (((burnolDirectRightResolventCLM c)^n.val) (raw (start+ordinal+1))) =
    FixedFourierKFeedback.price observation nontrivial half depth (start+ordinal+1+n.val)
  rw [← FixedFourierKFeedback.actual_whole_price observation nontrivial half depth, raw_power, raw_power,
    ← mul_apply_eq_comp, ← pow_add]
  rw [show n.val+(m+(start+ordinal+1+2))=m+(start+ordinal+1+n.val+2) by omega]

/-- Decode the newborn scalar from its innovation, then reuse the old Gram solver. -/
def decodeBornPrices (start ordinal : Nat) (values : PriceGram.Coordinates (Fin (width start ordinal))) :
    PriceGram.Coordinates (range (ordinal+1)) × ℂ :=
  let fresh := PriceGram.insertedCoefficient (old start ordinal) (born start ordinal) values
  (PriceGram.coefficients (old start ordinal) (values-fresh • born start ordinal),fresh)

theorem actual_born_price_decode (start ordinal : Nat) (a : PriceGram.Coordinates (range (ordinal+1))) (b : ℂ) :
    decodeBornPrices observation nontrivial half depth start ordinal
      (read (width start ordinal) ((∑ j : range (ordinal+1), a j • raw (start+j.val))+
        b • raw (start+ordinal+1))) = (a,b) := by
  have linear (v w : BurnolL2) :
      read (width start ordinal) (v+b • w) = read (width start ordinal) v+b • read (width start ordinal) w := by
    ext n
    simp only [readPriceWindow, WithLp.ofLp_toLp, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
      map_add, map_smul, inner_add_right, inner_smul_right, smul_eq_mul]
  rw [linear, actual_price_window_write observation nontrivial half depth, born_column_read]
  have decoded := PriceGram.insertion_read (old start ordinal) (born start ordinal)
    (born_not_old observation nontrivial half depth start ordinal)
    (old_columns_faithful observation nontrivial half depth start ordinal) a b
  exact Prod.ext decoded.2 decoded.1

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
