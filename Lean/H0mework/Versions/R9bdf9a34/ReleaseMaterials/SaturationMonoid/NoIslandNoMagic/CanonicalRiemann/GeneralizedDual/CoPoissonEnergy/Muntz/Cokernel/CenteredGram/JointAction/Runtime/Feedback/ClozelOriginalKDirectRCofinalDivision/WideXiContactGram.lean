import H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixImage.ContactFibre
import H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiBoundaryConsumer

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 140000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace WideResidualReturn.XiContact

open BurnolPhysicalState Filter SourceGeneratedFiniteGram
open OriginalKFiniteOrderRelease.PositionGapCayley
open HilbertInventory HilbertInventory.SecondConductorStock HilbertInventory.SecondConductorStock.SingleSlot
open OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open scoped Topology InnerProductSpace lp

attribute [local instance] HilbertInventory.SecondConductorStock.SingleSlot.wideInner
attribute [local instance] DivisionEffectPrice.wideNormed

open private contactComplete from H0mework.Versions.R9bdf9a34.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideXiAdjointStock
open private cotests price_read from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream
open private cotests_separate from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DenseDivisionPrice

namespace JointGram

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "a" => OriginalPrimitiveRankBalance.conjugateCoordinate c
local notation "degree" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "S" => contact a degree
local notation "A" => advanceWide c observation.mathlibZero
local notation "stock" => actualWide observation nontrivial half depth
local notation "tests" => cotests observation nontrivial half depth
local notation "readSample" => sample observation nontrivial half depth
local notation "nativeInput" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth

local instance paidContact : CompleteSpace ↥S := contactComplete a degree

abbrev Address (n : Nat) := Sum (Fin n) (Fin n)
abbrev JointBank (n : Nat) := Coordinates (Address n)

/-- Both banks are observations of the same predecessor, with next tests pulled back by the actual R. -/
def test (n : Nat) : Address n → Wide
  | .inl i => tests i.val
  | .inr i => ContinuousLinearMap.adjoint A (tests i.val)

def bankMap (n : Nat) : BurnolL2 × BurnolL2 →ₗ[ℂ] JointBank n where
  toFun x := WithLp.toLp 2 (Sum.elim (fun i => readSample n x.1 i) (fun i => readSample n x.2 i))
  map_add' x y := by
    ext i
    cases i with
    | inl j =>
      change readSample n (x.1+y.1) j = readSample n x.1 j + readSample n y.1 j
      exact congrArg (fun data : PriceBank n => data j) (map_add (readSample n) _ _)
    | inr j =>
      change readSample n (x.2+y.2) j = readSample n x.2 j + readSample n y.2 j
      exact congrArg (fun data : PriceBank n => data j) (map_add (readSample n) _ _)
  map_smul' scalar x := by
    ext i
    cases i with
    | inl j =>
      change readSample n (scalar • x.1) j = scalar • readSample n x.1 j
      exact congrArg (fun data : PriceBank n => data j) (map_smul (readSample n) scalar _)
    | inr j =>
      change readSample n (scalar • x.2) j = scalar • readSample n x.2 j
      exact congrArg (fun data : PriceBank n => data j) (map_smul (readSample n) scalar _)

/-- The two original material occurrences supply two banks of unmodified K prices. -/
def bank (n : Nat) : JointBank n :=
  bankMap observation nontrivial half depth n ((nativeInput ordinal).1, (nativeInput (ordinal+1)).1)

theorem bank_source (n : Nat) :
    bank observation nontrivial half depth ordinal n =
      Projection.rhs (test observation nontrivial half depth n) (stock ordinal) := by
  have current := sample_source observation nontrivial half depth ordinal n
  have next := sample_source observation nontrivial half depth (ordinal+1) n
  ext i
  cases i with
  | inl j =>
    change readSample n (nativeInput ordinal).1 j = inner ℂ (tests j.val) (stock ordinal)
    exact (congrArg (fun data : PriceBank n => data j) current).trans
      (congrFun (price_read observation nontrivial half depth (stock ordinal)) j.val)
  | inr j =>
    change readSample n (nativeInput (ordinal+1)).1 j = inner ℂ (ContinuousLinearMap.adjoint A (tests j.val)) (stock ordinal)
    have read := (congrArg (fun data : PriceBank n => data j) next).trans
      (congrFun (price_read observation nontrivial half depth (stock (ordinal+1))) j.val)
    have pulled := ContinuousLinearMap.adjoint_inner_left A (stock ordinal) (tests j.val)
    exact read.trans ((congrArg (inner ℂ (tests j.val)) (actual_wide_next observation nontrivial half depth ordinal)).symm.trans
      pulled.symm)

def recover (n : Nat) : JointBank n →ₗ[ℂ] ↥S :=
  @SourceGeneratedFiniteGram.PrefixImage.ContactFibre.recover Wide (inferInstanceAs (NormedAddCommGroup Wide)) wideInner _ S
    (paidContact observation half) _ _ (test observation nontrivial half depth n)

local notation "decode" => recover observation nontrivial half depth
local notation "data" => bank observation nontrivial half depth ordinal

def fit (n : Nat) : S := decode n (data n)

theorem fit_equations (n : Nat) :
    Projection.rhs (test observation nontrivial half depth n)
      (fit observation nontrivial half depth ordinal n : Wide) = data n := by
  let x : S := ⟨stock ordinal, literal_contact observation nontrivial half depth ordinal⟩
  exact @SourceGeneratedFiniteGram.PrefixImage.ContactFibre.recover_equation Wide (inferInstanceAs (NormedAddCommGroup Wide)) wideInner _ S
    (paidContact observation half) _ _ (test observation nontrivial half depth n) (data n) x
    (bank_source observation nontrivial half depth ordinal n)

theorem fit_tendsto :
    Tendsto (fit observation nontrivial half depth ordinal) atTop
      (𝓝 (⟨stock ordinal, literal_contact observation nontrivial half depth ordinal⟩ : ↥S)) := by
  let x : S := ⟨stock ordinal, literal_contact observation nontrivial half depth ordinal⟩
  have separating (z : Wide) (silent : ∀ i, inner ℂ (tests i) z = 0) : z = 0 :=
    cotests_separate observation nontrivial half depth z silent
  exact @SourceGeneratedFiniteGram.PrefixImage.ContactFibre.recover_refined_tendsto Wide
    (inferInstanceAs (NormedAddCommGroup Wide)) wideInner S (paidContact observation half)
    Address _ _ tests separating (test observation nontrivial half depth)
    (fun _ => Sum.inl) (fun _ _ => rfl) data x
    (bank_source observation nontrivial half depth ordinal)

end JointGram
end WideResidualReturn.XiContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
