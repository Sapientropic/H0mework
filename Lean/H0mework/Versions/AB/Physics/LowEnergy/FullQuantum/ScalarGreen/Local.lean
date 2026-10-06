import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.SpatialWeak.Green
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.ClosedLoops.Source
import H0mework.Versions.AB.Physics.LowEnergyResponse.Yukawa
import Mathlib.MeasureTheory.Function.Holder

/-! Arbitrary bounded fields in all 35 complex scalar coordinates generate their actual full-matter insertion. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ScalarGreen
open FullSpace SpatialGreen YangMills.FullPairing DiracExteriorMatterAction
open StageNineDynamicBreakingVacuum StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualFormNativeConjugateMatterVariation Triangular
noncomputable section

abbrev ScalarProfile := Lp (α := Position) ScalarCoordinateCarrier ⊤ volume

def scalarLinear : ScalarCoordinateCarrier →ₗ[ℂ] FiberOperators where
  toFun scalar := operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm scalar))
  map_add' left right := by
    rw [map_add,diracDualRightChiralYukawaAction_add,operator_add]
  map_smul' c scalar := by
    rw [map_smul,diracDualRightChiralYukawaAction_smul,operator_smul]
    rfl

def scalarMap : ScalarCoordinateCarrier →L[ℂ] FiberOperators :=
  ⟨scalarLinear,scalarLinear.continuous_of_finiteDimensional⟩

def matrixField (profile : ScalarProfile) : Lp (α := Position) FiberOperators ⊤ volume :=
  scalarMap.compLpL ⊤ volume profile

def potential (profile : ScalarProfile) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (ContinuousLinearMap.id ℂ FiberOperators).holderL volume ⊤ 2 2 (matrixField profile)

theorem potential_ae (profile : ScalarProfile) (field : FullMatterL2) :
    potential profile field=ᵐ[volume] fun x =>
      operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (profile x))) (field x) := by
  filter_upwards [(ContinuousLinearMap.id ℂ FiberOperators).coeFn_holder (p := ⊤) (q := 2) (r := 2) (matrixField profile) field,
    scalarMap.coeFn_compLpL profile] with x multiply native
  erw [multiply]
  change matrixField profile x (field x)=_
  erw [native]
  rfl

def six : FullMatterL2 →L[ℂ] FullMatterL2 := (operator MixedSymbol.degreeSix).compLpL 2 volume

theorem six_ae (field : FullMatterL2) : six field=ᵐ[volume] fun x => operator MixedSymbol.degreeSix (field x) :=
  (operator MixedSymbol.degreeSix).coeFn_compLpL field

theorem six_potential (profile : ScalarProfile) (field : FullMatterL2) : six (potential profile field)=potential profile field := by
  apply Lp.ext
  filter_upwards [six_ae (potential profile field),potential_ae profile field] with x outer inner
  rw [outer,inner]
  have source : operator MixedSymbol.degreeSix*
      operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (profile x)))=
      operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (profile x))) := by
    simpa only [operator_mul] using congrArg operator (ClosedLoops.original_scalar_vertex (profile x)).1
  exact congrArg (fun A : FiberOperators => A (field x)) source

theorem potential_six (profile : ScalarProfile) (field : FullMatterL2) : potential profile (six field)=0 := by
  apply Lp.ext
  filter_upwards [potential_ae profile (six field),six_ae field,Lp.coeFn_zero (E := Hilbert) (p := 2) (μ := volume)]
    with x applied projected zero
  rw [applied,projected,zero]
  have source : operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (profile x)))*
      operator MixedSymbol.degreeSix=0 := by
    simpa only [operator_mul,operator_zero] using congrArg operator (ClosedLoops.original_scalar_vertex (profile x)).2
  exact congrArg (fun A : FiberOperators => A (field x)) source

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ScalarGreen
