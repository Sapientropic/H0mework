import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementDensity.LaplaceIntegers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceIntegers

open SourceGaussianModel SourceJetIncidence SourceFiniteData

private noncomputable def secondStencil (response : JetIndex → JetIndex → Nat)
    (left right : MultiIndex) (axis : Fin 3) : Nat :=
  response (sourceJetIndex (raise (raise left axis) axis)) (sourceJetIndex right) +
    2 * response (sourceJetIndex (raise left axis)) (sourceJetIndex (raise right axis)) +
      response (sourceJetIndex left) (sourceJetIndex (raise (raise right axis) axis))

private noncomputable def fourthStencil (response : JetIndex → JetIndex → Nat)
    (innerAxis axis : Fin 3) : Nat :=
  secondStencil response (raise (raise (fun _ => 0) innerAxis) innerAxis) (fun _ => 0) axis +
    2 * secondStencil response (raise (fun _ => 0) innerAxis) (raise (fun _ => 0) innerAxis) axis +
      secondStencil response (fun _ => 0) (raise (raise (fun _ => 0) innerAxis) innerAxis) axis

private theorem fourthStencil_symm (response : JetIndex → JetIndex → Nat) (innerAxis axis : Fin 3) :
    fourthStencil response innerAxis axis = fourthStencil response axis innerAxis := by
  unfold fourthStencil secondStencil
  fin_cases innerAxis <;> fin_cases axis <;>
    norm_num [sourceJetIndex, sourceJetCode, raise, Function.update, Fin.ext_iff] <;> ring

theorem fourthInt_symm (innerAxis axis : Fin 3) : fourthInt innerAxis axis = fourthInt axis innerAxis :=
  fourthStencil_symm bilinearByIndex innerAxis axis

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceIntegers
