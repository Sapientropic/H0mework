import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.HeatQuarticSource
import H0mework.Versions.X.NavierStokes.HigherTreeSeptic.PrimitiveKernel

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSepticAlignment
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open NativeUnheatedTreeRieszKernel (Wave)
open NativeUnheatedTreeHeatPacket
noncomputable section

def quintic (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (i j response outside l m p q : Coordinate) :
    Alignment nu
      (fun k index => NativeUnheatedQuinticFiveRows.nodes slot leaf k i j outside l m p q index)
      (fun k index => NativeUnheatedSexticSixRows.base nu slot leaf k i j response outside l m p q index) := by
  let paid := grow (NativeUnheatedTreeQuarticStartKernel.alignment nu slot i j response outside l m) leaf p q
  convert! paid using 1
  · funext k index number
    fin_cases number <;> rfl
  · funext k index
    unfold splitKernel NativeUnheatedTreeNormalForm.normalizer NativeUnheatedTreeTime.sumRate
    rw [Fin.sum_univ_five]
    rfl

def sextic (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5)
    (i j response outside l m p q r s : Coordinate) :
    Alignment nu
      (fun k index => NativeUnheatedSexticSixRows.nodes slot leaf position k i j outside l m p q r s index)
      (fun k index => NativeUnheatedSepticSevenRows.base nu slot leaf position k i j response outside l m p q r s index) := by
  exact grow (quintic nu slot leaf i j response outside l m p q) position r s

def septic (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (i j response outside l m p q r s u v : Coordinate) :
    Alignment nu
      (fun k index => NativeUnheatedSepticSevenRows.nodes slot leaf position newest k i j outside l m p q r s u v index)
      (fun k index => NativeUnheatedTreeNormalForm.normalizer nu
        (NativeUnheatedSepticSevenRows.nodes slot leaf position newest k i j outside l m p q r s u v index)
        (NativeUnheatedSepticSevenRows.kernel nu slot leaf position newest k i j response outside l m p q r s u v index)) :=
  grow (sextic nu slot leaf position i j response outside l m p q r s) newest u v

end
end SaturationMonoid.NavierStokes.NativeUnheatedSepticAlignment
