import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B108

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2593_pa : Scalar.QComplex := ((999999002931435790028414918052 : Int)/10^30,(-1412138850918783210866801125 : Int)/10^30)
theorem v2593_pa_checked : Scalar.distance (sourceCoefficient 31 83 1 0) v2593_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2593_pb : Scalar.QComplex := ((-609306101540634014171846 : Int)/10^30,(-431477041810895808713435093 : Int)/10^30)
theorem v2593_pb_checked : Scalar.distance (sourceCoefficient 31 83 1 1) v2593_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2593_pg : Scalar.QComplex := ((-93086331800295035997367 : Int)/10^30,(131450956690329871868 : Int)/10^30)
theorem v2593_pg_checked : Scalar.distance (sourceCoefficient 31 83 1 2) v2593_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2593_mb : Scalar.QComplex := ((-981651128746352705231888 : Int)/10^30,(-431476355348550166090895113 : Int)/10^30)
theorem v2593_mb_checked : Scalar.distance (sourceCoefficient 31 83 3 1) v2593_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2593_mg : Scalar.QComplex := ((-93086183703744158781388 : Int)/10^30,(211780219636032583035 : Int)/10^30)
theorem v2593_mg_checked : Scalar.distance (sourceCoefficient 31 83 3 2) v2593_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2593_upper : Scalar.QComplex := ((999995076326840608234436507660 : Int)/10^30,(-3138044307562617990272002978 : Int)/10^30)
theorem v2593_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 83 5) 1) 14) v2593_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2593 : Material (31 : Basis) (83 : Basis) where
  plus := ![v2593_pa,v2593_pb,v2593_pg]
  minus := ![(Primitive.Addresses.material2593 1).one,v2593_mb,v2593_mg]
  upper := v2593_upper
  lower := (Primitive.Addresses.material2593 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2593_pa_checked.trans (by decide +kernel)
    · exact v2593_pb_checked.trans (by decide +kernel)
    · exact v2593_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 83 Primitive.Addresses.material2593
    · exact v2593_mb_checked.trans (by decide +kernel)
    · exact v2593_mg_checked.trans (by decide +kernel)
  upper_error := v2593_upper_checked
  lower_error := reuse_lower_error 31 83 Primitive.Addresses.material2593

def v2594_pa : Scalar.QComplex := ((999998952692831908187762296285 : Int)/10^30,(-1447277872190174867428571847 : Int)/10^30)
theorem v2594_pa_checked : Scalar.distance (sourceCoefficient 31 84 1 0) v2594_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2594_pb : Scalar.QComplex := ((-624467791443365658518848 : Int)/10^30,(-431477015874471514843100898 : Int)/10^30)
theorem v2594_pb_checked : Scalar.distance (sourceCoefficient 31 84 1 1) v2594_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2594_pg : Scalar.QComplex := ((-93086326664282745504130 : Int)/10^30,(134721921879917154095 : Int)/10^30)
theorem v2594_pg_checked : Scalar.distance (sourceCoefficient 31 84 1 2) v2594_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2594_mb : Scalar.QComplex := ((-996812790621728242909186 : Int)/10^30,(-431476316328280000643639160 : Int)/10^30)
theorem v2594_mb_checked : Scalar.distance (sourceCoefficient 31 84 3 1) v2594_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2594_mg : Scalar.QComplex := ((-93086175745038140849838 : Int)/10^30,(215051179175542745396 : Int)/10^30)
theorem v2594_mg_checked : Scalar.distance (sourceCoefficient 31 84 3 2) v2594_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2594_upper : Scalar.QComplex := ((999994965441548623578940020036 : Int)/10^30,(-3173183189791292492976006148 : Int)/10^30)
theorem v2594_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 84 5) 1) 14) v2594_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2594 : Material (31 : Basis) (84 : Basis) where
  plus := ![v2594_pa,v2594_pb,v2594_pg]
  minus := ![(Primitive.Addresses.material2594 1).one,v2594_mb,v2594_mg]
  upper := v2594_upper
  lower := (Primitive.Addresses.material2594 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2594_pa_checked.trans (by decide +kernel)
    · exact v2594_pb_checked.trans (by decide +kernel)
    · exact v2594_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 84 Primitive.Addresses.material2594
    · exact v2594_mb_checked.trans (by decide +kernel)
    · exact v2594_mg_checked.trans (by decide +kernel)
  upper_error := v2594_upper_checked
  lower_error := reuse_lower_error 31 84 Primitive.Addresses.material2594

def v2595_pa : Scalar.QComplex := ((999998835150662574532228633990 : Int)/10^30,(-1526334602234043779519181812 : Int)/10^30)
theorem v2595_pa_checked : Scalar.distance (sourceCoefficient 31 85 1 0) v2595_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2595_pb : Scalar.QComplex := ((-658578973514019980094570 : Int)/10^30,(-431476954925086958513185235 : Int)/10^30)
theorem v2595_pb_checked : Scalar.distance (sourceCoefficient 31 85 1 1) v2595_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2595_pg : Scalar.QComplex := ((-93086314618919628393894 : Int)/10^30,(142081028500293654866 : Int)/10^30)
theorem v2595_pg_checked : Scalar.distance (sourceCoefficient 31 85 1 2) v2595_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2595_mb : Scalar.QComplex := ((-1030923907394656707811929 : Int)/10^30,(-431476225942504322190370468 : Int)/10^30)
theorem v2595_mb_checked : Scalar.distance (sourceCoefficient 31 85 3 1) v2595_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2595_mg : Scalar.QComplex := ((-93086157349101937252353 : Int)/10^30,(222410272661181656563 : Int)/10^30)
theorem v2595_mg_checked : Scalar.distance (sourceCoefficient 31 85 3 2) v2595_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2595_upper : Scalar.QComplex := ((999994711454810269984634008632 : Int)/10^30,(-3252239599222327733001857799 : Int)/10^30)
theorem v2595_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 85 5) 1) 14) v2595_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2595 : Material (31 : Basis) (85 : Basis) where
  plus := ![v2595_pa,v2595_pb,v2595_pg]
  minus := ![(Primitive.Addresses.material2595 1).one,v2595_mb,v2595_mg]
  upper := v2595_upper
  lower := (Primitive.Addresses.material2595 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2595_pa_checked.trans (by decide +kernel)
    · exact v2595_pb_checked.trans (by decide +kernel)
    · exact v2595_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 85 Primitive.Addresses.material2595
    · exact v2595_mb_checked.trans (by decide +kernel)
    · exact v2595_mg_checked.trans (by decide +kernel)
  upper_error := v2595_upper_checked
  lower_error := reuse_lower_error 31 85 Primitive.Addresses.material2595

def v2596_pa : Scalar.QComplex := ((999998812783259825424025335276 : Int)/10^30,(-1540919229182880889193369975 : Int)/10^30)
theorem v2596_pa_checked : Scalar.distance (sourceCoefficient 31 86 1 0) v2596_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2596_pb : Scalar.QComplex := ((-664871908208751255533241 : Int)/10^30,(-431476943288104603979024343 : Int)/10^30)
theorem v2596_pb_checked : Scalar.distance (sourceCoefficient 31 86 1 1) v2596_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2596_pg : Scalar.QComplex := ((-93086312322594657005747 : Int)/10^30,(143438658924386528945 : Int)/10^30)
theorem v2596_pg_checked : Scalar.distance (sourceCoefficient 31 86 1 2) v2596_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2596_mb : Scalar.QComplex := ((-1037216829704049133345184 : Int)/10^30,(-431476208875007082340970660 : Int)/10^30)
theorem v2596_mb_checked : Scalar.distance (sourceCoefficient 31 86 3 1) v2596_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2596_mg : Scalar.QComplex := ((-93086153881203910303266 : Int)/10^30,(223767900598141649307 : Int)/10^30)
theorem v2596_mg_checked : Scalar.distance (sourceCoefficient 31 86 3 2) v2596_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2596_upper : Scalar.QComplex := ((999994663915697827823768163680 : Int)/10^30,(-3266824165844968242978221052 : Int)/10^30)
theorem v2596_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 86 5) 1) 14) v2596_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2596 : Material (31 : Basis) (86 : Basis) where
  plus := ![v2596_pa,v2596_pb,v2596_pg]
  minus := ![(Primitive.Addresses.material2596 1).one,v2596_mb,v2596_mg]
  upper := v2596_upper
  lower := (Primitive.Addresses.material2596 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2596_pa_checked.trans (by decide +kernel)
    · exact v2596_pb_checked.trans (by decide +kernel)
    · exact v2596_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 86 Primitive.Addresses.material2596
    · exact v2596_mb_checked.trans (by decide +kernel)
    · exact v2596_mg_checked.trans (by decide +kernel)
  upper_error := v2596_upper_checked
  lower_error := reuse_lower_error 31 86 Primitive.Addresses.material2596

def v2597_pa : Scalar.QComplex := ((999998811294640813483014524462 : Int)/10^30,(-1541884984476015646825354842 : Int)/10^30)
theorem v2597_pa_checked : Scalar.distance (sourceCoefficient 31 87 1 0) v2597_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2597_pb : Scalar.QComplex := ((-665288609640882258805321 : Int)/10^30,(-431476942513214589462033631 : Int)/10^30)
theorem v2597_pb_checked : Scalar.distance (sourceCoefficient 31 87 1 1) v2597_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2597_pg : Scalar.QComplex := ((-93086312169722632536953 : Int)/10^30,(143528557607907952483 : Int)/10^30)
theorem v2597_pg_checked : Scalar.distance (sourceCoefficient 31 87 1 2) v2597_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2597_mb : Scalar.QComplex := ((-1037633530312327966461192 : Int)/10^30,(-431476207740522787957710255 : Int)/10^30)
theorem v2597_mb_checked : Scalar.distance (sourceCoefficient 31 87 3 1) v2597_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2597_mg : Scalar.QComplex := ((-93086153650753427763129 : Int)/10^30,(223857799116268012380 : Int)/10^30)
theorem v2597_mg_checked : Scalar.distance (sourceCoefficient 31 87 3 2) v2597_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2597_upper : Scalar.QComplex := ((999994660760275009691119326112 : Int)/10^30,(-3267789917130502568923487355 : Int)/10^30)
theorem v2597_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 87 5) 1) 14) v2597_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2597 : Material (31 : Basis) (87 : Basis) where
  plus := ![v2597_pa,v2597_pb,v2597_pg]
  minus := ![(Primitive.Addresses.material2597 1).one,v2597_mb,v2597_mg]
  upper := v2597_upper
  lower := (Primitive.Addresses.material2597 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2597_pa_checked.trans (by decide +kernel)
    · exact v2597_pb_checked.trans (by decide +kernel)
    · exact v2597_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 87 Primitive.Addresses.material2597
    · exact v2597_mb_checked.trans (by decide +kernel)
    · exact v2597_mg_checked.trans (by decide +kernel)
  upper_error := v2597_upper_checked
  lower_error := reuse_lower_error 31 87 Primitive.Addresses.material2597

def v2598_pa : Scalar.QComplex := ((999998793093556149120568129233 : Int)/10^30,(-1553644563945883555050567588 : Int)/10^30)
theorem v2598_pa_checked : Scalar.distance (sourceCoefficient 31 88 1 0) v2598_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2598_pb : Scalar.QComplex := ((-670362600542303188346417 : Int)/10^30,(-431476933034672449638343808 : Int)/10^30)
theorem v2598_pb_checked : Scalar.distance (sourceCoefficient 31 88 1 1) v2598_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2598_pg : Scalar.QComplex := ((-93086310300141119058437 : Int)/10^30,(144623214522283495243 : Int)/10^30)
theorem v2598_pg_checked : Scalar.distance (sourceCoefficient 31 88 1 2) v2598_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2598_mb : Scalar.QComplex := ((-1042707511144915221586288 : Int)/10^30,(-431476193883358553569175545 : Int)/10^30)
theorem v2598_mb_checked : Scalar.distance (sourceCoefficient 31 88 3 1) v2598_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2598_mg : Scalar.QComplex := ((-93086150836532994826426 : Int)/10^30,(224952454009688114320 : Int)/10^30)
theorem v2598_mg_checked : Scalar.distance (sourceCoefficient 31 88 3 2) v2598_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2598_upper : Scalar.QComplex := ((999994622263250109430181622717 : Int)/10^30,(-3279549447672437292834224084 : Int)/10^30)
theorem v2598_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 88 5) 1) 14) v2598_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2598 : Material (31 : Basis) (88 : Basis) where
  plus := ![v2598_pa,v2598_pb,v2598_pg]
  minus := ![(Primitive.Addresses.material2598 1).one,v2598_mb,v2598_mg]
  upper := v2598_upper
  lower := (Primitive.Addresses.material2598 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2598_pa_checked.trans (by decide +kernel)
    · exact v2598_pb_checked.trans (by decide +kernel)
    · exact v2598_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 88 Primitive.Addresses.material2598
    · exact v2598_mb_checked.trans (by decide +kernel)
    · exact v2598_mg_checked.trans (by decide +kernel)
  upper_error := v2598_upper_checked
  lower_error := reuse_lower_error 31 88 Primitive.Addresses.material2598

def v2599_pa : Scalar.QComplex := ((999998767966780377566148978588 : Int)/10^30,(-1569734028852981656869237020 : Int)/10^30)
theorem v2599_pa_checked : Scalar.distance (sourceCoefficient 31 89 1 0) v2599_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2599_pb : Scalar.QComplex := ((-677304838352210749611999 : Int)/10^30,(-431476919937234227183853684 : Int)/10^30)
theorem v2599_pb_checked : Scalar.distance (sourceCoefficient 31 89 1 1) v2599_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2599_pg : Scalar.QComplex := ((-93086307717847578239622 : Int)/10^30,(146120924870818802272 : Int)/10^30)
theorem v2599_pg_checked : Scalar.distance (sourceCoefficient 31 89 1 2) v2599_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2599_mb : Scalar.QComplex := ((-1049649735067411071023313 : Int)/10^30,(-431476174795086644723514393 : Int)/10^30)
theorem v2599_mb_checked : Scalar.distance (sourceCoefficient 31 89 3 1) v2599_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2599_mg : Scalar.QComplex := ((-93086146961783839097617 : Int)/10^30,(226450161572154386302 : Int)/10^30)
theorem v2599_mg_checked : Scalar.distance (sourceCoefficient 31 89 3 2) v2599_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2599_upper : Scalar.QComplex := ((999994569367554956459760341329 : Int)/10^30,(-3295638845249631918432331316 : Int)/10^30)
theorem v2599_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 89 5) 1) 14) v2599_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2599 : Material (31 : Basis) (89 : Basis) where
  plus := ![v2599_pa,v2599_pb,v2599_pg]
  minus := ![(Primitive.Addresses.material2599 1).one,v2599_mb,v2599_mg]
  upper := v2599_upper
  lower := (Primitive.Addresses.material2599 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2599_pa_checked.trans (by decide +kernel)
    · exact v2599_pb_checked.trans (by decide +kernel)
    · exact v2599_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 89 Primitive.Addresses.material2599
    · exact v2599_mb_checked.trans (by decide +kernel)
    · exact v2599_mg_checked.trans (by decide +kernel)
  upper_error := v2599_upper_checked
  lower_error := reuse_lower_error 31 89 Primitive.Addresses.material2599

def v2600_pa : Scalar.QComplex := ((999998726491834515401104597428 : Int)/10^30,(-1595936937709679753891482765 : Int)/10^30)
theorem v2600_pa_checked : Scalar.distance (sourceCoefficient 31 90 1 0) v2600_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2600_pb : Scalar.QComplex := ((-688610796698165322168475 : Int)/10^30,(-431476898288295251864809487 : Int)/10^30)
theorem v2600_pb_checked : Scalar.distance (sourceCoefficient 31 90 1 1) v2600_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2600_pg : Scalar.QComplex := ((-93086303452212509347639 : Int)/10^30,(148560059266686563967 : Int)/10^30)
theorem v2600_pg_checked : Scalar.distance (sourceCoefficient 31 90 1 2) v2600_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2600_mb : Scalar.QComplex := ((-1060955670521581339874831 : Int)/10^30,(-431476143389622879196515007 : Int)/10^30)
theorem v2600_mb_checked : Scalar.distance (sourceCoefficient 31 90 3 1) v2600_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2600_mg : Scalar.QComplex := ((-93086140591287229397839 : Int)/10^30,(228889291378769991085 : Int)/10^30)
theorem v2600_mg_checked : Scalar.distance (sourceCoefficient 31 90 3 2) v2600_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2600_upper : Scalar.QComplex := ((999994482668827289016193473475 : Int)/10^30,(-3321841643498181302895576402 : Int)/10^30)
theorem v2600_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 90 5) 1) 14) v2600_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2600 : Material (31 : Basis) (90 : Basis) where
  plus := ![v2600_pa,v2600_pb,v2600_pg]
  minus := ![(Primitive.Addresses.material2600 1).one,v2600_mb,v2600_mg]
  upper := v2600_upper
  lower := (Primitive.Addresses.material2600 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2600_pa_checked.trans (by decide +kernel)
    · exact v2600_pb_checked.trans (by decide +kernel)
    · exact v2600_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 90 Primitive.Addresses.material2600
    · exact v2600_mb_checked.trans (by decide +kernel)
    · exact v2600_mg_checked.trans (by decide +kernel)
  upper_error := v2600_upper_checked
  lower_error := reuse_lower_error 31 90 Primitive.Addresses.material2600

def v2601_pa : Scalar.QComplex := ((999998702825151616943782514211 : Int)/10^30,(-1610697989724804107221540651 : Int)/10^30)
theorem v2601_pa_checked : Scalar.distance (sourceCoefficient 31 91 1 0) v2601_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2601_pb : Scalar.QComplex := ((-694979854272396180233974 : Int)/10^30,(-431476885918725056578500389 : Int)/10^30)
theorem v2601_pb_checked : Scalar.distance (sourceCoefficient 31 91 1 1) v2601_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2601_pg : Scalar.QComplex := ((-93086301016391061208063 : Int)/10^30,(149934112408778602934 : Int)/10^30)
theorem v2601_pg_checked : Scalar.distance (sourceCoefficient 31 91 1 2) v2601_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2601_mb : Scalar.QComplex := ((-1067324715049939008972189 : Int)/10^30,(-431476125523847454809983934 : Int)/10^30)
theorem v2601_mb_checked : Scalar.distance (sourceCoefficient 31 91 3 1) v2601_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2601_mg : Scalar.QComplex := ((-93086136969720711656720 : Int)/10^30,(230263341907235043500 : Int)/10^30)
theorem v2601_mg_checked : Scalar.distance (sourceCoefficient 31 91 3 2) v2601_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2601_upper : Scalar.QComplex := ((999994433525942973376572735443 : Int)/10^30,(-3336602632681904976634873606 : Int)/10^30)
theorem v2601_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 91 5) 1) 14) v2601_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2601 : Material (31 : Basis) (91 : Basis) where
  plus := ![v2601_pa,v2601_pb,v2601_pg]
  minus := ![(Primitive.Addresses.material2601 1).one,v2601_mb,v2601_mg]
  upper := v2601_upper
  lower := (Primitive.Addresses.material2601 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2601_pa_checked.trans (by decide +kernel)
    · exact v2601_pb_checked.trans (by decide +kernel)
    · exact v2601_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 91 Primitive.Addresses.material2601
    · exact v2601_mb_checked.trans (by decide +kernel)
    · exact v2601_mg_checked.trans (by decide +kernel)
  upper_error := v2601_upper_checked
  lower_error := reuse_lower_error 31 91 Primitive.Addresses.material2601

def v2602_pa : Scalar.QComplex := ((999998650842922475083871783308 : Int)/10^30,(-1642654052083095316546277772 : Int)/10^30)
theorem v2602_pa_checked : Scalar.distance (sourceCoefficient 31 92 1 0) v2602_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2602_pb : Scalar.QComplex := ((-708768166580516127348236 : Int)/10^30,(-431476858710524250257184394 : Int)/10^30)
theorem v2602_pb_checked : Scalar.distance (sourceCoefficient 31 92 1 1) v2602_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2602_pg : Scalar.QComplex := ((-93086295662039087671358 : Int)/10^30,(152908787060625843744 : Int)/10^30)
theorem v2602_pg_checked : Scalar.distance (sourceCoefficient 31 92 1 2) v2602_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2602_mb : Scalar.QComplex := ((-1081112998744588242790121 : Int)/10^30,(-431476086416964259971450050 : Int)/10^30)
theorem v2602_mb_checked : Scalar.distance (sourceCoefficient 31 92 3 1) v2602_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2602_mg : Scalar.QComplex := ((-93086129048360481618748 : Int)/10^30,(233238010830910359979 : Int)/10^30)
theorem v2602_mg_checked : Scalar.distance (sourceCoefficient 31 92 3 2) v2602_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2602_upper : Scalar.QComplex := ((999994326390526653861234128929 : Int)/10^30,(-3368558557728783418200933213 : Int)/10^30)
theorem v2602_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 92 5) 1) 14) v2602_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2602 : Material (31 : Basis) (92 : Basis) where
  plus := ![v2602_pa,v2602_pb,v2602_pg]
  minus := ![(Primitive.Addresses.material2602 1).one,v2602_mb,v2602_mg]
  upper := v2602_upper
  lower := (Primitive.Addresses.material2602 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2602_pa_checked.trans (by decide +kernel)
    · exact v2602_pb_checked.trans (by decide +kernel)
    · exact v2602_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 92 Primitive.Addresses.material2602
    · exact v2602_mb_checked.trans (by decide +kernel)
    · exact v2602_mg_checked.trans (by decide +kernel)
  upper_error := v2602_upper_checked
  lower_error := reuse_lower_error 31 92 Primitive.Addresses.material2602

def v2603_pa : Scalar.QComplex := ((999998587825087712250907286886 : Int)/10^30,(-1680579611425033113570759487 : Int)/10^30)
theorem v2603_pa_checked : Scalar.distance (sourceCoefficient 31 93 1 0) v2603_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2603_pb : Scalar.QComplex := ((-725132180015654644989852 : Int)/10^30,(-431476825657377319993967814 : Int)/10^30)
theorem v2603_pb_checked : Scalar.distance (sourceCoefficient 31 93 1 1) v2603_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2603_pg : Scalar.QComplex := ((-93086289163563799616360 : Int)/10^30,(156439140590929963414 : Int)/10^30)
theorem v2603_pg_checked : Scalar.distance (sourceCoefficient 31 93 1 2) v2603_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2603_mb : Scalar.QComplex := ((-1097476977563279543829019 : Int)/10^30,(-431476039242423050187001177 : Int)/10^30)
theorem v2603_mb_checked : Scalar.distance (sourceCoefficient 31 93 3 1) v2603_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2603_mg : Scalar.QComplex := ((-93086119503351517811242 : Int)/10^30,(236768357438811022061 : Int)/10^30)
theorem v2603_mg_checked : Scalar.distance (sourceCoefficient 31 93 3 2) v2603_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2603_upper : Scalar.QComplex := ((999994197916710904373081937456 : Int)/10^30,(-3406483951821989757221259554 : Int)/10^30)
theorem v2603_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 93 5) 1) 14) v2603_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2603 : Material (31 : Basis) (93 : Basis) where
  plus := ![v2603_pa,v2603_pb,v2603_pg]
  minus := ![(Primitive.Addresses.material2603 1).one,v2603_mb,v2603_mg]
  upper := v2603_upper
  lower := (Primitive.Addresses.material2603 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2603_pa_checked.trans (by decide +kernel)
    · exact v2603_pb_checked.trans (by decide +kernel)
    · exact v2603_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 93 Primitive.Addresses.material2603
    · exact v2603_mb_checked.trans (by decide +kernel)
    · exact v2603_mg_checked.trans (by decide +kernel)
  upper_error := v2603_upper_checked
  lower_error := reuse_lower_error 31 93 Primitive.Addresses.material2603

def v2604_pa : Scalar.QComplex := ((999998511534091427336314676955 : Int)/10^30,(-1725378103957091020206617950 : Int)/10^30)
theorem v2604_pa_checked : Scalar.distance (sourceCoefficient 31 94 1 0) v2604_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2604_pb : Scalar.QComplex := ((-744461706256642449639300 : Int)/10^30,(-431476785548268831782355247 : Int)/10^30)
theorem v2604_pb_checked : Scalar.distance (sourceCoefficient 31 94 1 1) v2604_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2604_pg : Scalar.QComplex := ((-93086281286190659509813 : Int)/10^30,(160609270571407930388 : Int)/10^30)
theorem v2604_pg_checked : Scalar.distance (sourceCoefficient 31 94 1 2) v2604_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2604_mb : Scalar.QComplex := ((-1116806461994647147829717 : Int)/10^30,(-431475982452818920001913682 : Int)/10^30)
theorem v2604_mb_checked : Scalar.distance (sourceCoefficient 31 94 3 1) v2604_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2604_mg : Scalar.QComplex := ((-93086108027346953340519 : Int)/10^30,(240938479068740776752 : Int)/10^30)
theorem v2604_mg_checked : Scalar.distance (sourceCoefficient 31 94 3 2) v2604_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2604_upper : Scalar.QComplex := ((999994044307694223099337897667 : Int)/10^30,(-3451282245960616915309148368 : Int)/10^30)
theorem v2604_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 94 5) 1) 14) v2604_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2604 : Material (31 : Basis) (94 : Basis) where
  plus := ![v2604_pa,v2604_pb,v2604_pg]
  minus := ![(Primitive.Addresses.material2604 1).one,v2604_mb,v2604_mg]
  upper := v2604_upper
  lower := (Primitive.Addresses.material2604 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2604_pa_checked.trans (by decide +kernel)
    · exact v2604_pb_checked.trans (by decide +kernel)
    · exact v2604_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 94 Primitive.Addresses.material2604
    · exact v2604_mb_checked.trans (by decide +kernel)
    · exact v2604_mg_checked.trans (by decide +kernel)
  upper_error := v2604_upper_checked
  lower_error := reuse_lower_error 31 94 Primitive.Addresses.material2604

def v2605_pa : Scalar.QComplex := ((999998434164213373540116182572 : Int)/10^30,(-1769652260024892316281909016 : Int)/10^30)
theorem v2605_pa_checked : Scalar.distance (sourceCoefficient 31 95 1 0) v2605_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2605_pb : Scalar.QComplex := ((-763564992155271233116153 : Int)/10^30,(-431476744774219453510682002 : Int)/10^30)
theorem v2605_pb_checked : Scalar.distance (sourceCoefficient 31 95 1 1) v2605_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2605_pg : Scalar.QComplex := ((-93086273286876124890406 : Int)/10^30,(164730591840470951675 : Int)/10^30)
theorem v2605_pg_checked : Scalar.distance (sourceCoefficient 31 95 1 2) v2605_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2605_mb : Scalar.QComplex := ((-1135909705594081309516661 : Int)/10^30,(-431475925193509373313715129 : Int)/10^30)
theorem v2605_mb_checked : Scalar.distance (sourceCoefficient 31 95 3 1) v2605_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2605_mg : Scalar.QComplex := ((-93086096471520759449628 : Int)/10^30,(245059791900199368255 : Int)/10^30)
theorem v2605_mg_checked : Scalar.distance (sourceCoefficient 31 95 3 2) v2605_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2605_upper : Scalar.QComplex := ((999993890524754549686097226104 : Int)/10^30,(-3495556202553872975758795847 : Int)/10^30)
theorem v2605_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 95 5) 1) 14) v2605_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2605 : Material (31 : Basis) (95 : Basis) where
  plus := ![v2605_pa,v2605_pb,v2605_pg]
  minus := ![(Primitive.Addresses.material2605 1).one,v2605_mb,v2605_mg]
  upper := v2605_upper
  lower := (Primitive.Addresses.material2605 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2605_pa_checked.trans (by decide +kernel)
    · exact v2605_pb_checked.trans (by decide +kernel)
    · exact v2605_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 95 Primitive.Addresses.material2605
    · exact v2605_mb_checked.trans (by decide +kernel)
    · exact v2605_mg_checked.trans (by decide +kernel)
  upper_error := v2605_upper_checked
  lower_error := reuse_lower_error 31 95 Primitive.Addresses.material2605

def v2606_pa : Scalar.QComplex := ((999998396308076135093438638444 : Int)/10^30,(-1790916322976041908072238780 : Int)/10^30)
theorem v2606_pa_checked : Scalar.distance (sourceCoefficient 31 96 1 0) v2606_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2606_pb : Scalar.QComplex := ((-772739948648037190470423 : Int)/10^30,(-431476724790318221287312653 : Int)/10^30)
theorem v2606_pb_checked : Scalar.distance (sourceCoefficient 31 96 1 1) v2606_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2606_pg : Scalar.QComplex := ((-93086269369278636023086 : Int)/10^30,(166709986609845008425 : Int)/10^30)
theorem v2606_pg_checked : Scalar.distance (sourceCoefficient 31 96 1 2) v2606_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2606_mb : Scalar.QComplex := ((-1145084641425384926479424 : Int)/10^30,(-431475897292041353453874984 : Int)/10^30)
theorem v2606_mb_checked : Scalar.distance (sourceCoefficient 31 96 3 1) v2606_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2606_mg : Scalar.QComplex := ((-93086090845796191944145 : Int)/10^30,(247039182551844098707 : Int)/10^30)
theorem v2606_mg_checked : Scalar.distance (sourceCoefficient 31 96 3 2) v2606_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2606_upper : Scalar.QComplex := ((999993815968830100546679554332 : Int)/10^30,(-3516820168498440062494772695 : Int)/10^30)
theorem v2606_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 96 5) 1) 14) v2606_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2606 : Material (31 : Basis) (96 : Basis) where
  plus := ![v2606_pa,v2606_pb,v2606_pg]
  minus := ![(Primitive.Addresses.material2606 1).one,v2606_mb,v2606_mg]
  upper := v2606_upper
  lower := (Primitive.Addresses.material2606 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2606_pa_checked.trans (by decide +kernel)
    · exact v2606_pb_checked.trans (by decide +kernel)
    · exact v2606_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 96 Primitive.Addresses.material2606
    · exact v2606_mb_checked.trans (by decide +kernel)
    · exact v2606_mg_checked.trans (by decide +kernel)
  upper_error := v2606_upper_checked
  lower_error := reuse_lower_error 31 96 Primitive.Addresses.material2606

def v2607_pa : Scalar.QComplex := ((999998262604305148080156316586 : Int)/10^30,(-1864078424090585089399986121 : Int)/10^30)
theorem v2607_pa_checked : Scalar.distance (sourceCoefficient 31 97 1 0) v2607_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2607_pb : Scalar.QComplex := ((-804307718705922968243561 : Int)/10^30,(-431476654045575606707044933 : Int)/10^30)
theorem v2607_pb_checked : Scalar.distance (sourceCoefficient 31 97 1 1) v2607_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2607_pg : Scalar.QComplex := ((-93086255515083327377310 : Int)/10^30,(173520381958614647862 : Int)/10^30)
theorem v2607_pg_checked : Scalar.distance (sourceCoefficient 31 97 1 2) v2607_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2607_mb : Scalar.QComplex := ((-1176652338679620541884669 : Int)/10^30,(-431475799305761280004261426 : Int)/10^30)
theorem v2607_mb_checked : Scalar.distance (sourceCoefficient 31 97 3 1) v2607_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2607_mg : Scalar.QComplex := ((-93086071114541584680451 : Int)/10^30,(253849563409245717785 : Int)/10^30)
theorem v2607_mg_checked : Scalar.distance (sourceCoefficient 31 97 3 2) v2607_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2607_upper : Scalar.QComplex := ((999993555994108939858844332743 : Int)/10^30,(-3589981929886048645587155604 : Int)/10^30)
theorem v2607_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 97 5) 1) 14) v2607_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2607 : Material (31 : Basis) (97 : Basis) where
  plus := ![v2607_pa,v2607_pb,v2607_pg]
  minus := ![(Primitive.Addresses.material2607 1).one,v2607_mb,v2607_mg]
  upper := v2607_upper
  lower := (Primitive.Addresses.material2607 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2607_pa_checked.trans (by decide +kernel)
    · exact v2607_pb_checked.trans (by decide +kernel)
    · exact v2607_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 97 Primitive.Addresses.material2607
    · exact v2607_mb_checked.trans (by decide +kernel)
    · exact v2607_mg_checked.trans (by decide +kernel)
  upper_error := v2607_upper_checked
  lower_error := reuse_lower_error 31 97 Primitive.Addresses.material2607

def v2608_pa : Scalar.QComplex := ((999999818145450463385229973109 : Int)/10^30,(-603082967759952870059400984 : Int)/10^30)
theorem v2608_pa_checked : Scalar.distance (sourceCoefficient 32 33 1 0) v2608_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2608_pb : Scalar.QComplex := ((-260216743884859568119394 : Int)/10^30,(-431477442531316435332250433 : Int)/10^30)
theorem v2608_pb_checked : Scalar.distance (sourceCoefficient 32 33 1 1) v2608_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2608_pg : Scalar.QComplex := ((-93086412968441599182866 : Int)/10^30,(56138840400239856194 : Int)/10^30)
theorem v2608_pg_checked : Scalar.distance (sourceCoefficient 32 33 1 2) v2608_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2608_mb : Scalar.QComplex := ((-632562246876175509213227 : Int)/10^30,(-431477057317214842090774537 : Int)/10^30)
theorem v2608_mb_checked : Scalar.distance (sourceCoefficient 32 33 3 1) v2608_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2608_mg : Scalar.QComplex := ((-93086329862824925900760 : Int)/10^30,(136468201432540202324 : Int)/10^30)
theorem v2608_mg_checked : Scalar.distance (sourceCoefficient 32 33 3 2) v2608_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2608_upper : Scalar.QComplex := ((999997287896698471844874950209 : Int)/10^30,(-2328991036382920922936913205 : Int)/10^30)
theorem v2608_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 33 5) 1) 14) v2608_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2608 : Material (32 : Basis) (33 : Basis) where
  plus := ![v2608_pa,v2608_pb,v2608_pg]
  minus := ![(Primitive.Addresses.material2608 1).one,v2608_mb,v2608_mg]
  upper := v2608_upper
  lower := (Primitive.Addresses.material2608 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2608_pa_checked.trans (by decide +kernel)
    · exact v2608_pb_checked.trans (by decide +kernel)
    · exact v2608_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 33 Primitive.Addresses.material2608
    · exact v2608_mb_checked.trans (by decide +kernel)
    · exact v2608_mg_checked.trans (by decide +kernel)
  upper_error := v2608_upper_checked
  lower_error := reuse_lower_error 32 33 Primitive.Addresses.material2608

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
