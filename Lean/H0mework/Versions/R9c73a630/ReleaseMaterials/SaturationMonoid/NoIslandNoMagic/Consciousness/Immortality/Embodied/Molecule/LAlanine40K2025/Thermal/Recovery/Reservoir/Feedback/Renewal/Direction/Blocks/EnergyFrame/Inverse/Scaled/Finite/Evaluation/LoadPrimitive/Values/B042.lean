import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B028

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v673_pa : Scalar.QComplex := ((999999999878751196197205502217 : Int)/10^30,(-15572334686580805797907177 : Int)/10^30)
theorem v673_pa_checked : Scalar.distance (sourceCoefficient 7 23 1 0) v673_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v673_pb : Scalar.QComplex := ((-6719112248534544668848 : Int)/10^30,(-431477513356423098950115462 : Int)/10^30)
theorem v673_pb_checked : Scalar.distance (sourceCoefficient 7 23 1 1) v673_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v673_pg : Scalar.QComplex := ((-93086429066754402207237 : Int)/10^30,(1449573028381922320 : Int)/10^30)
theorem v673_pg_checked : Scalar.distance (sourceCoefficient 7 23 1 2) v673_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v673_mb : Scalar.QComplex := ((-379064770747481364374013 : Int)/10^30,(-431477346899334126927183414 : Int)/10^30)
theorem v673_mb_checked : Scalar.distance (sourceCoefficient 7 23 3 1) v673_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v673_mg : Scalar.QComplex := ((-93086393155506363533572 : Int)/10^30,(81778968316114841903 : Int)/10^30)
theorem v673_mg_checked : Scalar.distance (sourceCoefficient 7 23 3 2) v673_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v673_upper : Scalar.QComplex := ((999998483619782670606479521077 : Int)/10^30,(-1741481591992813323122128429 : Int)/10^30)
theorem v673_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 23 5) 1) 14) v673_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material673 : Material (7 : Basis) (23 : Basis) where
  plus := ![v673_pa,v673_pb,v673_pg]
  minus := ![(Primitive.Addresses.material673 1).one,v673_mb,v673_mg]
  upper := v673_upper
  lower := (Primitive.Addresses.material673 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v673_pa_checked.trans (by decide +kernel)
    · exact v673_pb_checked.trans (by decide +kernel)
    · exact v673_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 23 Primitive.Addresses.material673
    · exact v673_mb_checked.trans (by decide +kernel)
    · exact v673_mg_checked.trans (by decide +kernel)
  upper_error := v673_upper_checked
  lower_error := reuse_lower_error 7 23 Primitive.Addresses.material673

def v674_pa : Scalar.QComplex := ((999999997787657148331232269890 : Int)/10^30,(-66518311001130166751288472 : Int)/10^30)
theorem v674_pa_checked : Scalar.distance (sourceCoefficient 7 24 1 0) v674_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v674_pb : Scalar.QComplex := ((-28701155256135865231976 : Int)/10^30,(-431477509886735218379578858 : Int)/10^30)
theorem v674_pb_checked : Scalar.distance (sourceCoefficient 7 24 1 1) v674_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v674_pg : Scalar.QComplex := ((-93086428595155065140011 : Int)/10^30,(6191952020975741694 : Int)/10^30)
theorem v674_pg_checked : Scalar.distance (sourceCoefficient 7 24 1 2) v674_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v674_mb : Scalar.QComplex := ((-401046802575979072220835 : Int)/10^30,(-431477324460134457185333149 : Int)/10^30)
theorem v674_mb_checked : Scalar.distance (sourceCoefficient 7 24 3 1) v674_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v674_mg : Scalar.QComplex := ((-93086388591447720276903 : Int)/10^30,(86521345135935237063 : Int)/10^30)
theorem v674_mg_checked : Scalar.distance (sourceCoefficient 7 24 3 2) v674_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v674_upper : Scalar.QComplex := ((999998393600558401135125867645 : Int)/10^30,(-1792427488820276874276259760 : Int)/10^30)
theorem v674_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 24 5) 1) 14) v674_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material674 : Material (7 : Basis) (24 : Basis) where
  plus := ![v674_pa,v674_pb,v674_pg]
  minus := ![(Primitive.Addresses.material674 1).one,v674_mb,v674_mg]
  upper := v674_upper
  lower := (Primitive.Addresses.material674 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v674_pa_checked.trans (by decide +kernel)
    · exact v674_pb_checked.trans (by decide +kernel)
    · exact v674_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 24 Primitive.Addresses.material674
    · exact v674_mb_checked.trans (by decide +kernel)
    · exact v674_mg_checked.trans (by decide +kernel)
  upper_error := v674_upper_checked
  lower_error := reuse_lower_error 7 24 Primitive.Addresses.material674

def v675_pa : Scalar.QComplex := ((999999995994637809740653928879 : Int)/10^30,(-89502650041637123958612577 : Int)/10^30)
theorem v675_pa_checked : Scalar.distance (sourceCoefficient 7 25 1 0) v675_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v675_pb : Scalar.QComplex := ((-38618380539058846802220 : Int)/10^30,(-431477507832592253559499143 : Int)/10^30)
theorem v675_pb_checked : Scalar.distance (sourceCoefficient 7 25 1 1) v675_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v675_pg : Scalar.QComplex := ((-93086428290123042378140 : Int)/10^30,(8331482048247435457 : Int)/10^30)
theorem v675_pg_checked : Scalar.distance (sourceCoefficient 7 25 1 2) v675_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v675_mb : Scalar.QComplex := ((-410964022393632977898016 : Int)/10^30,(-431477313847873493300145849 : Int)/10^30)
theorem v675_mb_checked : Scalar.distance (sourceCoefficient 7 25 3 1) v675_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v675_mg : Scalar.QComplex := ((-93086386440097758412268 : Int)/10^30,(88660874103333222809 : Int)/10^30)
theorem v675_mg_checked : Scalar.distance (sourceCoefficient 7 25 3 2) v675_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v675_upper : Scalar.QComplex := ((999998352138657672070889542840 : Int)/10^30,(-1815411790533722043808333151 : Int)/10^30)
theorem v675_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 25 5) 1) 14) v675_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material675 : Material (7 : Basis) (25 : Basis) where
  plus := ![v675_pa,v675_pb,v675_pg]
  minus := ![(Primitive.Addresses.material675 1).one,v675_mb,v675_mg]
  upper := v675_upper
  lower := (Primitive.Addresses.material675 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v675_pa_checked.trans (by decide +kernel)
    · exact v675_pb_checked.trans (by decide +kernel)
    · exact v675_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 25 Primitive.Addresses.material675
    · exact v675_mb_checked.trans (by decide +kernel)
    · exact v675_mg_checked.trans (by decide +kernel)
  upper_error := v675_upper_checked
  lower_error := reuse_lower_error 7 25 Primitive.Addresses.material675

def v676_pa : Scalar.QComplex := ((999999995310369874956734833740 : Int)/10^30,(-96846580879729045924405637 : Int)/10^30)
theorem v676_pa_checked : Scalar.distance (sourceCoefficient 7 26 1 0) v676_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v676_pb : Scalar.QComplex := ((-41787121486290373943202 : Int)/10^30,(-431477507112186455242996388 : Int)/10^30)
theorem v676_pb_checked : Scalar.distance (sourceCoefficient 7 26 1 1) v676_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v676_pg : Scalar.QComplex := ((-93086428180565282376452 : Int)/10^30,(9015102337871700221 : Int)/10^30)
theorem v676_pg_checked : Scalar.distance (sourceCoefficient 7 26 1 2) v676_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v676_mb : Scalar.QComplex := ((-414132761539319673694794 : Int)/10^30,(-431477310392987240557279169 : Int)/10^30)
theorem v676_mb_checked : Scalar.distance (sourceCoefficient 7 26 3 1) v676_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v676_mg : Scalar.QComplex := ((-93086385740606518373100 : Int)/10^30,(89344494043870998172 : Int)/10^30)
theorem v676_mg_checked : Scalar.distance (sourceCoefficient 7 26 3 2) v676_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v676_upper : Scalar.QComplex := ((999998338779432366078302338603 : Int)/10^30,(-1822755709252907282017411098 : Int)/10^30)
theorem v676_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 26 5) 1) 14) v676_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material676 : Material (7 : Basis) (26 : Basis) where
  plus := ![v676_pa,v676_pb,v676_pg]
  minus := ![(Primitive.Addresses.material676 1).one,v676_mb,v676_mg]
  upper := v676_upper
  lower := (Primitive.Addresses.material676 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v676_pa_checked.trans (by decide +kernel)
    · exact v676_pb_checked.trans (by decide +kernel)
    · exact v676_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 26 Primitive.Addresses.material676
    · exact v676_mb_checked.trans (by decide +kernel)
    · exact v676_mg_checked.trans (by decide +kernel)
  upper_error := v676_upper_checked
  lower_error := reuse_lower_error 7 26 Primitive.Addresses.material676

def v677_pa : Scalar.QComplex := ((999999994809029072268540031108 : Int)/10^30,(-101891814335189560237288231 : Int)/10^30)
theorem v677_pa_checked : Scalar.distance (sourceCoefficient 7 27 1 0) v677_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v677_pb : Scalar.QComplex := ((-43964026220441597636826 : Int)/10^30,(-431477506599292264746527054 : Int)/10^30)
theorem v677_pb_checked : Scalar.distance (sourceCoefficient 7 27 1 1) v677_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v677_pg : Scalar.QComplex := ((-93086428101905688716349 : Int)/10^30,(9484745098520382443 : Int)/10^30)
theorem v677_pg_checked : Scalar.distance (sourceCoefficient 7 27 1 2) v677_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v677_mb : Scalar.QComplex := ((-416309665020305188901066 : Int)/10^30,(-431477308001522499611907588 : Int)/10^30)
theorem v677_mb_checked : Scalar.distance (sourceCoefficient 7 27 3 1) v677_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v677_mg : Scalar.QComplex := ((-93086385256666403486489 : Int)/10^30,(89814136561770530238 : Int)/10^30)
theorem v677_mg_checked : Scalar.distance (sourceCoefficient 7 27 3 2) v677_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v677_upper : Scalar.QComplex := ((999998329570477065957216966977 : Int)/10^30,(-1827800934328816475017777149 : Int)/10^30)
theorem v677_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 27 5) 1) 14) v677_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material677 : Material (7 : Basis) (27 : Basis) where
  plus := ![v677_pa,v677_pb,v677_pg]
  minus := ![(Primitive.Addresses.material677 1).one,v677_mb,v677_mg]
  upper := v677_upper
  lower := (Primitive.Addresses.material677 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v677_pa_checked.trans (by decide +kernel)
    · exact v677_pb_checked.trans (by decide +kernel)
    · exact v677_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 27 Primitive.Addresses.material677
    · exact v677_mb_checked.trans (by decide +kernel)
    · exact v677_mg_checked.trans (by decide +kernel)
  upper_error := v677_upper_checked
  lower_error := reuse_lower_error 7 27 Primitive.Addresses.material677

def v678_pa : Scalar.QComplex := ((999999994093415960264551955248 : Int)/10^30,(-108688398850029808832473816 : Int)/10^30)
theorem v678_pa_checked : Scalar.distance (sourceCoefficient 7 28 1 0) v678_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v678_pb : Scalar.QComplex := ((-46896599531466045525568 : Int)/10^30,(-431477505885205865045795893 : Int)/10^30)
theorem v678_pb_checked : Scalar.distance (sourceCoefficient 7 28 1 1) v678_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v678_pg : Scalar.QComplex := ((-93086427991570693014883 : Int)/10^30,(10117414872831775929 : Int)/10^30)
theorem v678_pg_checked : Scalar.distance (sourceCoefficient 7 28 1 2) v678_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v678_mb : Scalar.QComplex := ((-419242236623174166189942 : Int)/10^30,(-431477304756757676583035198 : Int)/10^30)
theorem v678_mb_checked : Scalar.distance (sourceCoefficient 7 28 3 1) v678_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v678_mg : Scalar.QComplex := ((-93086384600365928025925 : Int)/10^30,(90446806005295920325 : Int)/10^30)
theorem v678_mg_checked : Scalar.distance (sourceCoefficient 7 28 3 2) v678_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v678_upper : Scalar.QComplex := ((999998317124576728491345596472 : Int)/10^30,(-1834597507485859160254376518 : Int)/10^30)
theorem v678_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 28 5) 1) 14) v678_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material678 : Material (7 : Basis) (28 : Basis) where
  plus := ![v678_pa,v678_pb,v678_pg]
  minus := ![(Primitive.Addresses.material678 1).one,v678_mb,v678_mg]
  upper := v678_upper
  lower := (Primitive.Addresses.material678 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v678_pa_checked.trans (by decide +kernel)
    · exact v678_pb_checked.trans (by decide +kernel)
    · exact v678_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 28 Primitive.Addresses.material678
    · exact v678_mb_checked.trans (by decide +kernel)
    · exact v678_mg_checked.trans (by decide +kernel)
  upper_error := v678_upper_checked
  lower_error := reuse_lower_error 7 28 Primitive.Addresses.material678

def v679_pa : Scalar.QComplex := ((999999992502538802919032111448 : Int)/10^30,(-122453755916060048694315670 : Int)/10^30)
theorem v679_pa_checked : Scalar.distance (sourceCoefficient 7 29 1 0) v679_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v679_pb : Scalar.QComplex := ((-52836041398003200114071 : Int)/10^30,(-431477504357524408074890294 : Int)/10^30)
theorem v679_pb_checked : Scalar.distance (sourceCoefficient 7 29 1 1) v679_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v679_pg : Scalar.QComplex := ((-93086427752736096169361 : Int)/10^30,(11398782788593435691 : Int)/10^30)
theorem v679_pg_checked : Scalar.distance (sourceCoefficient 7 29 1 2) v679_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v679_mb : Scalar.QComplex := ((-425181674959865374816459 : Int)/10^30,(-431477298103605960147698203 : Int)/10^30)
theorem v679_mb_checked : Scalar.distance (sourceCoefficient 7 29 3 1) v679_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v679_mg : Scalar.QComplex := ((-93086383255768619475732 : Int)/10^30,(91728173237842243275 : Int)/10^30)
theorem v679_mg_checked : Scalar.distance (sourceCoefficient 7 29 3 2) v679_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v679_upper : Scalar.QComplex := ((999998291775944428040349440672 : Int)/10^30,(-1848362841304297392362630668 : Int)/10^30)
theorem v679_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 29 5) 1) 14) v679_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material679 : Material (7 : Basis) (29 : Basis) where
  plus := ![v679_pa,v679_pb,v679_pg]
  minus := ![(Primitive.Addresses.material679 1).one,v679_mb,v679_mg]
  upper := v679_upper
  lower := (Primitive.Addresses.material679 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v679_pa_checked.trans (by decide +kernel)
    · exact v679_pb_checked.trans (by decide +kernel)
    · exact v679_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 29 Primitive.Addresses.material679
    · exact v679_mb_checked.trans (by decide +kernel)
    · exact v679_mg_checked.trans (by decide +kernel)
  upper_error := v679_upper_checked
  lower_error := reuse_lower_error 7 29 Primitive.Addresses.material679

def v680_pa : Scalar.QComplex := ((999999991850178687988622456405 : Int)/10^30,(-127670053487899689488765353 : Int)/10^30)
theorem v680_pa_checked : Scalar.distance (sourceCoefficient 7 30 1 0) v680_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v680_pb : Scalar.QComplex := ((-55086756431552697897963 : Int)/10^30,(-431477503750137365584360798 : Int)/10^30)
theorem v680_pb_checked : Scalar.distance (sourceCoefficient 7 30 1 1) v680_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v680_pg : Scalar.QComplex := ((-93086427656854692327566 : Int)/10^30,(11884349294803466694 : Int)/10^30)
theorem v680_pg_checked : Scalar.distance (sourceCoefficient 7 30 1 2) v680_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v680_mb : Scalar.QComplex := ((-427432388631223140878893 : Int)/10^30,(-431477295553953438304044616 : Int)/10^30)
theorem v680_mb_checked : Scalar.distance (sourceCoefficient 7 30 3 1) v680_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v680_mg : Scalar.QComplex := ((-93086382740865225579329 : Int)/10^30,(92213739480512339353 : Int)/10^30)
theorem v680_mg_checked : Scalar.distance (sourceCoefficient 7 30 3 2) v680_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v680_upper : Scalar.QComplex := ((999998282120728894547614100714 : Int)/10^30,(-1853579129981160172535456055 : Int)/10^30)
theorem v680_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 30 5) 1) 14) v680_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material680 : Material (7 : Basis) (30 : Basis) where
  plus := ![v680_pa,v680_pb,v680_pg]
  minus := ![(Primitive.Addresses.material680 1).one,v680_mb,v680_mg]
  upper := v680_upper
  lower := (Primitive.Addresses.material680 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v680_pa_checked.trans (by decide +kernel)
    · exact v680_pb_checked.trans (by decide +kernel)
    · exact v680_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 30 Primitive.Addresses.material680
    · exact v680_mb_checked.trans (by decide +kernel)
    · exact v680_mg_checked.trans (by decide +kernel)
  upper_error := v680_upper_checked
  lower_error := reuse_lower_error 7 30 Primitive.Addresses.material680

def v681_pa : Scalar.QComplex := ((999999990372120289997205618486 : Int)/10^30,(-138765122877866976840527297 : Int)/10^30)
theorem v681_pa_checked : Scalar.distance (sourceCoefficient 7 31 1 0) v681_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v681_pb : Scalar.QComplex := ((-59874029216886807746436 : Int)/10^30,(-431477502406166630841535563 : Int)/10^30)
theorem v681_pb_checked : Scalar.distance (sourceCoefficient 7 31 1 1) v681_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v681_pg : Scalar.QComplex := ((-93086427443087805836542 : Int)/10^30,(12917149666766491266 : Int)/10^30)
theorem v681_pg_checked : Scalar.distance (sourceCoefficient 7 31 1 2) v681_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v681_mb : Scalar.QComplex := ((-432219658474250589684631 : Int)/10^30,(-431477290078782401002013346 : Int)/10^30)
theorem v681_mb_checked : Scalar.distance (sourceCoefficient 7 31 3 1) v681_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v681_mg : Scalar.QComplex := ((-93086381635838213281409 : Int)/10^30,(93246539283445388795 : Int)/10^30)
theorem v681_mg_checked : Scalar.distance (sourceCoefficient 7 31 3 2) v681_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v681_upper : Scalar.QComplex := ((999998261493589467699441752088 : Int)/10^30,(-1864674180295330215411852599 : Int)/10^30)
theorem v681_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 31 5) 1) 14) v681_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material681 : Material (7 : Basis) (31 : Basis) where
  plus := ![v681_pa,v681_pb,v681_pg]
  minus := ![(Primitive.Addresses.material681 1).one,v681_mb,v681_mg]
  upper := v681_upper
  lower := (Primitive.Addresses.material681 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v681_pa_checked.trans (by decide +kernel)
    · exact v681_pb_checked.trans (by decide +kernel)
    · exact v681_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 31 Primitive.Addresses.material681
    · exact v681_mb_checked.trans (by decide +kernel)
    · exact v681_mg_checked.trans (by decide +kernel)
  upper_error := v681_upper_checked
  lower_error := reuse_lower_error 7 31 Primitive.Addresses.material681

def v682_pa : Scalar.QComplex := ((999999989697960046935409782889 : Int)/10^30,(-143541212897192537411237114 : Int)/10^30)
theorem v682_pa_checked : Scalar.distance (sourceCoefficient 7 32 1 0) v682_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v682_pb : Scalar.QComplex := ((-61934804585113319425659 : Int)/10^30,(-431477501805823497042403441 : Int)/10^30)
theorem v682_pb_checked : Scalar.distance (sourceCoefficient 7 32 1 1) v682_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v682_pg : Scalar.QComplex := ((-93086427346951576024468 : Int)/10^30,(13361738823300988878 : Int)/10^30)
theorem v682_pg_checked : Scalar.distance (sourceCoefficient 7 32 1 2) v682_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v682_mb : Scalar.QComplex := ((-434280432557087163668486 : Int)/10^30,(-431477287700083161835759243 : Int)/10^30)
theorem v682_mb_checked : Scalar.distance (sourceCoefficient 7 32 3 1) v682_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v682_mg : Scalar.QComplex := ((-93086381156041600728277 : Int)/10^30,(93691128191477788189 : Int)/10^30)
theorem v682_mg_checked : Scalar.distance (sourceCoefficient 7 32 3 2) v682_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v682_upper : Scalar.QComplex := ((999998252576332138866146227441 : Int)/10^30,(-1869450262037691310956486664 : Int)/10^30)
theorem v682_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 32 5) 1) 14) v682_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material682 : Material (7 : Basis) (32 : Basis) where
  plus := ![v682_pa,v682_pb,v682_pg]
  minus := ![(Primitive.Addresses.material682 1).one,v682_mb,v682_mg]
  upper := v682_upper
  lower := (Primitive.Addresses.material682 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v682_pa_checked.trans (by decide +kernel)
    · exact v682_pb_checked.trans (by decide +kernel)
    · exact v682_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 32 Primitive.Addresses.material682
    · exact v682_mb_checked.trans (by decide +kernel)
    · exact v682_mg_checked.trans (by decide +kernel)
  upper_error := v682_upper_checked
  lower_error := reuse_lower_error 7 32 Primitive.Addresses.material682

def v683_pa : Scalar.QComplex := ((999999988720380904515897404525 : Int)/10^30,(-150197330414819285002153576 : Int)/10^30)
theorem v683_pa_checked : Scalar.distance (sourceCoefficient 7 33 1 0) v683_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v683_pb : Scalar.QComplex := ((-64806769507334307454523 : Int)/10^30,(-431477500947276786914204901 : Int)/10^30)
theorem v683_pb_checked : Scalar.distance (sourceCoefficient 7 33 1 1) v683_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v683_pg : Scalar.QComplex := ((-93086427208840994133604 : Int)/10^30,(13981333022325425831 : Int)/10^30)
theorem v683_pg_checked : Scalar.distance (sourceCoefficient 7 33 1 2) v683_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v683_mb : Scalar.QComplex := ((-437152395669057212541172 : Int)/10^30,(-431477284363160392005480606 : Int)/10^30)
theorem v683_mb_checked : Scalar.distance (sourceCoefficient 7 33 3 1) v683_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v683_mg : Scalar.QComplex := ((-93086380483249181991029 : Int)/10^30,(94310722040615776089 : Int)/10^30)
theorem v683_mg_checked : Scalar.distance (sourceCoefficient 7 33 3 2) v683_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v683_upper : Scalar.QComplex := ((999998240110899455276439063595 : Int)/10^30,(-1876106367954599984001182639 : Int)/10^30)
theorem v683_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 33 5) 1) 14) v683_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material683 : Material (7 : Basis) (33 : Basis) where
  plus := ![v683_pa,v683_pb,v683_pg]
  minus := ![(Primitive.Addresses.material683 1).one,v683_mb,v683_mg]
  upper := v683_upper
  lower := (Primitive.Addresses.material683 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v683_pa_checked.trans (by decide +kernel)
    · exact v683_pb_checked.trans (by decide +kernel)
    · exact v683_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 33 Primitive.Addresses.material683
    · exact v683_mb_checked.trans (by decide +kernel)
    · exact v683_mg_checked.trans (by decide +kernel)
  upper_error := v683_upper_checked
  lower_error := reuse_lower_error 7 33 Primitive.Addresses.material683

def v684_pa : Scalar.QComplex := ((999999986161460506458450205419 : Int)/10^30,(-166364295434981854386616027 : Int)/10^30)
theorem v684_pa_checked : Scalar.distance (sourceCoefficient 7 34 1 0) v684_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v684_pb : Scalar.QComplex := ((-71782451069925393436587 : Int)/10^30,(-431477498755825141610481964 : Int)/10^30)
theorem v684_pb_checked : Scalar.distance (sourceCoefficient 7 34 1 1) v684_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v684_pg : Scalar.QComplex := ((-93086426853350070417873 : Int)/10^30,(15486258032324752812 : Int)/10^30)
theorem v684_pg_checked : Scalar.distance (sourceCoefficient 7 34 1 2) v684_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v684_mb : Scalar.QComplex := ((-444128072743159177795008 : Int)/10^30,(-431477276152010547198180139 : Int)/10^30)
theorem v684_mb_checked : Scalar.distance (sourceCoefficient 7 34 3 1) v684_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v684_mg : Scalar.QComplex := ((-93086378829075886317761 : Int)/10^30,(95815646183490086926 : Int)/10^30)
theorem v684_mg_checked : Scalar.distance (sourceCoefficient 7 34 3 2) v684_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v684_upper : Scalar.QComplex := ((999998209649267899239482368472 : Int)/10^30,(-1892273304479502797367577425 : Int)/10^30)
theorem v684_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 34 5) 1) 14) v684_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material684 : Material (7 : Basis) (34 : Basis) where
  plus := ![v684_pa,v684_pb,v684_pg]
  minus := ![(Primitive.Addresses.material684 1).one,v684_mb,v684_mg]
  upper := v684_upper
  lower := (Primitive.Addresses.material684 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v684_pa_checked.trans (by decide +kernel)
    · exact v684_pb_checked.trans (by decide +kernel)
    · exact v684_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 34 Primitive.Addresses.material684
    · exact v684_mb_checked.trans (by decide +kernel)
    · exact v684_mg_checked.trans (by decide +kernel)
  upper_error := v684_upper_checked
  lower_error := reuse_lower_error 7 34 Primitive.Addresses.material684

def v685_pa : Scalar.QComplex := ((999999976297607400206753943444 : Int)/10^30,(-217726398578084869672523842 : Int)/10^30)
theorem v685_pa_checked : Scalar.distance (sourceCoefficient 7 35 1 0) v685_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v685_pb : Scalar.QComplex := ((-93944042365204929954371 : Int)/10^30,(-431477490795928872020755615 : Int)/10^30)
theorem v685_pb_checked : Scalar.distance (sourceCoefficient 7 35 1 1) v685_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v685_pg : Scalar.QComplex := ((-93086425535625518016050 : Int)/10^30,(20267372668764042850 : Int)/10^30)
theorem v685_pg_checked : Scalar.distance (sourceCoefficient 7 35 1 2) v685_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v685_mb : Scalar.QComplex := ((-466289648917633460086861 : Int)/10^30,(-431477249067662074635325660 : Int)/10^30)
theorem v685_mb_checked : Scalar.distance (sourceCoefficient 7 35 3 1) v685_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v685_mg : Scalar.QComplex := ((-93086373385465226727578 : Int)/10^30,(100596757902564949473 : Int)/10^30)
theorem v685_mg_checked : Scalar.distance (sourceCoefficient 7 35 3 2) v685_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v685_upper : Scalar.QComplex := ((999998111139098992641357215778 : Int)/10^30,(-1943635314100670977834374281 : Int)/10^30)
theorem v685_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 35 5) 1) 14) v685_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material685 : Material (7 : Basis) (35 : Basis) where
  plus := ![v685_pa,v685_pb,v685_pg]
  minus := ![(Primitive.Addresses.material685 1).one,v685_mb,v685_mg]
  upper := v685_upper
  lower := (Primitive.Addresses.material685 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v685_pa_checked.trans (by decide +kernel)
    · exact v685_pb_checked.trans (by decide +kernel)
    · exact v685_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 35 Primitive.Addresses.material685
    · exact v685_mb_checked.trans (by decide +kernel)
    · exact v685_mg_checked.trans (by decide +kernel)
  upper_error := v685_upper_checked
  lower_error := reuse_lower_error 7 35 Primitive.Addresses.material685

def v686_pa : Scalar.QComplex := ((999999972652101883274687965894 : Int)/10^30,(-233871322494963226873185575 : Int)/10^30)
theorem v686_pa_checked : Scalar.distance (sourceCoefficient 7 36 1 0) v686_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v686_pb : Scalar.QComplex := ((-100910213500449386639407 : Int)/10^30,(-431477487980341852765648361 : Int)/10^30)
theorem v686_pb_checked : Scalar.distance (sourceCoefficient 7 36 1 1) v686_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v686_pg : Scalar.QComplex := ((-93086425062236330170128 : Int)/10^30,(21770245931003967837 : Int)/10^30)
theorem v686_pg_checked : Scalar.distance (sourceCoefficient 7 36 1 2) v686_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v686_mb : Scalar.QComplex := ((-473255815029329245086527 : Int)/10^30,(-431477240240584158737158882 : Int)/10^30)
theorem v686_mb_checked : Scalar.distance (sourceCoefficient 7 36 3 1) v686_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v686_mg : Scalar.QComplex := ((-93086371615164276732105 : Int)/10^30,(102099630196702925774 : Int)/10^30)
theorem v686_mg_checked : Scalar.distance (sourceCoefficient 7 36 3 2) v686_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v686_upper : Scalar.QComplex := ((999998079628924880785956990201 : Int)/10^30,(-1959780207679769872283306831 : Int)/10^30)
theorem v686_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 36 5) 1) 14) v686_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material686 : Material (7 : Basis) (36 : Basis) where
  plus := ![v686_pa,v686_pb,v686_pg]
  minus := ![(Primitive.Addresses.material686 1).one,v686_mb,v686_mg]
  upper := v686_upper
  lower := (Primitive.Addresses.material686 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v686_pa_checked.trans (by decide +kernel)
    · exact v686_pb_checked.trans (by decide +kernel)
    · exact v686_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 36 Primitive.Addresses.material686
    · exact v686_mb_checked.trans (by decide +kernel)
    · exact v686_mg_checked.trans (by decide +kernel)
  upper_error := v686_upper_checked
  lower_error := reuse_lower_error 7 36 Primitive.Addresses.material686

def v687_pa : Scalar.QComplex := ((999999971016015686239941835927 : Int)/10^30,(-240765379129659689591509749 : Int)/10^30)
theorem v687_pa_checked : Scalar.distance (sourceCoefficient 7 37 1 0) v687_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v687_pb : Scalar.QComplex := ((-103884843690027856433308 : Int)/10^30,(-431477486732367528176389723 : Int)/10^30)
theorem v687_pb_checked : Scalar.distance (sourceCoefficient 7 37 1 1) v687_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v687_pg : Scalar.QComplex := ((-93086424851469395361975 : Int)/10^30,(22411989020777342851 : Int)/10^30)
theorem v687_pg_checked : Scalar.distance (sourceCoefficient 7 37 1 2) v687_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v687_mb : Scalar.QComplex := ((-476230443034371312541326 : Int)/10^30,(-431477236425638417590007552 : Int)/10^30)
theorem v687_mb_checked : Scalar.distance (sourceCoefficient 7 37 3 1) v687_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v687_mg : Scalar.QComplex := ((-93086370850602036963524 : Int)/10^30,(102741372865643647208 : Int)/10^30)
theorem v687_mg_checked : Scalar.distance (sourceCoefficient 7 37 3 2) v687_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v687_upper : Scalar.QComplex := ((999998066094324792955674520783 : Int)/10^30,(-1966674251222842458899605265 : Int)/10^30)
theorem v687_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 37 5) 1) 14) v687_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material687 : Material (7 : Basis) (37 : Basis) where
  plus := ![v687_pa,v687_pb,v687_pg]
  minus := ![(Primitive.Addresses.material687 1).one,v687_mb,v687_mg]
  upper := v687_upper
  lower := (Primitive.Addresses.material687 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v687_pa_checked.trans (by decide +kernel)
    · exact v687_pb_checked.trans (by decide +kernel)
    · exact v687_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 37 Primitive.Addresses.material687
    · exact v687_mb_checked.trans (by decide +kernel)
    · exact v687_mg_checked.trans (by decide +kernel)
  upper_error := v687_upper_checked
  lower_error := reuse_lower_error 7 37 Primitive.Addresses.material687

def v688_pa : Scalar.QComplex := ((999999965134469067289976471513 : Int)/10^30,(-264066394396967521129612837 : Int)/10^30)
theorem v688_pa_checked : Scalar.distance (sourceCoefficient 7 38 1 0) v688_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v688_pb : Scalar.QComplex := ((-113938706990142508769146 : Int)/10^30,(-431477482311991768232009934 : Int)/10^30)
theorem v688_pb_checked : Scalar.distance (sourceCoefficient 7 38 1 1) v688_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v688_pg : Scalar.QComplex := ((-93086424100900090708957 : Int)/10^30,(24580997236661185646 : Int)/10^30)
theorem v688_pg_checked : Scalar.distance (sourceCoefficient 7 38 1 2) v688_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v688_mb : Scalar.QComplex := ((-486284298776387979494476 : Int)/10^30,(-431477223329233084748569143 : Int)/10^30)
theorem v688_mb_checked : Scalar.distance (sourceCoefficient 7 38 3 1) v688_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v688_mg : Scalar.QComplex := ((-93086368228276609977681 : Int)/10^30,(104910379626199097127 : Int)/10^30)
theorem v688_mg_checked : Scalar.distance (sourceCoefficient 7 38 3 2) v688_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v688_upper : Scalar.QComplex := ((999998019997348434097733554052 : Int)/10^30,(-1989975221635009284742466458 : Int)/10^30)
theorem v688_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 38 5) 1) 14) v688_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material688 : Material (7 : Basis) (38 : Basis) where
  plus := ![v688_pa,v688_pb,v688_pg]
  minus := ![(Primitive.Addresses.material688 1).one,v688_mb,v688_mg]
  upper := v688_upper
  lower := (Primitive.Addresses.material688 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v688_pa_checked.trans (by decide +kernel)
    · exact v688_pb_checked.trans (by decide +kernel)
    · exact v688_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 38 Primitive.Addresses.material688
    · exact v688_mb_checked.trans (by decide +kernel)
    · exact v688_mg_checked.trans (by decide +kernel)
  upper_error := v688_upper_checked
  lower_error := reuse_lower_error 7 38 Primitive.Addresses.material688

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
