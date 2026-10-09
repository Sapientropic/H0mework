import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B023
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B024

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v561_pa : Scalar.QComplex := ((999996356425438115886499551322 : Int)/10^30,(2699469549399036838834977755 : Int)/10^30)
theorem v561_pa_checked : Scalar.distance (sourceCoefficient 5 92 1 0) v561_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v561_pb : Scalar.QComplex := ((1164754772849724510841161 : Int)/10^30,(-431473853534729892936307865 : Int)/10^30)
theorem v561_pb_checked : Scalar.distance (sourceCoefficient 5 92 1 1) v561_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v561_pg : Scalar.QComplex := ((-93085864705899785409727 : Int)/10^30,(-251283372822760042002 : Int)/10^30)
theorem v561_pg_checked : Scalar.distance (sourceCoefficient 5 92 1 2) v561_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v561_mb : Scalar.QComplex := ((792411836418800254213491 : Int)/10^30,(-431474698008205254393353574 : Int)/10^30)
theorem v561_mb_checked : Scalar.distance (sourceCoefficient 5 92 3 1) v561_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v561_mg : Scalar.QComplex := ((-93086046892011484273729 : Int)/10^30,(-170954370449000580769 : Int)/10^30)
theorem v561_mg_checked : Scalar.distance (sourceCoefficient 5 92 3 2) v561_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v561_upper : Scalar.QComplex := ((999999526087881342109485368070 : Int)/10^30,(973562536626736073408521071 : Int)/10^30)
theorem v561_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 92 5) 1) 14) v561_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material561 : Material (5 : Basis) (92 : Basis) where
  plus := ![v561_pa,v561_pb,v561_pg]
  minus := ![(Primitive.Addresses.material561 1).one,v561_mb,v561_mg]
  upper := v561_upper
  lower := (Primitive.Addresses.material561 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v561_pa_checked.trans (by decide +kernel)
    · exact v561_pb_checked.trans (by decide +kernel)
    · exact v561_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 92 Primitive.Addresses.material561
    · exact v561_mb_checked.trans (by decide +kernel)
    · exact v561_mg_checked.trans (by decide +kernel)
  upper_error := v561_upper_checked
  lower_error := reuse_lower_error 5 92 Primitive.Addresses.material561

def v562_pa : Scalar.QComplex := ((999996458085298626858483145908 : Int)/10^30,(2661544073951534478048922383 : Int)/10^30)
theorem v562_pa_checked : Scalar.distance (sourceCoefficient 5 93 1 0) v562_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v562_pb : Scalar.QComplex := ((1148390783546883668452677 : Int)/10^30,(-431473867851341134145680609 : Int)/10^30)
theorem v562_pb_checked : Scalar.distance (sourceCoefficient 5 93 1 1) v562_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v562_pg : Scalar.QComplex := ((-93085870981797490795390 : Int)/10^30,(-247753025800304609949 : Int)/10^30)
theorem v562_pg_checked : Scalar.distance (sourceCoefficient 5 93 1 2) v562_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v562_mb : Scalar.QComplex := ((776047840854429795600035 : Int)/10^30,(-431474698203425403241637291 : Int)/10^30)
theorem v562_mb_checked : Scalar.distance (sourceCoefficient 5 93 3 1) v562_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v562_mg : Scalar.QComplex := ((-93086050121376373404315 : Int)/10^30,(-167424019325237626199 : Int)/10^30)
theorem v562_mg_checked : Scalar.distance (sourceCoefficient 5 93 3 2) v562_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v562_upper : Scalar.QComplex := ((999999562291660392528291109446 : Int)/10^30,(935636942209077620947339888 : Int)/10^30)
theorem v562_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 93 5) 1) 14) v562_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material562 : Material (5 : Basis) (93 : Basis) where
  plus := ![v562_pa,v562_pb,v562_pg]
  minus := ![(Primitive.Addresses.material562 1).one,v562_mb,v562_mg]
  upper := v562_upper
  lower := (Primitive.Addresses.material562 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v562_pa_checked.trans (by decide +kernel)
    · exact v562_pb_checked.trans (by decide +kernel)
    · exact v562_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 93 Primitive.Addresses.material562
    · exact v562_mb_checked.trans (by decide +kernel)
    · exact v562_mg_checked.trans (by decide +kernel)
  upper_error := v562_upper_checked
  lower_error := reuse_lower_error 5 93 Primitive.Addresses.material562

def v563_pa : Scalar.QComplex := ((999996576315181991659194192495 : Int)/10^30,(2616745672471619575604457069 : Int)/10^30)
theorem v563_pa_checked : Scalar.distance (sourceCoefficient 5 94 1 0) v563_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v563_pb : Scalar.QComplex := ((1129061283497107456976338 : Int)/10^30,(-431473883696421001285980908 : Int)/10^30)
theorem v563_pb_checked : Scalar.distance (sourceCoefficient 5 94 1 1) v563_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v563_pg : Scalar.QComplex := ((-93085878193791658334650 : Int)/10^30,(-243582902882911148208 : Int)/10^30)
theorem v563_pg_checked : Scalar.distance (sourceCoefficient 5 94 1 2) v563_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v563_mb : Scalar.QComplex := ((756718334328319565012316 : Int)/10^30,(-431474697368011395942901755 : Int)/10^30)
theorem v563_mb_checked : Scalar.distance (sourceCoefficient 5 94 3 1) v563_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v563_mg : Scalar.QComplex := ((-93086053734739593242150 : Int)/10^30,(-163253891736945360209 : Int)/10^30)
theorem v563_mg_checked : Scalar.distance (sourceCoefficient 5 94 3 2) v563_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v563_upper : Scalar.QComplex := ((999999603203390792708279471818 : Int)/10^30,(890838403397066376523575430 : Int)/10^30)
theorem v563_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 94 5) 1) 14) v563_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material563 : Material (5 : Basis) (94 : Basis) where
  plus := ![v563_pa,v563_pb,v563_pg]
  minus := ![(Primitive.Addresses.material563 1).one,v563_mb,v563_mg]
  upper := v563_upper
  lower := (Primitive.Addresses.material563 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v563_pa_checked.trans (by decide +kernel)
    · exact v563_pb_checked.trans (by decide +kernel)
    · exact v563_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 94 Primitive.Addresses.material563
    · exact v563_mb_checked.trans (by decide +kernel)
    · exact v563_mg_checked.trans (by decide +kernel)
  upper_error := v563_upper_checked
  lower_error := reuse_lower_error 5 94 Primitive.Addresses.material563

def v564_pa : Scalar.QComplex := ((999996691189465069514467664104 : Int)/10^30,(2572471597828402652334458875 : Int)/10^30)
theorem v564_pa_checked : Scalar.distance (sourceCoefficient 5 95 1 0) v564_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v564_pb : Scalar.QComplex := ((1109958021020309502445888 : Int)/10^30,(-431473898221657254765246426 : Int)/10^30)
theorem v564_pb_checked : Scalar.distance (sourceCoefficient 5 95 1 1) v564_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v564_pg : Scalar.QComplex := ((-93085885107234633260228 : Int)/10^30,(-239461587930103841705 : Int)/10^30)
theorem v564_pg_checked : Scalar.distance (sourceCoefficient 5 95 1 2) v564_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v564_mb : Scalar.QComplex := ((737615066429914598422572 : Int)/10^30,(-431474695407987102539424339 : Int)/10^30)
theorem v564_mb_checked : Scalar.distance (sourceCoefficient 5 95 3 1) v564_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v564_mg : Scalar.QComplex := ((-93086057091670806839285 : Int)/10^30,(-159132572352702046586 : Int)/10^30)
theorem v564_mg_checked : Scalar.distance (sourceCoefficient 5 95 3 2) v564_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v564_upper : Scalar.QComplex := ((999999641664466457296937548010 : Int)/10^30,(846564196432291557357235576 : Int)/10^30)
theorem v564_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 95 5) 1) 14) v564_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material564 : Material (5 : Basis) (95 : Basis) where
  plus := ![v564_pa,v564_pb,v564_pg]
  minus := ![(Primitive.Addresses.material564 1).one,v564_mb,v564_mg]
  upper := v564_upper
  lower := (Primitive.Addresses.material564 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v564_pa_checked.trans (by decide +kernel)
    · exact v564_pb_checked.trans (by decide +kernel)
    · exact v564_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 95 Primitive.Addresses.material564
    · exact v564_mb_checked.trans (by decide +kernel)
    · exact v564_mg_checked.trans (by decide +kernel)
  upper_error := v564_upper_checked
  lower_error := reuse_lower_error 5 95 Primitive.Addresses.material564

def v565_pa : Scalar.QComplex := ((999996745664669593137427781644 : Int)/10^30,(2551207570958365278991168534 : Int)/10^30)
theorem v565_pa_checked : Scalar.distance (sourceCoefficient 5 96 1 0) v565_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v565_pb : Scalar.QComplex := ((1100783074906294592805379 : Int)/10^30,(-431473904796987256587216600 : Int)/10^30)
theorem v565_pb_checked : Scalar.distance (sourceCoefficient 5 96 1 1) v565_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v565_pg : Scalar.QComplex := ((-93085888351960743745610 : Int)/10^30,(-237482195959608011105 : Int)/10^30)
theorem v565_pg_checked : Scalar.distance (sourceCoefficient 5 96 1 2) v565_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v565_mb : Scalar.QComplex := ((728440118057937793079461 : Int)/10^30,(-431474694065749383904031032 : Int)/10^30)
theorem v565_mb_checked : Scalar.distance (sourceCoefficient 5 96 3 1) v565_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v565_mg : Scalar.QComplex := ((-93086058628269587131946 : Int)/10^30,(-157153178319171812974 : Int)/10^30)
theorem v565_mg_checked : Scalar.distance (sourceCoefficient 5 96 3 2) v565_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v565_upper : Scalar.QComplex := ((999999659439808526266040336972 : Int)/10^30,(825300107213263303050945904 : Int)/10^30)
theorem v565_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 96 5) 1) 14) v565_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material565 : Material (5 : Basis) (96 : Basis) where
  plus := ![v565_pa,v565_pb,v565_pg]
  minus := ![(Primitive.Addresses.material565 1).one,v565_mb,v565_mg]
  upper := v565_upper
  lower := (Primitive.Addresses.material565 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v565_pa_checked.trans (by decide +kernel)
    · exact v565_pb_checked.trans (by decide +kernel)
    · exact v565_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 96 Primitive.Addresses.material565
    · exact v565_mb_checked.trans (by decide +kernel)
    · exact v565_mg_checked.trans (by decide +kernel)
  upper_error := v565_upper_checked
  lower_error := reuse_lower_error 5 96 Primitive.Addresses.material565

def v566_pa : Scalar.QComplex := ((999996929640340676042797972412 : Int)/10^30,(2478045578987496509064107488 : Int)/10^30)
theorem v566_pa_checked : Scalar.distance (sourceCoefficient 5 97 1 0) v566_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v566_pb : Scalar.QComplex := ((1069215336243630582741566 : Int)/10^30,(-431473925433148774263666655 : Int)/10^30)
theorem v566_pb_checked : Scalar.distance (sourceCoefficient 5 97 1 1) v566_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v566_pg : Scalar.QComplex := ((-93085899140783480892592 : Int)/10^30,(-230671809077311638981 : Int)/10^30)
theorem v566_pg_checked : Scalar.distance (sourceCoefficient 5 97 1 2) v566_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v566_mb : Scalar.QComplex := ((696872373341307632512360 : Int)/10^30,(-431474687460366510086610412 : Int)/10^30)
theorem v566_mb_checked : Scalar.distance (sourceCoefficient 5 97 3 1) v566_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v566_mg : Scalar.QComplex := ((-93086063540031156124264 : Int)/10^30,(-150342784662425615566 : Int)/10^30)
theorem v566_mg_checked : Scalar.distance (sourceCoefficient 5 97 3 2) v566_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v566_upper : Scalar.QComplex := ((999999717144244661365740424214 : Int)/10^30,(752137906683269215855337568 : Int)/10^30)
theorem v566_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 97 5) 1) 14) v566_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material566 : Material (5 : Basis) (97 : Basis) where
  plus := ![v566_pa,v566_pb,v566_pg]
  minus := ![(Primitive.Addresses.material566 1).one,v566_mb,v566_mg]
  upper := v566_upper
  lower := (Primitive.Addresses.material566 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v566_pa_checked.trans (by decide +kernel)
    · exact v566_pb_checked.trans (by decide +kernel)
    · exact v566_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 97 Primitive.Addresses.material566
    · exact v566_mb_checked.trans (by decide +kernel)
    · exact v566_mg_checked.trans (by decide +kernel)
  upper_error := v566_upper_checked
  lower_error := reuse_lower_error 5 97 Primitive.Addresses.material566

def v567_pa : Scalar.QComplex := ((999999931992323801669943203954 : Int)/10^30,(368802586449195190151685223 : Int)/10^30)
theorem v567_pa_checked : Scalar.distance (sourceCoefficient 6 7 1 0) v567_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v567_pb : Scalar.QComplex := ((159130025645966377564013 : Int)/10^30,(-431477491402637578588980543 : Int)/10^30)
theorem v567_pb_checked : Scalar.distance (sourceCoefficient 6 7 1 1) v567_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v567_pg : Scalar.QComplex := ((-93086423538960465522973 : Int)/10^30,(-34330516099212487756 : Int)/10^30)
theorem v567_pg_checked : Scalar.distance (sourceCoefficient 6 7 1 2) v567_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v567_mb : Scalar.QComplex := ((-213215675661066018033030 : Int)/10^30,(-431477468065893216030656654 : Int)/10^30)
theorem v567_mb_checked : Scalar.distance (sourceCoefficient 6 7 3 1) v567_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v567_mg : Scalar.QComplex := ((-93086418504319926820071 : Int)/10^30,(45998887740845640124 : Int)/10^30)
theorem v567_mg_checked : Scalar.distance (sourceCoefficient 6 7 3 2) v567_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v567_upper : Scalar.QComplex := ((999999079129700044833466638790 : Int)/10^30,(-1357107126172515434560570866 : Int)/10^30)
theorem v567_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 7 5) 1) 14) v567_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material567 : Material (6 : Basis) (7 : Basis) where
  plus := ![v567_pa,v567_pb,v567_pg]
  minus := ![(Primitive.Addresses.material567 1).one,v567_mb,v567_mg]
  upper := v567_upper
  lower := (Primitive.Addresses.material567 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v567_pa_checked.trans (by decide +kernel)
    · exact v567_pb_checked.trans (by decide +kernel)
    · exact v567_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 7 Primitive.Addresses.material567
    · exact v567_mb_checked.trans (by decide +kernel)
    · exact v567_mg_checked.trans (by decide +kernel)
  upper_error := v567_upper_checked
  lower_error := reuse_lower_error 6 7 Primitive.Addresses.material567

def v568_pa : Scalar.QComplex := ((999999945394606727827921263764 : Int)/10^30,(330470548706832849994674980 : Int)/10^30)
theorem v568_pa_checked : Scalar.distance (sourceCoefficient 6 8 1 0) v568_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v568_pb : Scalar.QComplex := ((142590612892485949856585 : Int)/10^30,(-431477496751955600002777704 : Int)/10^30)
theorem v568_pb_checked : Scalar.distance (sourceCoefficient 6 8 1 1) v568_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v568_pg : Scalar.QComplex := ((-93086424739773447568295 : Int)/10^30,(-30762323540699006414 : Int)/10^30)
theorem v568_pg_checked : Scalar.distance (sourceCoefficient 6 8 1 2) v568_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v568_mb : Scalar.QComplex := ((-229755086872387717255165 : Int)/10^30,(-431477459142440946893420041 : Int)/10^30)
theorem v568_mb_checked : Scalar.distance (sourceCoefficient 6 8 3 1) v568_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v568_mg : Scalar.QComplex := ((-93086416625942989177875 : Int)/10^30,(49567080007005478371 : Int)/10^30)
theorem v568_mg_checked : Scalar.distance (sourceCoefficient 6 8 3 2) v568_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v568_upper : Scalar.QComplex := ((999999026374343321847566868415 : Int)/10^30,(-1395439129954934839865636773 : Int)/10^30)
theorem v568_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 8 5) 1) 14) v568_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material568 : Material (6 : Basis) (8 : Basis) where
  plus := ![v568_pa,v568_pb,v568_pg]
  minus := ![(Primitive.Addresses.material568 1).one,v568_mb,v568_mg]
  upper := v568_upper
  lower := (Primitive.Addresses.material568 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v568_pa_checked.trans (by decide +kernel)
    · exact v568_pb_checked.trans (by decide +kernel)
    · exact v568_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 8 Primitive.Addresses.material568
    · exact v568_mb_checked.trans (by decide +kernel)
    · exact v568_mg_checked.trans (by decide +kernel)
  upper_error := v568_upper_checked
  lower_error := reuse_lower_error 6 8 Primitive.Addresses.material568

def v569_pa : Scalar.QComplex := ((999999952163175626874701070999 : Int)/10^30,(309311568580757793409602510 : Int)/10^30)
theorem v569_pa_checked : Scalar.distance (sourceCoefficient 6 9 1 0) v569_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v569_pb : Scalar.QComplex := ((133460988513327667332032 : Int)/10^30,(-431477499342649476117080824 : Int)/10^30)
theorem v569_pb_checked : Scalar.distance (sourceCoefficient 6 9 1 1) v569_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v569_pg : Scalar.QComplex := ((-93086425334260960888520 : Int)/10^30,(-28792709611067641798 : Int)/10^30)
theorem v569_pg_checked : Scalar.distance (sourceCoefficient 6 9 1 2) v569_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v569_mb : Scalar.QComplex := ((-238884710087821733538517 : Int)/10^30,(-431477453854679202178600876 : Int)/10^30)
theorem v569_mb_checked : Scalar.distance (sourceCoefficient 6 9 3 1) v569_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v569_mg : Scalar.QComplex := ((-93086415520742167989752 : Int)/10^30,(51536693716275510453 : Int)/10^30)
theorem v569_mg_checked : Scalar.distance (sourceCoefficient 6 9 3 2) v569_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v569_upper : Scalar.QComplex := ((999998996624421969983025983586 : Int)/10^30,(-1416598090249130387045799652 : Int)/10^30)
theorem v569_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 9 5) 1) 14) v569_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material569 : Material (6 : Basis) (9 : Basis) where
  plus := ![v569_pa,v569_pb,v569_pg]
  minus := ![(Primitive.Addresses.material569 1).one,v569_mb,v569_mg]
  upper := v569_upper
  lower := (Primitive.Addresses.material569 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v569_pa_checked.trans (by decide +kernel)
    · exact v569_pb_checked.trans (by decide +kernel)
    · exact v569_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 9 Primitive.Addresses.material569
    · exact v569_mb_checked.trans (by decide +kernel)
    · exact v569_mg_checked.trans (by decide +kernel)
  upper_error := v569_upper_checked
  lower_error := reuse_lower_error 6 9 Primitive.Addresses.material569

def v570_pa : Scalar.QComplex := ((999999964238842782454064665866 : Int)/10^30,(267436559124274378124172354 : Int)/10^30)
theorem v570_pa_checked : Scalar.distance (sourceCoefficient 6 10 1 0) v570_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v570_pb : Scalar.QComplex := ((115392863058458273419110 : Int)/10^30,(-431477503710531802627025379 : Int)/10^30)
theorem v570_pb_checked : Scalar.distance (sourceCoefficient 6 10 1 1) v570_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v570_pg : Scalar.QComplex := ((-93086426367462115238013 : Int)/10^30,(-24894714459152993070 : Int)/10^30)
theorem v570_pg_checked : Scalar.distance (sourceCoefficient 6 10 1 2) v570_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v570_mb : Scalar.QComplex := ((-256952832584387992137958 : Int)/10^30,(-431477442630581392936410627 : Int)/10^30)
theorem v570_mb_checked : Scalar.distance (sourceCoefficient 6 10 3 1) v570_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v570_mg : Scalar.QComplex := ((-93086413190148680713473 : Int)/10^30,(55434688308394479495 : Int)/10^30)
theorem v570_mg_checked : Scalar.distance (sourceCoefficient 6 10 3 2) v570_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v570_upper : Scalar.QComplex := ((999998936427603689567033089692 : Int)/10^30,(-1458473058179212215612903879 : Int)/10^30)
theorem v570_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 10 5) 1) 14) v570_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material570 : Material (6 : Basis) (10 : Basis) where
  plus := ![v570_pa,v570_pb,v570_pg]
  minus := ![(Primitive.Addresses.material570 1).one,v570_mb,v570_mg]
  upper := v570_upper
  lower := (Primitive.Addresses.material570 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v570_pa_checked.trans (by decide +kernel)
    · exact v570_pb_checked.trans (by decide +kernel)
    · exact v570_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 10 Primitive.Addresses.material570
    · exact v570_mb_checked.trans (by decide +kernel)
    · exact v570_mg_checked.trans (by decide +kernel)
  upper_error := v570_upper_checked
  lower_error := reuse_lower_error 6 10 Primitive.Addresses.material570

def v571_pa : Scalar.QComplex := ((999999966608632618613027702007 : Int)/10^30,(258423554746448236757953177 : Int)/10^30)
theorem v571_pa_checked : Scalar.distance (sourceCoefficient 6 11 1 0) v571_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v571_pb : Scalar.QComplex := ((111503954234124892231051 : Int)/10^30,(-431477504518724208371905193 : Int)/10^30)
theorem v571_pb_checked : Scalar.distance (sourceCoefficient 6 11 1 1) v571_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v571_pg : Scalar.QComplex := ((-93086426564938971147413 : Int)/10^30,(-24055726054809326015 : Int)/10^30)
theorem v571_pg_checked : Scalar.distance (sourceCoefficient 6 11 1 2) v571_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v571_mb : Scalar.QComplex := ((-260841740658136532636387 : Int)/10^30,(-431477440082820332306189749 : Int)/10^30)
theorem v571_mb_checked : Scalar.distance (sourceCoefficient 6 11 3 1) v571_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v571_mg : Scalar.QComplex := ((-93086412663616256779655 : Int)/10^30,(56273676570758052572 : Int)/10^30)
theorem v571_mg_checked : Scalar.distance (sourceCoefficient 6 11 3 2) v571_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v571_upper : Scalar.QComplex := ((999998923241762093444489015949 : Int)/10^30,(-1467486053223269349629674332 : Int)/10^30)
theorem v571_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 11 5) 1) 14) v571_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material571 : Material (6 : Basis) (11 : Basis) where
  plus := ![v571_pa,v571_pb,v571_pg]
  minus := ![(Primitive.Addresses.material571 1).one,v571_mb,v571_mg]
  upper := v571_upper
  lower := (Primitive.Addresses.material571 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v571_pa_checked.trans (by decide +kernel)
    · exact v571_pb_checked.trans (by decide +kernel)
    · exact v571_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 11 Primitive.Addresses.material571
    · exact v571_mb_checked.trans (by decide +kernel)
    · exact v571_mg_checked.trans (by decide +kernel)
  upper_error := v571_upper_checked
  lower_error := reuse_lower_error 6 11 Primitive.Addresses.material571

def v572_pa : Scalar.QComplex := ((999999967868302321889471510798 : Int)/10^30,(253502257038818219080796104 : Int)/10^30)
theorem v572_pa_checked : Scalar.distance (sourceCoefficient 6 12 1 0) v572_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v572_pb : Scalar.QComplex := ((109380524878423129030662 : Int)/10^30,(-431477504940289282903368164 : Int)/10^30)
theorem v572_pb_checked : Scalar.distance (sourceCoefficient 6 12 1 1) v572_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v572_pg : Scalar.QComplex := ((-93086426669042014461870 : Int)/10^30,(-23597620018512184356 : Int)/10^30)
theorem v572_pg_checked : Scalar.distance (sourceCoefficient 6 12 1 2) v572_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v572_mb : Scalar.QComplex := ((-262965169586980173927819 : Int)/10^30,(-431477438671961351607103803 : Int)/10^30)
theorem v572_mb_checked : Scalar.distance (sourceCoefficient 6 12 3 1) v572_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v572_mg : Scalar.QComplex := ((-93086412372394384337325 : Int)/10^30,(56731782526317618191 : Int)/10^30)
theorem v572_mg_checked : Scalar.distance (sourceCoefficient 6 12 3 2) v572_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v572_upper : Scalar.QComplex := ((999998916007716533861978790932 : Int)/10^30,(-1472407345775280159542042699 : Int)/10^30)
theorem v572_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 12 5) 1) 14) v572_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material572 : Material (6 : Basis) (12 : Basis) where
  plus := ![v572_pa,v572_pb,v572_pg]
  minus := ![(Primitive.Addresses.material572 1).one,v572_mb,v572_mg]
  upper := v572_upper
  lower := (Primitive.Addresses.material572 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v572_pa_checked.trans (by decide +kernel)
    · exact v572_pb_checked.trans (by decide +kernel)
    · exact v572_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 12 Primitive.Addresses.material572
    · exact v572_mb_checked.trans (by decide +kernel)
    · exact v572_mg_checked.trans (by decide +kernel)
  upper_error := v572_upper_checked
  lower_error := reuse_lower_error 6 12 Primitive.Addresses.material572

def v573_pa : Scalar.QComplex := ((999999979600610770694006684789 : Int)/10^30,(201987073948995324569864755 : Int)/10^30)
theorem v573_pa_checked : Scalar.distance (sourceCoefficient 6 13 1 0) v573_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v573_pb : Scalar.QComplex := ((87152881197986804482137 : Int)/10^30,(-431477508516850086883505506 : Int)/10^30)
theorem v573_pb_checked : Scalar.distance (sourceCoefficient 6 13 1 1) v573_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v573_pg : Scalar.QComplex := ((-93086427600902785018801 : Int)/10^30,(-18802255519025878999 : Int)/10^30)
theorem v573_pg_checked : Scalar.distance (sourceCoefficient 6 13 1 2) v573_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v573_mb : Scalar.QComplex := ((-285192808077459794265428 : Int)/10^30,(-431477423067065423562588711 : Int)/10^30)
theorem v573_mb_checked : Scalar.distance (sourceCoefficient 6 13 3 1) v573_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v573_mg : Scalar.QComplex := ((-93086409166071220062902 : Int)/10^30,(61527146044424436943 : Int)/10^30)
theorem v573_mg_checked : Scalar.distance (sourceCoefficient 6 13 3 2) v573_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v573_upper : Scalar.QComplex := ((999998838829474916640085376415 : Int)/10^30,(-1523922472388189276183434895 : Int)/10^30)
theorem v573_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 13 5) 1) 14) v573_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material573 : Material (6 : Basis) (13 : Basis) where
  plus := ![v573_pa,v573_pb,v573_pg]
  minus := ![(Primitive.Addresses.material573 1).one,v573_mb,v573_mg]
  upper := v573_upper
  lower := (Primitive.Addresses.material573 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v573_pa_checked.trans (by decide +kernel)
    · exact v573_pb_checked.trans (by decide +kernel)
    · exact v573_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 13 Primitive.Addresses.material573
    · exact v573_mb_checked.trans (by decide +kernel)
    · exact v573_mg_checked.trans (by decide +kernel)
  upper_error := v573_upper_checked
  lower_error := reuse_lower_error 6 13 Primitive.Addresses.material573

def v574_pa : Scalar.QComplex := ((999999982762073654982929910130 : Int)/10^30,(185676741658421062199677778 : Int)/10^30)
theorem v574_pa_checked : Scalar.distance (sourceCoefficient 6 14 1 0) v574_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v574_pb : Scalar.QComplex := ((80115339412496347488832 : Int)/10^30,(-431477509331016034911866441 : Int)/10^30)
theorem v574_pb_checked : Scalar.distance (sourceCoefficient 6 14 1 1) v574_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v574_pg : Scalar.QComplex := ((-93086427835871012359522 : Int)/10^30,(-17283984911126336010 : Int)/10^30)
theorem v574_pg_checked : Scalar.distance (sourceCoefficient 6 14 1 2) v574_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v574_mb : Scalar.QComplex := ((-292230347945140357447500 : Int)/10^30,(-431477417808149466677436625 : Int)/10^30)
theorem v574_mb_checked : Scalar.distance (sourceCoefficient 6 14 3 1) v574_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v574_mg : Scalar.QComplex := ((-93086408090840205666689 : Int)/10^30,(63045416289769441836 : Int)/10^30)
theorem v574_mg_checked : Scalar.distance (sourceCoefficient 6 14 3 2) v574_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v574_upper : Scalar.QComplex := ((999998813840779220557154448944 : Int)/10^30,(-1540232785842837670572211926 : Int)/10^30)
theorem v574_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 14 5) 1) 14) v574_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material574 : Material (6 : Basis) (14 : Basis) where
  plus := ![v574_pa,v574_pb,v574_pg]
  minus := ![(Primitive.Addresses.material574 1).one,v574_mb,v574_mg]
  upper := v574_upper
  lower := (Primitive.Addresses.material574 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v574_pa_checked.trans (by decide +kernel)
    · exact v574_pb_checked.trans (by decide +kernel)
    · exact v574_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 14 Primitive.Addresses.material574
    · exact v574_mb_checked.trans (by decide +kernel)
    · exact v574_mg_checked.trans (by decide +kernel)
  upper_error := v574_upper_checked
  lower_error := reuse_lower_error 6 14 Primitive.Addresses.material574

def v575_pa : Scalar.QComplex := ((999999987296049080599918334321 : Int)/10^30,(159398562344237579289868273 : Int)/10^30)
theorem v575_pa_checked : Scalar.distance (sourceCoefficient 6 15 1 0) v575_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v575_pb : Scalar.QComplex := ((68776895702748572249084 : Int)/10^30,(-431477510320823917983704314 : Int)/10^30)
theorem v575_pb_checked : Scalar.distance (sourceCoefficient 6 15 1 1) v575_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v575_pg : Scalar.QComplex := ((-93086428153666773790901 : Int)/10^30,(-14837843009953874810 : Int)/10^30)
theorem v575_pg_checked : Scalar.distance (sourceCoefficient 6 15 1 2) v575_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v575_mb : Scalar.QComplex := ((-303568788287226970870191 : Int)/10^30,(-431477409013390724234161093 : Int)/10^30)
theorem v575_mb_checked : Scalar.distance (sourceCoefficient 6 15 3 1) v575_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v575_mg : Scalar.QComplex := ((-93086406297725558197869 : Int)/10^30,(65491557554374908147 : Int)/10^30)
theorem v575_mg_checked : Scalar.distance (sourceCoefficient 6 15 3 2) v575_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v575_upper : Scalar.QComplex := ((999998773020994334874735634912 : Int)/10^30,(-1566510933843990182364836590 : Int)/10^30)
theorem v575_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 15 5) 1) 14) v575_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material575 : Material (6 : Basis) (15 : Basis) where
  plus := ![v575_pa,v575_pb,v575_pg]
  minus := ![(Primitive.Addresses.material575 1).one,v575_mb,v575_mg]
  upper := v575_upper
  lower := (Primitive.Addresses.material575 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v575_pa_checked.trans (by decide +kernel)
    · exact v575_pb_checked.trans (by decide +kernel)
    · exact v575_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 15 Primitive.Addresses.material575
    · exact v575_mb_checked.trans (by decide +kernel)
    · exact v575_mg_checked.trans (by decide +kernel)
  upper_error := v575_upper_checked
  lower_error := reuse_lower_error 6 15 Primitive.Addresses.material575

def v576_pa : Scalar.QComplex := ((999999987821685440145460204581 : Int)/10^30,(156066104492287927651879570 : Int)/10^30)
theorem v576_pa_checked : Scalar.distance (sourceCoefficient 6 16 1 0) v576_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v576_pb : Scalar.QComplex := ((67339015047037566684481 : Int)/10^30,(-431477510417961672566831470 : Int)/10^30)
theorem v576_pb_checked : Scalar.distance (sourceCoefficient 6 16 1 1) v576_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v576_pg : Scalar.QComplex := ((-93086428188609769827507 : Int)/10^30,(-14527636405419554735 : Int)/10^30)
theorem v576_pg_checked : Scalar.distance (sourceCoefficient 6 16 1 2) v576_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v576_mb : Scalar.QComplex := ((-305006668491374801204441 : Int)/10^30,(-431477407869702196510603649 : Int)/10^30)
theorem v576_mb_checked : Scalar.distance (sourceCoefficient 6 16 3 1) v576_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v576_mg : Scalar.QComplex := ((-93086406064974212697316 : Int)/10^30,(65801764073559364017 : Int)/10^30)
theorem v576_mg_checked : Scalar.distance (sourceCoefficient 6 16 3 2) v576_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v576_upper : Scalar.QComplex := ((999998767795109977296315397610 : Int)/10^30,(-1569843387639835992739098590 : Int)/10^30)
theorem v576_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 16 5) 1) 14) v576_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material576 : Material (6 : Basis) (16 : Basis) where
  plus := ![v576_pa,v576_pb,v576_pg]
  minus := ![(Primitive.Addresses.material576 1).one,v576_mb,v576_mg]
  upper := v576_upper
  lower := (Primitive.Addresses.material576 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v576_pa_checked.trans (by decide +kernel)
    · exact v576_pb_checked.trans (by decide +kernel)
    · exact v576_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 16 Primitive.Addresses.material576
    · exact v576_mb_checked.trans (by decide +kernel)
    · exact v576_mg_checked.trans (by decide +kernel)
  upper_error := v576_upper_checked
  lower_error := reuse_lower_error 6 16 Primitive.Addresses.material576

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
