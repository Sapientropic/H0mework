import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B071
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B072

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1713_pa : Scalar.QComplex := ((999999678080314642317307250270 : Int)/10^30,(-802395954054531337222484124 : Int)/10^30)
theorem v1713_pa_checked : Scalar.distance (sourceCoefficient 19 61 1 0) v1713_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1713_pb : Scalar.QComplex := ((-346215796554721008857921 : Int)/10^30,(-431477356474197374720174691 : Int)/10^30)
theorem v1713_pb_checked : Scalar.distance (sourceCoefficient 19 61 1 1) v1713_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1713_pg : Scalar.QComplex := ((-93086397166431353944863 : Int)/10^30,(74692172508738381434 : Int)/10^30)
theorem v1713_pg_checked : Scalar.distance (sourceCoefficient 19 61 1 2) v1713_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1713_mb : Scalar.QComplex := ((-718561193261241409547311 : Int)/10^30,(-431476897046818623937026582 : Int)/10^30)
theorem v1713_mb_checked : Scalar.distance (sourceCoefficient 19 61 3 1) v1713_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1713_mg : Scalar.QComplex := ((-93086298050130565897957 : Int)/10^30,(155021512996362108886 : Int)/10^30)
theorem v1713_mg_checked : Scalar.distance (sourceCoefficient 19 61 3 2) v1713_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1713_upper : Scalar.QComplex := ((999996803835638449772577431415 : Int)/10^30,(-2528303484084501435065291331 : Int)/10^30)
theorem v1713_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 61 5) 1) 14) v1713_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1713 : Material (19 : Basis) (61 : Basis) where
  plus := ![v1713_pa,v1713_pb,v1713_pg]
  minus := ![(Primitive.Addresses.material1713 1).one,v1713_mb,v1713_mg]
  upper := v1713_upper
  lower := (Primitive.Addresses.material1713 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1713_pa_checked.trans (by decide +kernel)
    · exact v1713_pb_checked.trans (by decide +kernel)
    · exact v1713_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 61 Primitive.Addresses.material1713
    · exact v1713_mb_checked.trans (by decide +kernel)
    · exact v1713_mg_checked.trans (by decide +kernel)
  upper_error := v1713_upper_checked
  lower_error := reuse_lower_error 19 61 Primitive.Addresses.material1713

def v1714_pa : Scalar.QComplex := ((999999671212987755701666667853 : Int)/10^30,(-810909314527646331765712544 : Int)/10^30)
theorem v1714_pa_checked : Scalar.distance (sourceCoefficient 19 62 1 0) v1714_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1714_pb : Scalar.QComplex := ((-349889119411951760650098 : Int)/10^30,(-431477352774969026899424403 : Int)/10^30)
theorem v1714_pb_checked : Scalar.distance (sourceCoefficient 19 62 1 1) v1714_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1714_pg : Scalar.QComplex := ((-93086396447770394466453 : Int)/10^30,(75484650753683014637 : Int)/10^30)
theorem v1714_pg_checked : Scalar.distance (sourceCoefficient 19 62 1 2) v1714_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1714_mb : Scalar.QComplex := ((-722234511558458725335239 : Int)/10^30,(-431476890177679468037970790 : Int)/10^30)
theorem v1714_mb_checked : Scalar.distance (sourceCoefficient 19 62 3 1) v1714_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1714_mg : Scalar.QComplex := ((-93086296647596840517855 : Int)/10^30,(155813990326058832710 : Int)/10^30)
theorem v1714_mg_checked : Scalar.distance (sourceCoefficient 19 62 3 2) v1714_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1714_upper : Scalar.QComplex := ((999996782275033940666202137348 : Int)/10^30,(-2536816820025582847204515083 : Int)/10^30)
theorem v1714_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 62 5) 1) 14) v1714_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1714 : Material (19 : Basis) (62 : Basis) where
  plus := ![v1714_pa,v1714_pb,v1714_pg]
  minus := ![(Primitive.Addresses.material1714 1).one,v1714_mb,v1714_mg]
  upper := v1714_upper
  lower := (Primitive.Addresses.material1714 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1714_pa_checked.trans (by decide +kernel)
    · exact v1714_pb_checked.trans (by decide +kernel)
    · exact v1714_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 62 Primitive.Addresses.material1714
    · exact v1714_mb_checked.trans (by decide +kernel)
    · exact v1714_mg_checked.trans (by decide +kernel)
  upper_error := v1714_upper_checked
  lower_error := reuse_lower_error 19 62 Primitive.Addresses.material1714

def v1715_pa : Scalar.QComplex := ((999999650798950124521137499602 : Int)/10^30,(-835704479950648877017916408 : Int)/10^30)
theorem v1715_pa_checked : Scalar.distance (sourceCoefficient 19 63 1 0) v1715_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1715_pb : Scalar.QComplex := ((-360587673426461566628247 : Int)/10^30,(-431477341763396225073372572 : Int)/10^30)
theorem v1715_pb_checked : Scalar.distance (sourceCoefficient 19 63 1 1) v1715_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1715_pg : Scalar.QComplex := ((-93086394309823863221659 : Int)/10^30,(77792743912480239344 : Int)/10^30)
theorem v1715_pg_checked : Scalar.distance (sourceCoefficient 19 63 1 2) v1715_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1715_mb : Scalar.QComplex := ((-732933052086916538491248 : Int)/10^30,(-431476869933740496787651121 : Int)/10^30)
theorem v1715_mb_checked : Scalar.distance (sourceCoefficient 19 63 3 1) v1715_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1715_mg : Scalar.QComplex := ((-93086292517870661943227 : Int)/10^30,(158122080780495922401 : Int)/10^30)
theorem v1715_mg_checked : Scalar.distance (sourceCoefficient 19 63 3 2) v1715_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1715_upper : Scalar.QComplex := ((999996719066820593530157757316 : Int)/10^30,(-2561611913286322135236837922 : Int)/10^30)
theorem v1715_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 63 5) 1) 14) v1715_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1715 : Material (19 : Basis) (63 : Basis) where
  plus := ![v1715_pa,v1715_pb,v1715_pg]
  minus := ![(Primitive.Addresses.material1715 1).one,v1715_mb,v1715_mg]
  upper := v1715_upper
  lower := (Primitive.Addresses.material1715 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1715_pa_checked.trans (by decide +kernel)
    · exact v1715_pb_checked.trans (by decide +kernel)
    · exact v1715_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 63 Primitive.Addresses.material1715
    · exact v1715_mb_checked.trans (by decide +kernel)
    · exact v1715_mg_checked.trans (by decide +kernel)
  upper_error := v1715_upper_checked
  lower_error := reuse_lower_error 19 63 Primitive.Addresses.material1715

def v1716_pa : Scalar.QComplex := ((999999620555963732831318829449 : Int)/10^30,(-871141738499861286276021908 : Int)/10^30)
theorem v1716_pa_checked : Scalar.distance (sourceCoefficient 19 64 1 0) v1716_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1716_pb : Scalar.QComplex := ((-375878050007075192550717 : Int)/10^30,(-431477325411667903293850038 : Int)/10^30)
theorem v1716_pb_checked : Scalar.distance (sourceCoefficient 19 64 1 1) v1716_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1716_pg : Scalar.QComplex := ((-93086391138367163050979 : Int)/10^30,(81091471376630458104 : Int)/10^30)
theorem v1716_pg_checked : Scalar.distance (sourceCoefficient 19 64 1 2) v1716_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1716_mb : Scalar.QComplex := ((-748223408863419071529285 : Int)/10^30,(-431476840387111927431524453 : Int)/10^30)
theorem v1716_mb_checked : Scalar.distance (sourceCoefficient 19 64 3 1) v1716_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1716_mg : Scalar.QComplex := ((-93086286499761910259019 : Int)/10^30,(161420804279554851825 : Int)/10^30)
theorem v1716_mg_checked : Scalar.distance (sourceCoefficient 19 64 3 2) v1716_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1716_upper : Scalar.QComplex := ((999996627662385832257969721505 : Int)/10^30,(-2597049066859249798486511978 : Int)/10^30)
theorem v1716_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 64 5) 1) 14) v1716_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1716 : Material (19 : Basis) (64 : Basis) where
  plus := ![v1716_pa,v1716_pb,v1716_pg]
  minus := ![(Primitive.Addresses.material1716 1).one,v1716_mb,v1716_mg]
  upper := v1716_upper
  lower := (Primitive.Addresses.material1716 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1716_pa_checked.trans (by decide +kernel)
    · exact v1716_pb_checked.trans (by decide +kernel)
    · exact v1716_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 64 Primitive.Addresses.material1716
    · exact v1716_mb_checked.trans (by decide +kernel)
    · exact v1716_mg_checked.trans (by decide +kernel)
  upper_error := v1716_upper_checked
  lower_error := reuse_lower_error 19 64 Primitive.Addresses.material1716

def v1717_pa : Scalar.QComplex := ((999999588577142253650760293440 : Int)/10^30,(-907108343156389783208034654 : Int)/10^30)
theorem v1717_pa_checked : Scalar.distance (sourceCoefficient 19 65 1 0) v1717_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1717_pb : Scalar.QComplex := ((-391396827068862556826744 : Int)/10^30,(-431477308076950195829375071 : Int)/10^30)
theorem v1717_pb_checked : Scalar.distance (sourceCoefficient 19 65 1 1) v1717_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1717_pg : Scalar.QComplex := ((-93086387780084655803330 : Int)/10^30,(84439473729935389098 : Int)/10^30)
theorem v1717_pg_checked : Scalar.distance (sourceCoefficient 19 65 1 2) v1717_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1717_mb : Scalar.QComplex := ((-763742165187775837714595 : Int)/10^30,(-431476809660395009925191274 : Int)/10^30)
theorem v1717_mb_checked : Scalar.distance (sourceCoefficient 19 65 3 1) v1717_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1717_mg : Scalar.QComplex := ((-93086280252305410979736 : Int)/10^30,(164768802488198943092 : Int)/10^30)
theorem v1717_mg_checked : Scalar.distance (sourceCoefficient 19 65 3 2) v1717_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1717_upper : Scalar.QComplex := ((999996533608515209493660989054 : Int)/10^30,(-2633015562755200816644551353 : Int)/10^30)
theorem v1717_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 65 5) 1) 14) v1717_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1717 : Material (19 : Basis) (65 : Basis) where
  plus := ![v1717_pa,v1717_pb,v1717_pg]
  minus := ![(Primitive.Addresses.material1717 1).one,v1717_mb,v1717_mg]
  upper := v1717_upper
  lower := (Primitive.Addresses.material1717 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1717_pa_checked.trans (by decide +kernel)
    · exact v1717_pb_checked.trans (by decide +kernel)
    · exact v1717_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 65 Primitive.Addresses.material1717
    · exact v1717_mb_checked.trans (by decide +kernel)
    · exact v1717_mg_checked.trans (by decide +kernel)
  upper_error := v1717_upper_checked
  lower_error := reuse_lower_error 19 65 Primitive.Addresses.material1717

def v1718_pa : Scalar.QComplex := ((999999572468652744035174215164 : Int)/10^30,(-924695902299170332529378005 : Int)/10^30)
theorem v1718_pa_checked : Scalar.distance (sourceCoefficient 19 66 1 0) v1718_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1718_pb : Scalar.QComplex := ((-398985461203792101527514 : Int)/10^30,(-431477299329390918408698543 : Int)/10^30)
theorem v1718_pb_checked : Scalar.distance (sourceCoefficient 19 66 1 1) v1718_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1718_pg : Scalar.QComplex := ((-93086386086749922729528 : Int)/10^30,(86076636574716557177 : Int)/10^30)
theorem v1718_pg_checked : Scalar.distance (sourceCoefficient 19 66 1 2) v1718_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1718_mb : Scalar.QComplex := ((-771330788948360395298743 : Int)/10^30,(-431476794364189510570409605 : Int)/10^30)
theorem v1718_mb_checked : Scalar.distance (sourceCoefficient 19 66 3 1) v1718_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1718_mg : Scalar.QComplex := ((-93086277146173508443052 : Int)/10^30,(166405963262117952343 : Int)/10^30)
theorem v1718_mg_checked : Scalar.distance (sourceCoefficient 19 66 3 2) v1718_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1718_upper : Scalar.QComplex := ((999996487145518142043564883264 : Int)/10^30,(-2650603067901586459774709818 : Int)/10^30)
theorem v1718_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 66 5) 1) 14) v1718_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1718 : Material (19 : Basis) (66 : Basis) where
  plus := ![v1718_pa,v1718_pb,v1718_pg]
  minus := ![(Primitive.Addresses.material1718 1).one,v1718_mb,v1718_mg]
  upper := v1718_upper
  lower := (Primitive.Addresses.material1718 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1718_pa_checked.trans (by decide +kernel)
    · exact v1718_pb_checked.trans (by decide +kernel)
    · exact v1718_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 66 Primitive.Addresses.material1718
    · exact v1718_mb_checked.trans (by decide +kernel)
    · exact v1718_mg_checked.trans (by decide +kernel)
  upper_error := v1718_upper_checked
  lower_error := reuse_lower_error 19 66 Primitive.Addresses.material1718

def v1719_pa : Scalar.QComplex := ((999999544738629440825573177693 : Int)/10^30,(-954213044270216068306893157 : Int)/10^30)
theorem v1719_pa_checked : Scalar.distance (sourceCoefficient 19 67 1 0) v1719_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1719_pb : Scalar.QComplex := ((-411721440377017645874169 : Int)/10^30,(-431477284248441185553892900 : Int)/10^30)
theorem v1719_pb_checked : Scalar.distance (sourceCoefficient 19 67 1 1) v1719_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1719_pg : Scalar.QComplex := ((-93086383169332707709606 : Int)/10^30,(88824281502376902651 : Int)/10^30)
theorem v1719_pg_checked : Scalar.distance (sourceCoefficient 19 67 1 2) v1719_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1719_mb : Scalar.QComplex := ((-784066750365218431759225 : Int)/10^30,(-431476768292668973757439777 : Int)/10^30)
theorem v1719_mb_checked : Scalar.distance (sourceCoefficient 19 67 3 1) v1719_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1719_mg : Scalar.QComplex := ((-93086271857663556473763 : Int)/10^30,(169153604649104856705 : Int)/10^30)
theorem v1719_mg_checked : Scalar.distance (sourceCoefficient 19 67 3 2) v1719_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1719_upper : Scalar.QComplex := ((999996408471626871623325796396 : Int)/10^30,(-2680120118050811983465093758 : Int)/10^30)
theorem v1719_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 67 5) 1) 14) v1719_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1719 : Material (19 : Basis) (67 : Basis) where
  plus := ![v1719_pa,v1719_pb,v1719_pg]
  minus := ![(Primitive.Addresses.material1719 1).one,v1719_mb,v1719_mg]
  upper := v1719_upper
  lower := (Primitive.Addresses.material1719 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1719_pa_checked.trans (by decide +kernel)
    · exact v1719_pb_checked.trans (by decide +kernel)
    · exact v1719_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 67 Primitive.Addresses.material1719
    · exact v1719_mb_checked.trans (by decide +kernel)
    · exact v1719_mg_checked.trans (by decide +kernel)
  upper_error := v1719_upper_checked
  lower_error := reuse_lower_error 19 67 Primitive.Addresses.material1719

def v1720_pa : Scalar.QComplex := ((999999496623187688710201727226 : Int)/10^30,(-1003371003783926588247005044 : Int)/10^30)
theorem v1720_pa_checked : Scalar.distance (sourceCoefficient 19 68 1 0) v1720_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1720_pb : Scalar.QComplex := ((-432931987417462384372873 : Int)/10^30,(-431477258020074670020520744 : Int)/10^30)
theorem v1720_pb_checked : Scalar.distance (sourceCoefficient 19 68 1 1) v1720_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1720_pg : Scalar.QComplex := ((-93086378100647580933693 : Int)/10^30,(93400219648961721096 : Int)/10^30)
theorem v1720_pg_checked : Scalar.distance (sourceCoefficient 19 68 1 2) v1720_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1720_mb : Scalar.QComplex := ((-805277266874108116084080 : Int)/10^30,(-431476723760565415916567474 : Int)/10^30)
theorem v1720_mb_checked : Scalar.distance (sourceCoefficient 19 68 3 1) v1720_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1720_mg : Scalar.QComplex := ((-93086262840151789101880 : Int)/10^30,(173729536717811793168 : Int)/10^30)
theorem v1720_mg_checked : Scalar.distance (sourceCoefficient 19 68 3 2) v1720_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1720_upper : Scalar.QComplex := ((999996275514078236392843601730 : Int)/10^30,(-2729277921306628841921458317 : Int)/10^30)
theorem v1720_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 68 5) 1) 14) v1720_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1720 : Material (19 : Basis) (68 : Basis) where
  plus := ![v1720_pa,v1720_pb,v1720_pg]
  minus := ![(Primitive.Addresses.material1720 1).one,v1720_mb,v1720_mg]
  upper := v1720_upper
  lower := (Primitive.Addresses.material1720 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1720_pa_checked.trans (by decide +kernel)
    · exact v1720_pb_checked.trans (by decide +kernel)
    · exact v1720_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 68 Primitive.Addresses.material1720
    · exact v1720_mb_checked.trans (by decide +kernel)
    · exact v1720_mg_checked.trans (by decide +kernel)
  upper_error := v1720_upper_checked
  lower_error := reuse_lower_error 19 68 Primitive.Addresses.material1720

def v1721_pa : Scalar.QComplex := ((999999474680822063903153492546 : Int)/10^30,(-1025006380424997640198934680 : Int)/10^30)
theorem v1721_pa_checked : Scalar.distance (sourceCoefficient 19 69 1 0) v1721_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1721_pb : Scalar.QComplex := ((-442267162526405464579813 : Int)/10^30,(-431477246035879705171760397 : Int)/10^30)
theorem v1721_pb_checked : Scalar.distance (sourceCoefficient 19 69 1 1) v1721_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1721_pg : Scalar.QComplex := ((-93086375786651593964502 : Int)/10^30,(95414179234855091796 : Int)/10^30)
theorem v1721_pg_checked : Scalar.distance (sourceCoefficient 19 69 1 2) v1721_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1721_mb : Scalar.QComplex := ((-814612428165318358093004 : Int)/10^30,(-431476703720539234992834229 : Int)/10^30)
theorem v1721_mb_checked : Scalar.distance (sourceCoefficient 19 69 3 1) v1721_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1721_mg : Scalar.QComplex := ((-93086258788200246485778 : Int)/10^30,(175743493556941649295 : Int)/10^30)
theorem v1721_mg_checked : Scalar.distance (sourceCoefficient 19 69 3 2) v1721_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1721_upper : Scalar.QComplex := ((999996216231047955709973849554 : Int)/10^30,(-2750913227853815384309673074 : Int)/10^30)
theorem v1721_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 69 5) 1) 14) v1721_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1721 : Material (19 : Basis) (69 : Basis) where
  plus := ![v1721_pa,v1721_pb,v1721_pg]
  minus := ![(Primitive.Addresses.material1721 1).one,v1721_mb,v1721_mg]
  upper := v1721_upper
  lower := (Primitive.Addresses.material1721 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1721_pa_checked.trans (by decide +kernel)
    · exact v1721_pb_checked.trans (by decide +kernel)
    · exact v1721_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 69 Primitive.Addresses.material1721
    · exact v1721_mb_checked.trans (by decide +kernel)
    · exact v1721_mg_checked.trans (by decide +kernel)
  upper_error := v1721_upper_checked
  lower_error := reuse_lower_error 19 69 Primitive.Addresses.material1721

def v1722_pa : Scalar.QComplex := ((999999459991691562541156565431 : Int)/10^30,(-1039238339008884191282407719 : Int)/10^30)
theorem v1722_pa_checked : Scalar.distance (sourceCoefficient 19 70 1 0) v1722_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1722_pb : Scalar.QComplex := ((-448407930289219216827591 : Int)/10^30,(-431477238005725619296950449 : Int)/10^30)
theorem v1722_pb_checked : Scalar.distance (sourceCoefficient 19 70 1 1) v1722_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1722_pg : Scalar.QComplex := ((-93086374236764448301403 : Int)/10^30,(96738981186028065372 : Int)/10^30)
theorem v1722_pg_checked : Scalar.distance (sourceCoefficient 19 70 1 2) v1722_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1722_mb : Scalar.QComplex := ((-820753186711982313898663 : Int)/10^30,(-431476690391182129716397791 : Int)/10^30)
theorem v1722_mb_checked : Scalar.distance (sourceCoefficient 19 70 3 1) v1722_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1722_mg : Scalar.QComplex := ((-93086256095069260919163 : Int)/10^30,(177068293677347507627 : Int)/10^30)
theorem v1722_mg_checked : Scalar.distance (sourceCoefficient 19 70 3 2) v1722_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1722_upper : Scalar.QComplex := ((999996176978869929491272427015 : Int)/10^30,(-2765145139888764770145842196 : Int)/10^30)
theorem v1722_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 70 5) 1) 14) v1722_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1722 : Material (19 : Basis) (70 : Basis) where
  plus := ![v1722_pa,v1722_pb,v1722_pg]
  minus := ![(Primitive.Addresses.material1722 1).one,v1722_mb,v1722_mg]
  upper := v1722_upper
  lower := (Primitive.Addresses.material1722 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1722_pa_checked.trans (by decide +kernel)
    · exact v1722_pb_checked.trans (by decide +kernel)
    · exact v1722_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 70 Primitive.Addresses.material1722
    · exact v1722_mb_checked.trans (by decide +kernel)
    · exact v1722_mg_checked.trans (by decide +kernel)
  upper_error := v1722_upper_checked
  lower_error := reuse_lower_error 19 70 Primitive.Addresses.material1722

def v1723_pa : Scalar.QComplex := ((999999434450594980469029113053 : Int)/10^30,(-1063531142088905840342805324 : Int)/10^30)
theorem v1723_pa_checked : Scalar.distance (sourceCoefficient 19 71 1 0) v1723_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1723_pb : Scalar.QComplex := ((-458889724382463294955760 : Int)/10^30,(-431477224029695461128254166 : Int)/10^30)
theorem v1723_pb_checked : Scalar.distance (sourceCoefficient 19 71 1 1) v1723_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1723_pg : Scalar.QComplex := ((-93086371540413913736094 : Int)/10^30,(99000311026855628901 : Int)/10^30)
theorem v1723_pg_checked : Scalar.distance (sourceCoefficient 19 71 1 2) v1723_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1723_mb : Scalar.QComplex := ((-831234964841690839989058 : Int)/10^30,(-431476667369840955474260357 : Int)/10^30)
theorem v1723_mb_checked : Scalar.distance (sourceCoefficient 19 71 3 1) v1723_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1723_mg : Scalar.QComplex := ((-93086251447293924209510 : Int)/10^30,(179329620349349551328 : Int)/10^30)
theorem v1723_mg_checked : Scalar.distance (sourceCoefficient 19 71 3 2) v1723_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1723_upper : Scalar.QComplex := ((999996109510637097644946270140 : Int)/10^30,(-2789437862705894234146040030 : Int)/10^30)
theorem v1723_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 71 5) 1) 14) v1723_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1723 : Material (19 : Basis) (71 : Basis) where
  plus := ![v1723_pa,v1723_pb,v1723_pg]
  minus := ![(Primitive.Addresses.material1723 1).one,v1723_mb,v1723_mg]
  upper := v1723_upper
  lower := (Primitive.Addresses.material1723 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1723_pa_checked.trans (by decide +kernel)
    · exact v1723_pb_checked.trans (by decide +kernel)
    · exact v1723_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 71 Primitive.Addresses.material1723
    · exact v1723_mb_checked.trans (by decide +kernel)
    · exact v1723_mg_checked.trans (by decide +kernel)
  upper_error := v1723_upper_checked
  lower_error := reuse_lower_error 19 71 Primitive.Addresses.material1723

def v1724_pa : Scalar.QComplex := ((999999406065627229361774085681 : Int)/10^30,(-1089893752979269669406373291 : Int)/10^30)
theorem v1724_pa_checked : Scalar.distance (sourceCoefficient 19 72 1 0) v1724_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1724_pb : Scalar.QComplex := ((-470264593380218358289583 : Int)/10^30,(-431477208478739411533944978 : Int)/10^30)
theorem v1724_pb_checked : Scalar.distance (sourceCoefficient 19 72 1 1) v1724_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1724_pg : Scalar.QComplex := ((-93086368541814183246635 : Int)/10^30,(101454311818452341183 : Int)/10^30)
theorem v1724_pg_checked : Scalar.distance (sourceCoefficient 19 72 1 2) v1724_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1724_mb : Scalar.QComplex := ((-842609816184287636524927 : Int)/10^30,(-431476642002891056230982889 : Int)/10^30)
theorem v1724_mb_checked : Scalar.distance (sourceCoefficient 19 72 3 1) v1724_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1724_mg : Scalar.QComplex := ((-93086246331003151180618 : Int)/10^30,(181783617639553100028 : Int)/10^30)
theorem v1724_mg_checked : Scalar.distance (sourceCoefficient 19 72 3 2) v1724_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1724_upper : Scalar.QComplex := ((999996035626236823222695353488 : Int)/10^30,(-2815800385342366637572042202 : Int)/10^30)
theorem v1724_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 72 5) 1) 14) v1724_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1724 : Material (19 : Basis) (72 : Basis) where
  plus := ![v1724_pa,v1724_pb,v1724_pg]
  minus := ![(Primitive.Addresses.material1724 1).one,v1724_mb,v1724_mg]
  upper := v1724_upper
  lower := (Primitive.Addresses.material1724 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1724_pa_checked.trans (by decide +kernel)
    · exact v1724_pb_checked.trans (by decide +kernel)
    · exact v1724_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 72 Primitive.Addresses.material1724
    · exact v1724_mb_checked.trans (by decide +kernel)
    · exact v1724_mg_checked.trans (by decide +kernel)
  upper_error := v1724_upper_checked
  lower_error := reuse_lower_error 19 72 Primitive.Addresses.material1724

def v1725_pa : Scalar.QComplex := ((999999395721872912541896305668 : Int)/10^30,(-1099343389948227837645804035 : Int)/10^30)
theorem v1725_pa_checked : Scalar.distance (sourceCoefficient 19 73 1 0) v1725_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1725_pb : Scalar.QComplex := ((-474341897453855733764810 : Int)/10^30,(-431477202807178245765067862 : Int)/10^30)
theorem v1725_pb_checked : Scalar.distance (sourceCoefficient 19 73 1 1) v1725_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1725_pg : Scalar.QComplex := ((-93086367448594784005549 : Int)/10^30,(102333944587068930602 : Int)/10^30)
theorem v1725_pg_checked : Scalar.distance (sourceCoefficient 19 73 1 2) v1725_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1725_mb : Scalar.QComplex := ((-846687113845456514957387 : Int)/10^30,(-431476632812802221653102439 : Int)/10^30)
theorem v1725_mb_checked : Scalar.distance (sourceCoefficient 19 73 3 1) v1725_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1725_mg : Scalar.QComplex := ((-93086244478700696868200 : Int)/10^30,(182663249137243103716 : Int)/10^30)
theorem v1725_mg_checked : Scalar.distance (sourceCoefficient 19 73 3 2) v1725_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1725_upper : Scalar.QComplex := ((999996008973281768157253490007 : Int)/10^30,(-2825249990384819000112479440 : Int)/10^30)
theorem v1725_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 73 5) 1) 14) v1725_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1725 : Material (19 : Basis) (73 : Basis) where
  plus := ![v1725_pa,v1725_pb,v1725_pg]
  minus := ![(Primitive.Addresses.material1725 1).one,v1725_mb,v1725_mg]
  upper := v1725_upper
  lower := (Primitive.Addresses.material1725 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1725_pa_checked.trans (by decide +kernel)
    · exact v1725_pb_checked.trans (by decide +kernel)
    · exact v1725_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 73 Primitive.Addresses.material1725
    · exact v1725_mb_checked.trans (by decide +kernel)
    · exact v1725_mg_checked.trans (by decide +kernel)
  upper_error := v1725_upper_checked
  lower_error := reuse_lower_error 19 73 Primitive.Addresses.material1725

def v1726_pa : Scalar.QComplex := ((999999383975834819863873058174 : Int)/10^30,(-1109976554200357949164334159 : Int)/10^30)
theorem v1726_pa_checked : Scalar.distance (sourceCoefficient 19 74 1 0) v1726_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1726_pb : Scalar.QComplex := ((-478929866668350532315387 : Int)/10^30,(-431477196363851620541715454 : Int)/10^30)
theorem v1726_pb_checked : Scalar.distance (sourceCoefficient 19 74 1 1) v1726_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1726_pg : Scalar.QComplex := ((-93086366206858723486007 : Int)/10^30,(103323747655247083095 : Int)/10^30)
theorem v1726_pg_checked : Scalar.distance (sourceCoefficient 19 74 1 2) v1726_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1726_mb : Scalar.QComplex := ((-851275075791340013490859 : Int)/10^30,(-431476622410267197928505052 : Int)/10^30)
theorem v1726_mb_checked : Scalar.distance (sourceCoefficient 19 74 3 1) v1726_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1726_mg : Scalar.QComplex := ((-93086242382809629941335 : Int)/10^30,(183653050765310043179 : Int)/10^30)
theorem v1726_mg_checked : Scalar.distance (sourceCoefficient 19 74 3 2) v1726_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1726_upper : Scalar.QComplex := ((999995978875384303772263037643 : Int)/10^30,(-2835883118527503861587437691 : Int)/10^30)
theorem v1726_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 74 5) 1) 14) v1726_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1726 : Material (19 : Basis) (74 : Basis) where
  plus := ![v1726_pa,v1726_pb,v1726_pg]
  minus := ![(Primitive.Addresses.material1726 1).one,v1726_mb,v1726_mg]
  upper := v1726_upper
  lower := (Primitive.Addresses.material1726 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1726_pa_checked.trans (by decide +kernel)
    · exact v1726_pb_checked.trans (by decide +kernel)
    · exact v1726_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 74 Primitive.Addresses.material1726
    · exact v1726_mb_checked.trans (by decide +kernel)
    · exact v1726_mg_checked.trans (by decide +kernel)
  upper_error := v1726_upper_checked
  lower_error := reuse_lower_error 19 74 Primitive.Addresses.material1726

def v1727_pa : Scalar.QComplex := ((999999367421645093023725757542 : Int)/10^30,(-1124791673892804672226348461 : Int)/10^30)
theorem v1727_pa_checked : Scalar.distance (sourceCoefficient 19 75 1 0) v1727_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1727_pb : Scalar.QComplex := ((-485322254729284224394978 : Int)/10^30,(-431477187277955496776721971 : Int)/10^30)
theorem v1727_pb_checked : Scalar.distance (sourceCoefficient 19 75 1 1) v1727_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1727_pg : Scalar.QComplex := ((-93086364456283479367602 : Int)/10^30,(104702833926125210314 : Int)/10^30)
theorem v1727_pg_checked : Scalar.distance (sourceCoefficient 19 75 1 2) v1727_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1727_mb : Scalar.QComplex := ((-857667453631376342679622 : Int)/10^30,(-431476607808031463142930517 : Int)/10^30)
theorem v1727_mb_checked : Scalar.distance (sourceCoefficient 19 75 3 1) v1727_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1727_mg : Scalar.QComplex := ((-93086239442145697614219 : Int)/10^30,(185032135012023731702 : Int)/10^30)
theorem v1727_mg_checked : Scalar.distance (sourceCoefficient 19 75 3 2) v1727_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1727_upper : Scalar.QComplex := ((999995936751666660449691012728 : Int)/10^30,(-2850698187583540424793605338 : Int)/10^30)
theorem v1727_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 75 5) 1) 14) v1727_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1727 : Material (19 : Basis) (75 : Basis) where
  plus := ![v1727_pa,v1727_pb,v1727_pg]
  minus := ![(Primitive.Addresses.material1727 1).one,v1727_mb,v1727_mg]
  upper := v1727_upper
  lower := (Primitive.Addresses.material1727 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1727_pa_checked.trans (by decide +kernel)
    · exact v1727_pb_checked.trans (by decide +kernel)
    · exact v1727_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 75 Primitive.Addresses.material1727
    · exact v1727_mb_checked.trans (by decide +kernel)
    · exact v1727_mg_checked.trans (by decide +kernel)
  upper_error := v1727_upper_checked
  lower_error := reuse_lower_error 19 75 Primitive.Addresses.material1727

def v1728_pa : Scalar.QComplex := ((999999353363021835834939305054 : Int)/10^30,(-1137221850910783630862124505 : Int)/10^30)
theorem v1728_pa_checked : Scalar.distance (sourceCoefficient 19 76 1 0) v1728_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1728_pb : Scalar.QComplex := ((-490685594057358452718328 : Int)/10^30,(-431477179557292476000640750 : Int)/10^30)
theorem v1728_pb_checked : Scalar.distance (sourceCoefficient 19 76 1 1) v1728_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1728_pg : Scalar.QComplex := ((-93086362969126777859228 : Int)/10^30,(105859914443238567143 : Int)/10^30)
theorem v1728_pg_checked : Scalar.distance (sourceCoefficient 19 76 1 2) v1728_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1728_mb : Scalar.QComplex := ((-863030784299849761269143 : Int)/10^30,(-431476595459051032830846941 : Int)/10^30)
theorem v1728_mb_checked : Scalar.distance (sourceCoefficient 19 76 3 1) v1728_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1728_mg : Scalar.QComplex := ((-93086236956481176545391 : Int)/10^30,(186189213814953876468 : Int)/10^30)
theorem v1728_mg_checked : Scalar.distance (sourceCoefficient 19 76 3 2) v1728_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1728_upper : Scalar.QComplex := ((999995901239706465747420790154 : Int)/10^30,(-2863128321824322512743538938 : Int)/10^30)
theorem v1728_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 76 5) 1) 14) v1728_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1728 : Material (19 : Basis) (76 : Basis) where
  plus := ![v1728_pa,v1728_pb,v1728_pg]
  minus := ![(Primitive.Addresses.material1728 1).one,v1728_mb,v1728_mg]
  upper := v1728_upper
  lower := (Primitive.Addresses.material1728 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1728_pa_checked.trans (by decide +kernel)
    · exact v1728_pb_checked.trans (by decide +kernel)
    · exact v1728_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 76 Primitive.Addresses.material1728
    · exact v1728_mb_checked.trans (by decide +kernel)
    · exact v1728_mg_checked.trans (by decide +kernel)
  upper_error := v1728_upper_checked
  lower_error := reuse_lower_error 19 76 Primitive.Addresses.material1728

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
