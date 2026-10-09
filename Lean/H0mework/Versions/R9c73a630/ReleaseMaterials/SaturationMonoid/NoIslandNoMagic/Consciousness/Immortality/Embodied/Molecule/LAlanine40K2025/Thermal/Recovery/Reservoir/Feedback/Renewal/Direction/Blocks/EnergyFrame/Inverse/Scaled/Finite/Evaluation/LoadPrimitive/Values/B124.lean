import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B082
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B083

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1985_pa : Scalar.QComplex := ((999999892499541405218200373341 : Int)/10^30,(-463681901343167588988077997 : Int)/10^30)
theorem v1985_pa_checked : Scalar.distance (sourceCoefficient 23 31 1 0) v1985_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1985_pb : Scalar.QComplex := ((-200068316818364240733172 : Int)/10^30,(-431477473525237613664365440 : Int)/10^30)
theorem v1985_pb_checked : Scalar.distance (sourceCoefficient 23 31 1 1) v1985_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1985_pg : Scalar.QComplex := ((-93086419772415261887726 : Int)/10^30,(43162492749289502877 : Int)/10^30)
theorem v1985_pg_checked : Scalar.distance (sourceCoefficient 23 31 1 2) v1985_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1985_mb : Scalar.QComplex := ((-572413868952046560109024 : Int)/10^30,(-431477140216508053762170317 : Int)/10^30)
theorem v1985_mb_checked : Scalar.distance (sourceCoefficient 23 31 3 1) v1985_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1985_mg : Scalar.QComplex := ((-93086347864799644942397 : Int)/10^30,(123491864484799959157 : Int)/10^30)
theorem v1985_mg_checked : Scalar.distance (sourceCoefficient 23 31 3 2) v1985_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1985_upper : Scalar.QComplex := ((999997602844272941407686460730 : Int)/10^30,(-2189590305916064485276170550 : Int)/10^30)
theorem v1985_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 31 5) 1) 14) v1985_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1985 : Material (23 : Basis) (31 : Basis) where
  plus := ![v1985_pa,v1985_pb,v1985_pg]
  minus := ![(Primitive.Addresses.material1985 1).one,v1985_mb,v1985_mg]
  upper := v1985_upper
  lower := (Primitive.Addresses.material1985 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1985_pa_checked.trans (by decide +kernel)
    · exact v1985_pb_checked.trans (by decide +kernel)
    · exact v1985_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 31 Primitive.Addresses.material1985
    · exact v1985_mb_checked.trans (by decide +kernel)
    · exact v1985_mg_checked.trans (by decide +kernel)
  upper_error := v1985_upper_checked
  lower_error := reuse_lower_error 23 31 Primitive.Addresses.material1985

def v1986_pa : Scalar.QComplex := ((999999890273549365078063719076 : Int)/10^30,(-468457990891339053507660606 : Int)/10^30)
theorem v1986_pa_checked : Scalar.distance (sourceCoefficient 23 32 1 0) v1986_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1986_pb : Scalar.QComplex := ((-202129092051062486688660 : Int)/10^30,(-431477472478507462189490104 : Int)/10^30)
theorem v1986_pb_checked : Scalar.distance (sourceCoefficient 23 32 1 1) v1986_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1986_pg : Scalar.QComplex := ((-93086419555900297987632 : Int)/10^30,(43607081869275623399 : Int)/10^30)
theorem v1986_pg_checked : Scalar.distance (sourceCoefficient 23 32 1 2) v1986_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1986_mb : Scalar.QComplex := ((-574474642514143027103308 : Int)/10^30,(-431477137391422080085249929 : Int)/10^30)
theorem v1986_mb_checked : Scalar.distance (sourceCoefficient 23 32 3 1) v1986_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1986_mg : Scalar.QComplex := ((-93086347264624374663352 : Int)/10^30,(123936453252402569208 : Int)/10^30)
theorem v1986_mg_checked : Scalar.distance (sourceCoefficient 23 32 3 2) v1986_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1986_upper : Scalar.QComplex := ((999997592375186939936447916017 : Int)/10^30,(-2194366384508951285822051068 : Int)/10^30)
theorem v1986_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 32 5) 1) 14) v1986_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1986 : Material (23 : Basis) (32 : Basis) where
  plus := ![v1986_pa,v1986_pb,v1986_pg]
  minus := ![(Primitive.Addresses.material1986 1).one,v1986_mb,v1986_mg]
  upper := v1986_upper
  lower := (Primitive.Addresses.material1986 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1986_pa_checked.trans (by decide +kernel)
    · exact v1986_pb_checked.trans (by decide +kernel)
    · exact v1986_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 32 Primitive.Addresses.material1986
    · exact v1986_mb_checked.trans (by decide +kernel)
    · exact v1986_mg_checked.trans (by decide +kernel)
  upper_error := v1986_upper_checked
  lower_error := reuse_lower_error 23 32 Primitive.Addresses.material1986

def v1987_pa : Scalar.QComplex := ((999999887133285943770112871049 : Int)/10^30,(-475114107739987691903619078 : Int)/10^30)
theorem v1987_pa_checked : Scalar.distance (sourceCoefficient 23 33 1 0) v1987_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1987_pb : Scalar.QComplex := ((-205001056780850799980787 : Int)/10^30,(-431477470997860994263078776 : Int)/10^30)
theorem v1987_pb_checked : Scalar.distance (sourceCoefficient 23 33 1 1) v1987_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1987_pg : Scalar.QComplex := ((-93086419250025918394705 : Int)/10^30,(44226676016406074075 : Int)/10^30)
theorem v1987_pg_checked : Scalar.distance (sourceCoefficient 23 33 1 2) v1987_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1987_mb : Scalar.QComplex := ((-577346604896836400243880 : Int)/10^30,(-431477133432399950153661147 : Int)/10^30)
theorem v1987_mb_checked : Scalar.distance (sourceCoefficient 23 33 3 1) v1987_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1987_mg : Scalar.QComplex := ((-93086346424068265472344 : Int)/10^30,(124556046904873988538 : Int)/10^30)
theorem v1987_mg_checked : Scalar.distance (sourceCoefficient 23 33 3 2) v1987_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1987_upper : Scalar.QComplex := ((999997577747074353118016196138 : Int)/10^30,(-2201022486024285977859826668 : Int)/10^30)
theorem v1987_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 33 5) 1) 14) v1987_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1987 : Material (23 : Basis) (33 : Basis) where
  plus := ![v1987_pa,v1987_pb,v1987_pg]
  minus := ![(Primitive.Addresses.material1987 1).one,v1987_mb,v1987_mg]
  upper := v1987_upper
  lower := (Primitive.Addresses.material1987 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1987_pa_checked.trans (by decide +kernel)
    · exact v1987_pb_checked.trans (by decide +kernel)
    · exact v1987_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 33 Primitive.Addresses.material1987
    · exact v1987_mb_checked.trans (by decide +kernel)
    · exact v1987_mg_checked.trans (by decide +kernel)
  upper_error := v1987_upper_checked
  lower_error := reuse_lower_error 23 33 Primitive.Addresses.material1987

def v1988_pa : Scalar.QComplex := ((999999879321447319880088805822 : Int)/10^30,(-491281071075333356792617258 : Int)/10^30)
theorem v1988_pa_checked : Scalar.distance (sourceCoefficient 23 34 1 0) v1988_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1988_pb : Scalar.QComplex := ((-211976737858801478907352 : Int)/10^30,(-431477467295398617672915753 : Int)/10^30)
theorem v1988_pb_checked : Scalar.distance (sourceCoefficient 23 34 1 1) v1988_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1988_pg : Scalar.QComplex := ((-93086418487055493938044 : Int)/10^30,(45731600895710742914 : Int)/10^30)
theorem v1988_pg_checked : Scalar.distance (sourceCoefficient 23 34 1 2) v1988_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1988_mb : Scalar.QComplex := ((-584322280182363931192868 : Int)/10^30,(-431477123710240354901116349 : Int)/10^30)
theorem v1988_mb_checked : Scalar.distance (sourceCoefficient 23 34 3 1) v1988_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1988_mg : Scalar.QComplex := ((-93086344362415733564990 : Int)/10^30,(126060970565417232953 : Int)/10^30)
theorem v1988_mg_checked : Scalar.distance (sourceCoefficient 23 34 3 2) v1988_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1988_upper : Scalar.QComplex := ((999997542032535302694260655792 : Int)/10^30,(-2217189411798314079299509640 : Int)/10^30)
theorem v1988_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 34 5) 1) 14) v1988_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1988 : Material (23 : Basis) (34 : Basis) where
  plus := ![v1988_pa,v1988_pb,v1988_pg]
  minus := ![(Primitive.Addresses.material1988 1).one,v1988_mb,v1988_mg]
  upper := v1988_upper
  lower := (Primitive.Addresses.material1988 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1988_pa_checked.trans (by decide +kernel)
    · exact v1988_pb_checked.trans (by decide +kernel)
    · exact v1988_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 34 Primitive.Addresses.material1988
    · exact v1988_mb_checked.trans (by decide +kernel)
    · exact v1988_mg_checked.trans (by decide +kernel)
  upper_error := v1988_upper_checked
  lower_error := reuse_lower_error 23 34 Primitive.Addresses.material1988

def v1989_pa : Scalar.QComplex := ((999999852769185108946747291817 : Int)/10^30,(-542643168302332589066496776 : Int)/10^30)
theorem v1989_pa_checked : Scalar.distance (sourceCoefficient 23 35 1 0) v1989_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1989_pb : Scalar.QComplex := ((-234138327452303848093960 : Int)/10^30,(-431477454535053510725478227 : Int)/10^30)
theorem v1989_pb_checked : Scalar.distance (sourceCoefficient 23 35 1 1) v1989_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1989_pg : Scalar.QComplex := ((-93086415874777265116838 : Int)/10^30,(50512715073225886146 : Int)/10^30)
theorem v1989_pg_checked : Scalar.distance (sourceCoefficient 23 35 1 2) v1989_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1989_mb : Scalar.QComplex := ((-606483850512490537353013 : Int)/10^30,(-431477091825446300964094400 : Int)/10^30)
theorem v1989_mb_checked : Scalar.distance (sourceCoefficient 23 35 3 1) v1989_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1989_mg : Scalar.QComplex := ((-93086337624252275607791 : Int)/10^30,(130842080708426601356 : Int)/10^30)
theorem v1989_mg_checked : Scalar.distance (sourceCoefficient 23 35 3 2) v1989_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1989_upper : Scalar.QComplex := ((999997426833992357497918169361 : Int)/10^30,(-2268551386700707134062954075 : Int)/10^30)
theorem v1989_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 35 5) 1) 14) v1989_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1989 : Material (23 : Basis) (35 : Basis) where
  plus := ![v1989_pa,v1989_pb,v1989_pg]
  minus := ![(Primitive.Addresses.material1989 1).one,v1989_mb,v1989_mg]
  upper := v1989_upper
  lower := (Primitive.Addresses.material1989 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1989_pa_checked.trans (by decide +kernel)
    · exact v1989_pb_checked.trans (by decide +kernel)
    · exact v1989_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 35 Primitive.Addresses.material1989
    · exact v1989_mb_checked.trans (by decide +kernel)
    · exact v1989_mg_checked.trans (by decide +kernel)
  upper_error := v1989_upper_checked
  lower_error := reuse_lower_error 23 35 Primitive.Addresses.material1989

def v1990_pa : Scalar.QComplex := ((999999843877922948041324870569 : Int)/10^30,(-558788090182507743863895443 : Int)/10^30)
theorem v1990_pa_checked : Scalar.distance (sourceCoefficient 23 36 1 0) v1990_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1990_pb : Scalar.QComplex := ((-241104498001687216890250 : Int)/10^30,(-431477450210515808114225944 : Int)/10^30)
theorem v1990_pb_checked : Scalar.distance (sourceCoefficient 23 36 1 1) v1990_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1990_pg : Scalar.QComplex := ((-93086414994464116050077 : Int)/10^30,(52015588177474620913 : Int)/10^30)
theorem v1990_pg_checked : Scalar.distance (sourceCoefficient 23 36 1 2) v1990_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1990_mb : Scalar.QComplex := ((-613450014736168973486400 : Int)/10^30,(-431477081489418769132817103 : Int)/10^30)
theorem v1990_mb_checked : Scalar.distance (sourceCoefficient 23 36 3 1) v1990_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1990_mg : Scalar.QComplex := ((-93086335447027652247150 : Int)/10^30,(132344952493416394904 : Int)/10^30)
theorem v1990_mg_checked : Scalar.distance (sourceCoefficient 23 36 3 2) v1990_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1990_upper : Scalar.QComplex := ((999997390078072929772431913458 : Int)/10^30,(-2284696269189405783366064591 : Int)/10^30)
theorem v1990_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 36 5) 1) 14) v1990_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1990 : Material (23 : Basis) (36 : Basis) where
  plus := ![v1990_pa,v1990_pb,v1990_pg]
  minus := ![(Primitive.Addresses.material1990 1).one,v1990_mb,v1990_mg]
  upper := v1990_upper
  lower := (Primitive.Addresses.material1990 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1990_pa_checked.trans (by decide +kernel)
    · exact v1990_pb_checked.trans (by decide +kernel)
    · exact v1990_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 36 Primitive.Addresses.material1990
    · exact v1990_mb_checked.trans (by decide +kernel)
    · exact v1990_mg_checked.trans (by decide +kernel)
  upper_error := v1990_upper_checked
  lower_error := reuse_lower_error 23 36 Primitive.Addresses.material1990

def v1991_pa : Scalar.QComplex := ((999999840001842093001381737137 : Int)/10^30,(-565682145921706373676792578 : Int)/10^30)
theorem v1991_pa_checked : Scalar.distance (sourceCoefficient 23 37 1 0) v1991_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1991_pb : Scalar.QComplex := ((-244079127933674235207430 : Int)/10^30,(-431477448318203269541441205 : Int)/10^30)
theorem v1991_pb_checked : Scalar.distance (sourceCoefficient 23 37 1 1) v1991_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1991_pg : Scalar.QComplex := ((-93086414609936261562146 : Int)/10^30,(52657331197782416346 : Int)/10^30)
theorem v1991_pg_checked : Scalar.distance (sourceCoefficient 23 37 1 2) v1991_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1991_mb : Scalar.QComplex := ((-616424641927584826625652 : Int)/10^30,(-431477077030135276208525586 : Int)/10^30)
theorem v1991_mb_checked : Scalar.distance (sourceCoefficient 23 37 3 1) v1991_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1991_mg : Scalar.QComplex := ((-93086334508704617443589 : Int)/10^30,(132986694942943714841 : Int)/10^30)
theorem v1991_mg_checked : Scalar.distance (sourceCoefficient 23 37 3 2) v1991_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1991_upper : Scalar.QComplex := ((999997374303483065693887949003 : Int)/10^30,(-2291590307970954301826774645 : Int)/10^30)
theorem v1991_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 37 5) 1) 14) v1991_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1991 : Material (23 : Basis) (37 : Basis) where
  plus := ![v1991_pa,v1991_pb,v1991_pg]
  minus := ![(Primitive.Addresses.material1991 1).one,v1991_mb,v1991_mg]
  upper := v1991_upper
  lower := (Primitive.Addresses.material1991 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1991_pa_checked.trans (by decide +kernel)
    · exact v1991_pb_checked.trans (by decide +kernel)
    · exact v1991_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 37 Primitive.Addresses.material1991
    · exact v1991_mb_checked.trans (by decide +kernel)
    · exact v1991_mg_checked.trans (by decide +kernel)
  upper_error := v1991_upper_checked
  lower_error := reuse_lower_error 23 37 Primitive.Addresses.material1991

def v1992_pa : Scalar.QComplex := ((999999826549404725320658790918 : Int)/10^30,(-588983158048046125348833282 : Int)/10^30)
theorem v1992_pa_checked : Scalar.distance (sourceCoefficient 23 38 1 0) v1992_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1992_pb : Scalar.QComplex := ((-254132990330284159737438 : Int)/10^30,(-431477441720048111741161590 : Int)/10^30)
theorem v1992_pb_checked : Scalar.distance (sourceCoefficient 23 38 1 1) v1992_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1992_pg : Scalar.QComplex := ((-93086413272077637420676 : Int)/10^30,(54826339170015007360 : Int)/10^30)
theorem v1992_pg_checked : Scalar.distance (sourceCoefficient 23 38 1 2) v1992_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1992_mb : Scalar.QComplex := ((-626478494886771565382481 : Int)/10^30,(-431477061755952136081874362 : Int)/10^30)
theorem v1992_mb_checked : Scalar.distance (sourceCoefficient 23 38 3 1) v1992_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1992_mg : Scalar.QComplex := ((-93086331299090299904003 : Int)/10^30,(135155700953043771513 : Int)/10^30)
theorem v1992_mg_checked : Scalar.distance (sourceCoefficient 23 38 3 2) v1992_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1992_upper : Scalar.QComplex := ((999997320635632655083579785404 : Int)/10^30,(-2314891262175487119440812596 : Int)/10^30)
theorem v1992_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 38 5) 1) 14) v1992_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1992 : Material (23 : Basis) (38 : Basis) where
  plus := ![v1992_pa,v1992_pb,v1992_pg]
  minus := ![(Primitive.Addresses.material1992 1).one,v1992_mb,v1992_mg]
  upper := v1992_upper
  lower := (Primitive.Addresses.material1992 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1992_pa_checked.trans (by decide +kernel)
    · exact v1992_pb_checked.trans (by decide +kernel)
    · exact v1992_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 38 Primitive.Addresses.material1992
    · exact v1992_mb_checked.trans (by decide +kernel)
    · exact v1992_mg_checked.trans (by decide +kernel)
  upper_error := v1992_upper_checked
  lower_error := reuse_lower_error 23 38 Primitive.Addresses.material1992

def v1993_pa : Scalar.QComplex := ((999999818496527549786934921517 : Int)/10^30,(-602500549341588251029983935 : Int)/10^30)
theorem v1993_pa_checked : Scalar.distance (sourceCoefficient 23 39 1 0) v1993_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1993_pb : Scalar.QComplex := ((-259965440457001798239582 : Int)/10^30,(-431477437749162972007542725 : Int)/10^30)
theorem v1993_pb_checked : Scalar.distance (sourceCoefficient 23 39 1 1) v1993_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1993_pg : Scalar.QComplex := ((-93086412468933905464165 : Int)/10^30,(56084624828324505725 : Int)/10^30)
theorem v1993_pg_checked : Scalar.distance (sourceCoefficient 23 39 1 2) v1993_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1993_mb : Scalar.QComplex := ((-632310939415106432006370 : Int)/10^30,(-431477052751926699335375662 : Int)/10^30)
theorem v1993_mb_checked : Scalar.distance (sourceCoefficient 23 39 3 1) v1993_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1993_mg : Scalar.QComplex := ((-93086329410103014955833 : Int)/10^30,(136413985449759144366 : Int)/10^30)
theorem v1993_mg_checked : Scalar.distance (sourceCoefficient 23 39 3 2) v1993_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1993_upper : Scalar.QComplex := ((999997289252976388869655282250 : Int)/10^30,(-2328408619437927324053094904 : Int)/10^30)
theorem v1993_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 39 5) 1) 14) v1993_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1993 : Material (23 : Basis) (39 : Basis) where
  plus := ![v1993_pa,v1993_pb,v1993_pg]
  minus := ![(Primitive.Addresses.material1993 1).one,v1993_mb,v1993_mg]
  upper := v1993_upper
  lower := (Primitive.Addresses.material1993 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1993_pa_checked.trans (by decide +kernel)
    · exact v1993_pb_checked.trans (by decide +kernel)
    · exact v1993_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 39 Primitive.Addresses.material1993
    · exact v1993_mb_checked.trans (by decide +kernel)
    · exact v1993_mg_checked.trans (by decide +kernel)
  upper_error := v1993_upper_checked
  lower_error := reuse_lower_error 23 39 Primitive.Addresses.material1993

def v1994_pa : Scalar.QComplex := ((999999804539925723375305886222 : Int)/10^30,(-625236043705582245604855080 : Int)/10^30)
theorem v1994_pa_checked : Scalar.distance (sourceCoefficient 23 40 1 0) v1994_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1994_pb : Scalar.QComplex := ((-269775294532739547731655 : Int)/10^30,(-431477430833266318571672738 : Int)/10^30)
theorem v1994_pb_checked : Scalar.distance (sourceCoefficient 23 40 1 1) v1994_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1994_pg : Scalar.QComplex := ((-93086411073335266761835 : Int)/10^30,(58200990758213620537 : Int)/10^30)
theorem v1994_pg_checked : Scalar.distance (sourceCoefficient 23 40 1 2) v1994_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1994_mb : Scalar.QComplex := ((-642120783870079845129362 : Int)/10^30,(-431477037370570373068687206 : Int)/10^30)
theorem v1994_mb_checked : Scalar.distance (sourceCoefficient 23 40 3 1) v1994_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1994_mg : Scalar.QComplex := ((-93086326188176415987479 : Int)/10^30,(138530349387289731008 : Int)/10^30)
theorem v1994_mg_checked : Scalar.distance (sourceCoefficient 23 40 3 2) v1994_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1994_upper : Scalar.QComplex := ((999997236056994624860315672736 : Int)/10^30,(-2351144055852244542873994346 : Int)/10^30)
theorem v1994_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 40 5) 1) 14) v1994_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1994 : Material (23 : Basis) (40 : Basis) where
  plus := ![v1994_pa,v1994_pb,v1994_pg]
  minus := ![(Primitive.Addresses.material1994 1).one,v1994_mb,v1994_mg]
  upper := v1994_upper
  lower := (Primitive.Addresses.material1994 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1994_pa_checked.trans (by decide +kernel)
    · exact v1994_pb_checked.trans (by decide +kernel)
    · exact v1994_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 40 Primitive.Addresses.material1994
    · exact v1994_mb_checked.trans (by decide +kernel)
    · exact v1994_mg_checked.trans (by decide +kernel)
  upper_error := v1994_upper_checked
  lower_error := reuse_lower_error 23 40 Primitive.Addresses.material1994

def v1995_pa : Scalar.QComplex := ((999999795379117368622633848174 : Int)/10^30,(-639720035166203875756459614 : Int)/10^30)
theorem v1995_pa_checked : Scalar.distance (sourceCoefficient 23 41 1 0) v1995_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1995_pb : Scalar.QComplex := ((-276024810788792238117744 : Int)/10^30,(-431477426272320212400821531 : Int)/10^30)
theorem v1995_pb_checked : Scalar.distance (sourceCoefficient 23 41 1 1) v1995_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1995_pg : Scalar.QComplex := ((-93086410154975342103187 : Int)/10^30,(59549253762857368418 : Int)/10^30)
theorem v1995_pg_checked : Scalar.distance (sourceCoefficient 23 41 1 2) v1995_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1995_mb : Scalar.QComplex := ((-648370293863260944146091 : Int)/10^30,(-431477027416574903936643146 : Int)/10^30)
theorem v1995_mb_checked : Scalar.distance (sourceCoefficient 23 41 3 1) v1995_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1995_mg : Scalar.QComplex := ((-93086324106326583780214 : Int)/10^30,(139878611097410290012 : Int)/10^30)
theorem v1995_mg_checked : Scalar.distance (sourceCoefficient 23 41 3 2) v1995_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1995_upper : Scalar.QComplex := ((999997201898144630463729364506 : Int)/10^30,(-2365628009929938143323050643 : Int)/10^30)
theorem v1995_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 41 5) 1) 14) v1995_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1995 : Material (23 : Basis) (41 : Basis) where
  plus := ![v1995_pa,v1995_pb,v1995_pg]
  minus := ![(Primitive.Addresses.material1995 1).one,v1995_mb,v1995_mg]
  upper := v1995_upper
  lower := (Primitive.Addresses.material1995 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1995_pa_checked.trans (by decide +kernel)
    · exact v1995_pb_checked.trans (by decide +kernel)
    · exact v1995_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 41 Primitive.Addresses.material1995
    · exact v1995_mb_checked.trans (by decide +kernel)
    · exact v1995_mg_checked.trans (by decide +kernel)
  upper_error := v1995_upper_checked
  lower_error := reuse_lower_error 23 41 Primitive.Addresses.material1995

def v1996_pa : Scalar.QComplex := ((999999787836598591186996395302 : Int)/10^30,(-651403682676354777953822801 : Int)/10^30)
theorem v1996_pa_checked : Scalar.distance (sourceCoefficient 23 42 1 0) v1996_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1996_pb : Scalar.QComplex := ((-281066041643545806888587 : Int)/10^30,(-431477422505245487685473574 : Int)/10^30)
theorem v1996_pb_checked : Scalar.distance (sourceCoefficient 23 42 1 1) v1996_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1996_pg : Scalar.QComplex := ((-93086409397570234911105 : Int)/10^30,(60636842753614899932 : Int)/10^30)
theorem v1996_pg_checked : Scalar.distance (sourceCoefficient 23 42 1 2) v1996_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1996_mb : Scalar.QComplex := ((-653411519590118045378422 : Int)/10^30,(-431477019299146402832306714 : Int)/10^30)
theorem v1996_mb_checked : Scalar.distance (sourceCoefficient 23 42 3 1) v1996_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1996_mg : Scalar.QComplex := ((-93086322410381442770721 : Int)/10^30,(140966199029602239747 : Int)/10^30)
theorem v1996_mg_checked : Scalar.distance (sourceCoefficient 23 42 3 2) v1996_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1996_upper : Scalar.QComplex := ((999997174190721416425731962384 : Int)/10^30,(-2377311627020965378901574402 : Int)/10^30)
theorem v1996_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 42 5) 1) 14) v1996_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1996 : Material (23 : Basis) (42 : Basis) where
  plus := ![v1996_pa,v1996_pb,v1996_pg]
  minus := ![(Primitive.Addresses.material1996 1).one,v1996_mb,v1996_mg]
  upper := v1996_upper
  lower := (Primitive.Addresses.material1996 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1996_pa_checked.trans (by decide +kernel)
    · exact v1996_pb_checked.trans (by decide +kernel)
    · exact v1996_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 42 Primitive.Addresses.material1996
    · exact v1996_mb_checked.trans (by decide +kernel)
    · exact v1996_mg_checked.trans (by decide +kernel)
  upper_error := v1996_upper_checked
  lower_error := reuse_lower_error 23 42 Primitive.Addresses.material1996

def v1997_pa : Scalar.QComplex := ((999999777634529222203056419643 : Int)/10^30,(-666881467810578233742107243 : Int)/10^30)
theorem v1997_pa_checked : Scalar.distance (sourceCoefficient 23 43 1 0) v1997_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1997_pb : Scalar.QComplex := ((-287744357423188179468209 : Int)/10^30,(-431477417393925680222156969 : Int)/10^30)
theorem v1997_pb_checked : Scalar.distance (sourceCoefficient 23 43 1 1) v1997_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1997_pg : Scalar.QComplex := ((-93086408371378202250955 : Int)/10^30,(62077614451837555157 : Int)/10^30)
theorem v1997_pg_checked : Scalar.distance (sourceCoefficient 23 43 1 2) v1997_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1997_mb : Scalar.QComplex := ((-660089828472279450545840 : Int)/10^30,(-431477008424742760892815823 : Int)/10^30)
theorem v1997_mb_checked : Scalar.distance (sourceCoefficient 23 43 3 1) v1997_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1997_mg : Scalar.QComplex := ((-93086320140868706591073 : Int)/10^30,(142406969305802238993 : Int)/10^30)
theorem v1997_mg_checked : Scalar.distance (sourceCoefficient 23 43 3 2) v1997_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1997_upper : Scalar.QComplex := ((999997137275414234254899374606 : Int)/10^30,(-2392789371494999819260916850 : Int)/10^30)
theorem v1997_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 43 5) 1) 14) v1997_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1997 : Material (23 : Basis) (43 : Basis) where
  plus := ![v1997_pa,v1997_pb,v1997_pg]
  minus := ![(Primitive.Addresses.material1997 1).one,v1997_mb,v1997_mg]
  upper := v1997_upper
  lower := (Primitive.Addresses.material1997 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1997_pa_checked.trans (by decide +kernel)
    · exact v1997_pb_checked.trans (by decide +kernel)
    · exact v1997_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 43 Primitive.Addresses.material1997
    · exact v1997_mb_checked.trans (by decide +kernel)
    · exact v1997_mg_checked.trans (by decide +kernel)
  upper_error := v1997_upper_checked
  lower_error := reuse_lower_error 23 43 Primitive.Addresses.material1997

def v1998_pa : Scalar.QComplex := ((999999773712273371269773775370 : Int)/10^30,(-672737245922451680075629443 : Int)/10^30)
theorem v1998_pa_checked : Scalar.distance (sourceCoefficient 23 44 1 0) v1998_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1998_pb : Scalar.QComplex := ((-290270993814979142828145 : Int)/10^30,(-431477415424202921010499990 : Int)/10^30)
theorem v1998_pb_checked : Scalar.distance (sourceCoefficient 23 44 1 1) v1998_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1998_pg : Scalar.QComplex := ((-93086407976351022078367 : Int)/10^30,(62622707905574332463 : Int)/10^30)
theorem v1998_pg_checked : Scalar.distance (sourceCoefficient 23 44 1 2) v1998_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1998_mb : Scalar.QComplex := ((-662616462223506184074647 : Int)/10^30,(-431477004274647324462161024 : Int)/10^30)
theorem v1998_mb_checked : Scalar.distance (sourceCoefficient 23 44 3 1) v1998_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1998_mg : Scalar.QComplex := ((-93086319275450573028133 : Int)/10^30,(142952062215685146346 : Int)/10^30)
theorem v1998_mg_checked : Scalar.distance (sourceCoefficient 23 44 3 2) v1998_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1998_upper : Scalar.QComplex := ((999997123246622436007949976534 : Int)/10^30,(-2398645134115921861536458298 : Int)/10^30)
theorem v1998_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 44 5) 1) 14) v1998_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1998 : Material (23 : Basis) (44 : Basis) where
  plus := ![v1998_pa,v1998_pb,v1998_pg]
  minus := ![(Primitive.Addresses.material1998 1).one,v1998_mb,v1998_mg]
  upper := v1998_upper
  lower := (Primitive.Addresses.material1998 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1998_pa_checked.trans (by decide +kernel)
    · exact v1998_pb_checked.trans (by decide +kernel)
    · exact v1998_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 44 Primitive.Addresses.material1998
    · exact v1998_mb_checked.trans (by decide +kernel)
    · exact v1998_mg_checked.trans (by decide +kernel)
  upper_error := v1998_upper_checked
  lower_error := reuse_lower_error 23 44 Primitive.Addresses.material1998

def v1999_pa : Scalar.QComplex := ((999999771748128456820965971681 : Int)/10^30,(-675650568702077838407013755 : Int)/10^30)
theorem v1999_pa_checked : Scalar.distance (sourceCoefficient 23 45 1 0) v1999_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1999_pb : Scalar.QComplex := ((-291528026988206336866000 : Int)/10^30,(-431477414436892531507790045 : Int)/10^30)
theorem v1999_pb_checked : Scalar.distance (sourceCoefficient 23 45 1 1) v1999_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1999_pg : Scalar.QComplex := ((-93086407778432838432527 : Int)/10^30,(62893898709581758504 : Int)/10^30)
theorem v1999_pg_checked : Scalar.distance (sourceCoefficient 23 45 1 2) v1999_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1999_mb : Scalar.QComplex := ((-663873494076678079134369 : Int)/10^30,(-431477002202574288757649671 : Int)/10^30)
theorem v1999_mb_checked : Scalar.distance (sourceCoefficient 23 45 3 1) v1999_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1999_mg : Scalar.QComplex := ((-93086318843507013198277 : Int)/10^30,(143223252747921363441 : Int)/10^30)
theorem v1999_mg_checked : Scalar.distance (sourceCoefficient 23 45 3 2) v1999_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1999_upper : Scalar.QComplex := ((999997116254349623865530036365 : Int)/10^30,(-2401558449166560026044309747 : Int)/10^30)
theorem v1999_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 45 5) 1) 14) v1999_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1999 : Material (23 : Basis) (45 : Basis) where
  plus := ![v1999_pa,v1999_pb,v1999_pg]
  minus := ![(Primitive.Addresses.material1999 1).one,v1999_mb,v1999_mg]
  upper := v1999_upper
  lower := (Primitive.Addresses.material1999 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1999_pa_checked.trans (by decide +kernel)
    · exact v1999_pb_checked.trans (by decide +kernel)
    · exact v1999_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 45 Primitive.Addresses.material1999
    · exact v1999_mb_checked.trans (by decide +kernel)
    · exact v1999_mg_checked.trans (by decide +kernel)
  upper_error := v1999_upper_checked
  lower_error := reuse_lower_error 23 45 Primitive.Addresses.material1999

def v2000_pa : Scalar.QComplex := ((999999760557724010245724580021 : Int)/10^30,(-692014808112445683151954417 : Int)/10^30)
theorem v2000_pa_checked : Scalar.distance (sourceCoefficient 23 46 1 0) v2000_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2000_pb : Scalar.QComplex := ((-298588827750646336864145 : Int)/10^30,(-431477408800390963800719362 : Int)/10^30)
theorem v2000_pb_checked : Scalar.distance (sourceCoefficient 23 46 1 1) v2000_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2000_pg : Scalar.QComplex := ((-93086406649589480197570 : Int)/10^30,(64417187259690682324 : Int)/10^30)
theorem v2000_pg_checked : Scalar.distance (sourceCoefficient 23 46 1 2) v2000_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2000_mb : Scalar.QComplex := ((-670934287346012266415558 : Int)/10^30,(-431476990472921768453371625 : Int)/10^30)
theorem v2000_mb_checked : Scalar.distance (sourceCoefficient 23 46 3 1) v2000_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2000_mg : Scalar.QComplex := ((-93086316400134662908801 : Int)/10^30,(144746539756699365390 : Int)/10^30)
theorem v2000_mg_checked : Scalar.distance (sourceCoefficient 23 46 3 2) v2000_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2000_upper : Scalar.QComplex := ((999997076820769173990917714086 : Int)/10^30,(-2417922644890692658412526058 : Int)/10^30)
theorem v2000_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 46 5) 1) 14) v2000_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2000 : Material (23 : Basis) (46 : Basis) where
  plus := ![v2000_pa,v2000_pb,v2000_pg]
  minus := ![(Primitive.Addresses.material2000 1).one,v2000_mb,v2000_mg]
  upper := v2000_upper
  lower := (Primitive.Addresses.material2000 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2000_pa_checked.trans (by decide +kernel)
    · exact v2000_pb_checked.trans (by decide +kernel)
    · exact v2000_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 46 Primitive.Addresses.material2000
    · exact v2000_mb_checked.trans (by decide +kernel)
    · exact v2000_mg_checked.trans (by decide +kernel)
  upper_error := v2000_upper_checked
  lower_error := reuse_lower_error 23 46 Primitive.Addresses.material2000

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
