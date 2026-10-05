module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0028
public import BecknerOnofri.EntropyScalarCertificate.Bessel0029
public import BecknerOnofri.EntropyScalarCertificate.Bessel0030
public import BecknerOnofri.EntropyScalarCertificate.Bessel0503
public import BecknerOnofri.EntropyScalarCertificate.Brackets0011
public import BecknerOnofri.EntropyScalarCertificate.Brackets0012
public import BecknerOnofri.EntropyScalarCertificate.Logs0023
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0184
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (29284079203435238223523437664721057263/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (29284079203435238223523437664721057263/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (939117026006887831537627243496355363223/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (939117026006887831537627243496355363223/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (1876207560516815454690377248767429195639/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1876207560516815454690377248767429195639/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨7,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨15,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0011.bracket0184 BracketBatch0011.bracket0185 (1876207560516815454690377248767429195639/20000000000000000000000000000000000000000) (14707247024945292363270629804310019/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0011.bracket0184 BracketBatch0011.bracket0185
  (1876207560516815454690377248767429195639/20000000000000000000000000000000000000000) (14707247024945292363270629804310019/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0184
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0185
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (46955851300344391576881362174817768161/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (46955851300344391576881362174817768161/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (470571816238383781851436670150954309143/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (470571816238383781851436670150954309143/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (940130329241827697620250291899131990753/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (940130329241827697620250291899131990753/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨23,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨31,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0011.bracket0185 BracketBatch0011.bracket0186 (940130329241827697620250291899131990753/10000000000000000000000000000000000000000) (59339437703410906400370041495710261/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0011.bracket0185 BracketBatch0011.bracket0186
  (940130329241827697620250291899131990753/10000000000000000000000000000000000000000) (59339437703410906400370041495710261/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0185
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0186
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (941143632476767563702873340301908618283/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (941143632476767563702873340301908618283/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (943170354177610144206590893986626521531/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (943170354177610144206590893986626521531/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (942156993327188853954732117144267569907/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (942156993327188853954732117144267569907/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨39,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨47,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0011.bracket0186 BracketBatch0011.bracket0187 (942156993327188853954732117144267569907/10000000000000000000000000000000000000000) (29926592679327874317993036855312663/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0011.bracket0186 BracketBatch0011.bracket0187
  (942156993327188853954732117144267569907/10000000000000000000000000000000000000000) (29926592679327874317993036855312663/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0186
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0187
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (117896294272201268025823861748328315191/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (117896294272201268025823861748328315191/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (236299297841884594083789378493447724647/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (236299297841884594083789378493447724647/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (472091886386287130135437101990104355029/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (472091886386287130135437101990104355029/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨55,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨63,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0011.bracket0187 BracketBatch0011.bracket0188 (472091886386287130135437101990104355029/5000000000000000000000000000000000000000) (60370245316044493079388192579873473/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0011.bracket0187 BracketBatch0011.bracket0188
  (472091886386287130135437101990104355029/5000000000000000000000000000000000000000) (60370245316044493079388192579873473/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0187
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0188
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (189039438273507675267031502794758179717/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (189039438273507675267031502794758179717/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (473612072152377365863250568750139411097/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (473612072152377365863250568750139411097/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (1892421335672293108061658651474069720779/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1892421335672293108061658651474069720779/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨71,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨79,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0011.bracket0188 BracketBatch0011.bracket0189 (1892421335672293108061658651474069720779/20000000000000000000000000000000000000000) (15222657964409770301691917820124029/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0011.bracket0188 BracketBatch0011.bracket0189
  (1892421335672293108061658651474069720779/20000000000000000000000000000000000000000) (15222657964409770301691917820124029/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0188
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0189
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (947224144304754731726501137500278822191/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (947224144304754731726501137500278822191/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (474625606623770770063327782354160025883/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (474625606623770770063327782354160025883/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (1896475357552296271853156702208598873957/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1896475357552296271853156702208598873957/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨87,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨95,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0011.bracket0189 BracketBatch0011.bracket0190 (1896475357552296271853156702208598873957/20000000000000000000000000000000000000000) (15353589824260415533975630886077851/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0011.bracket0189 BracketBatch0011.bracket0190
  (1896475357552296271853156702208598873957/20000000000000000000000000000000000000000) (15353589824260415533975630886077851/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0189
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0190
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (949251213247541540126655564708320051763/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (949251213247541540126655564708320051763/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (29727449951695661852498132230041832281/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (29727449951695661852498132230041832281/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (380105922340360543881319159213931736951/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (380105922340360543881319159213931736951/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨103,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨111,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0011.bracket0190 BracketBatch0011.bracket0191 (380105922340360543881319159213931736951/4000000000000000000000000000000000000000) (61941441979401672216311030473058177/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0011.bracket0190 BracketBatch0011.bracket0191
  (380105922340360543881319159213931736951/4000000000000000000000000000000000000000) (61941441979401672216311030473058177/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0190
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0191
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0029.rows BesselBatch0029.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (951278398454261179279940231361338632989/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (951278398454261179279940231361338632989/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0030.rows BesselBatch0030.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (953305700183356264953108648151640258467/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (953305700183356264953108648151640258467/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (29759126541212772566141388742390295179/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (29759126541212772566141388742390295179/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨119,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0023.rows ScalarLogs0023.accepted ⟨127,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0011.bracket0191 BracketBatch0012.bracket0192 (29759126541212772566141388742390295179/312500000000000000000000000000000000000) (15617973570355732783584192772978627/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0011.bracket0191 BracketBatch0012.bracket0192
  (29759126541212772566141388742390295179/312500000000000000000000000000000000000) (15617973570355732783584192772978627/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0191
