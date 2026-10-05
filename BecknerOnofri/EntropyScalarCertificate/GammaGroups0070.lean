import BecknerOnofri.EntropyScalarCertificate.Bessel0087
import BecknerOnofri.EntropyScalarCertificate.Bessel0088
import BecknerOnofri.EntropyScalarCertificate.Bessel0532
import BecknerOnofri.EntropyScalarCertificate.Bessel0533
import BecknerOnofri.EntropyScalarCertificate.Brackets0035
import BecknerOnofri.EntropyScalarCertificate.Logs0070
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0560
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (854751073765017162986194834190245949693/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (854751073765017162986194834190245949693/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1711590924365170948067254835156349193107/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1711590924365170948067254835156349193107/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (3421093071895205274039644503536841092493/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3421093071895205274039644503536841092493/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0035.bracket0560 BracketBatch0035.bracket0561 (3421093071895205274039644503536841092493/20000000000000000000000000000000000000000) (634852455719921952201253208320164501/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0035.bracket0560 BracketBatch0035.bracket0561
  (3421093071895205274039644503536841092493/20000000000000000000000000000000000000000) (634852455719921952201253208320164501/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0560
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0561
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (106974432772823184254203427197271824569/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (106974432772823184254203427197271824569/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (1713679920599372945792049670210743189157/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1713679920599372945792049670210743189157/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (3425270844964543893859304505367092382261/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3425270844964543893859304505367092382261/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0035.bracket0561 BracketBatch0035.bracket0562 (3425270844964543893859304505367092382261/20000000000000000000000000000000000000000) (159472887273348571762127632777037829/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0035.bracket0561 BracketBatch0035.bracket0562
  (3425270844964543893859304505367092382261/20000000000000000000000000000000000000000) (159472887273348571762127632777037829/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0561
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0562
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (856839960299686472896024835105371594577/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (856839960299686472896024835105371594577/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (428942284133854811266364783063045946669/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (428942284133854811266364783063045946669/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (342944905713479219085750880246292697583/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (342944905713479219085750880246292697583/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0035.bracket0562 BracketBatch0035.bracket0563 (342944905713479219085750880246292697583/2000000000000000000000000000000000000000) (160235399416100677143713466238902837/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0035.bracket0562 BracketBatch0035.bracket0563
  (342944905713479219085750880246292697583/2000000000000000000000000000000000000000) (160235399416100677143713466238902837/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0562
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0563
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1715769136535419245065459132252183786673/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1715769136535419245065459132252183786673/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (1717858572476252384032402922297476669457/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1717858572476252384032402922297476669457/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (343362770901167162909786205454966045613/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (343362770901167162909786205454966045613/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0035.bracket0563 BracketBatch0035.bracket0564 (343362770901167162909786205454966045613/2000000000000000000000000000000000000000) (644002628190821516513349150674641333/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0035.bracket0563 BracketBatch0035.bracket0564
  (343362770901167162909786205454966045613/2000000000000000000000000000000000000000) (644002628190821516513349150674641333/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0563
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0564
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (858929286238126192016201461148738334727/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (858929286238126192016201461148738334727/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (1719948228724978781752369137556989089641/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1719948228724978781752369137556989089641/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (687561360240246233156954411970893151819/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (687561360240246233156954411970893151819/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0035.bracket0564 BracketBatch0035.bracket0565 (687561360240246233156954411970893151819/4000000000000000000000000000000000000000) (647074667465980940944331147150490127/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0035.bracket0564 BracketBatch0035.bracket0565
  (687561360240246233156954411970893151819/4000000000000000000000000000000000000000) (647074667465980940944331147150490127/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0564
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0565
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (859974114362489390876184568778494544819/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (859974114362489390876184568778494544819/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1722038105584869007191519286244417844013/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1722038105584869007191519286244417844013/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (3441986334309847788943888423801406933651/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3441986334309847788943888423801406933651/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0035.bracket0565 BracketBatch0035.bracket0566 (3441986334309847788943888423801406933651/20000000000000000000000000000000000000000) (325078871159340667053950045448797773/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0035.bracket0565 BracketBatch0035.bracket0566
  (3441986334309847788943888423801406933651/20000000000000000000000000000000000000000) (325078871159340667053950045448797773/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0565
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0566
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (172203810558486900719151928624441784401/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (172203810558486900719151928624441784401/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (344825640671871609703833615329520863663/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (344825640671871609703833615329520863663/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (137846652357769082228427494515680886493/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (137846652357769082228427494515680886493/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0035.bracket0566 BracketBatch0035.bracket0567 (137846652357769082228427494515680886493/800000000000000000000000000000000000000) (326625939806603692214870033731812993/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0035.bracket0566 BracketBatch0035.bracket0567
  (137846652357769082228427494515680886493/800000000000000000000000000000000000000) (326625939806603692214870033731812993/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0566
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0567
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (215516025419919756064896009580950539789/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (215516025419919756064896009580950539789/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1726218522352045582709242449459750136449/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1726218522352045582709242449459750136449/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (3450346725711403631228410526107354454761/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3450346725711403631228410526107354454761/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0070.rows ScalarLogs0070.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0035.bracket0567 BracketBatch0035.bracket0568 (3450346725711403631228410526107354454761/20000000000000000000000000000000000000000) (656357106249342352782246648519396389/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0035.bracket0567 BracketBatch0035.bracket0568
  (3450346725711403631228410526107354454761/20000000000000000000000000000000000000000) (656357106249342352782246648519396389/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0567
