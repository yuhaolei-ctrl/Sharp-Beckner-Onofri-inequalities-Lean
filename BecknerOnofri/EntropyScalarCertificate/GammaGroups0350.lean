import BecknerOnofri.EntropyScalarCertificate.Bessel0437
import BecknerOnofri.EntropyScalarCertificate.Bessel0438
import BecknerOnofri.EntropyScalarCertificate.Bessel0707
import BecknerOnofri.EntropyScalarCertificate.Bessel0708
import BecknerOnofri.EntropyScalarCertificate.Brackets0175
import BecknerOnofri.EntropyScalarCertificate.Logs0350
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2800
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (948224679963041216122882216443342822018133/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (948224679963041216122882216443342822018133/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (475010788454214707780005093245641506742111/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (475010788454214707780005093245641506742111/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (379649251374294126336578480586925167100471/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (379649251374294126336578480586925167100471/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0175.bracket2800 BracketBatch0175.bracket2801 (379649251374294126336578480586925167100471/4000000000000000000000000000000000000000) (6031691861538074472450586305476868068711/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0175.bracket2800 BracketBatch0175.bracket2801
  (379649251374294126336578480586925167100471/4000000000000000000000000000000000000000) (6031691861538074472450586305476868068711/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2800
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2801
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (950021576908429415560010186491283013484219/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (950021576908429415560010186491283013484219/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (951825306197959647240721134281254623489921/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (951825306197959647240721134281254623489921/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (95092344155319453140036566038626881848707/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (95092344155319453140036566038626881848707/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0175.bracket2801 BracketBatch0175.bracket2802 (95092344155319453140036566038626881848707/1000000000000000000000000000000000000000) (6034603717996928464078543350435230543239/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0175.bracket2801 BracketBatch0175.bracket2802
  (95092344155319453140036566038626881848707/1000000000000000000000000000000000000000) (6034603717996928464078543350435230543239/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2801
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2802
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (475912653098979823620360567140627311744959/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (475912653098979823620360567140627311744959/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (190727181374719408769562533715377534669557/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (190727181374719408769562533715377534669557/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (1905461213071556691088533802858142296837703/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1905461213071556691088533802858142296837703/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0175.bracket2802 BracketBatch0175.bracket2803 (1905461213071556691088533802858142296837703/20000000000000000000000000000000000000000) (6037521199422579100565658893006649333301/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0175.bracket2802 BracketBatch0175.bracket2803
  (1905461213071556691088533802858142296837703/20000000000000000000000000000000000000000) (6037521199422579100565658893006649333301/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2802
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2803
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (476817953436798521923906334288443836673891/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (476817953436798521923906334288443836673891/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (955453418275337006358561767038764188556671/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (955453418275337006358561767038764188556671/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (1909089325148934050206374435615651861904453/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1909089325148934050206374435615651861904453/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0175.bracket2803 BracketBatch0175.bracket2804 (1909089325148934050206374435615651861904453/20000000000000000000000000000000000000000) (3020222163272201826441222146032668564439/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0175.bracket2803 BracketBatch0175.bracket2804
  (1909089325148934050206374435615651861904453/20000000000000000000000000000000000000000) (3020222163272201826441222146032668564439/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2803
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2804
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (238863354568834251589640441759691047139167/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (238863354568834251589640441759691047139167/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (239319470011013610447828096780811473826427/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (239319470011013610447828096780811473826427/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (239091412289923931018734269270251260482797/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (239091412289923931018734269270251260482797/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0175.bracket2804 BracketBatch0175.bracket2805 (239091412289923931018734269270251260482797/2500000000000000000000000000000000000000) (6043373120203295883940658697297498735079/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0175.bracket2804 BracketBatch0175.bracket2805
  (239091412289923931018734269270251260482797/2500000000000000000000000000000000000000) (6043373120203295883940658697297498735079/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2804
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2805
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (191455576008810888358262477424649179061141/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (191455576008810888358262477424649179061141/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (239777333031096437702804814747839394021827/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (239777333031096437702804814747839394021827/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (1916387212168440192602531646114603471393013/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1916387212168440192602531646114603471393013/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0175.bracket2805 BracketBatch0175.bracket2806 (1916387212168440192602531646114603471393013/20000000000000000000000000000000000000000) (6046307601352437317327155993647033386647/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0175.bracket2805 BracketBatch0175.bracket2806
  (1916387212168440192602531646114603471393013/20000000000000000000000000000000000000000) (6046307601352437317327155993647033386647/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2805
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2806
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (191821866424877150162243851798271515217461/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (191821866424877150162243851798271515217461/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (60059238422977750325778086439127007190987/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (60059238422977750325778086439127007190987/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (1920057146892029756023668642017389691143097/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1920057146892029756023668642017389691143097/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0175.bracket2806 BracketBatch0175.bracket2807 (1920057146892029756023668642017389691143097/20000000000000000000000000000000000000000) (241969911642322992619941679620798942601/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0175.bracket2806 BracketBatch0175.bracket2807
  (1920057146892029756023668642017389691143097/20000000000000000000000000000000000000000) (241969911642322992619941679620798942601/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2806
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2807
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (960947814767644005212449383026032115055789/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (960947814767644005212449383026032115055789/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0438.rows BesselBatch0438.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (962793368534767762063639701057535898692277/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (962793368534767762063639701057535898692277/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (961870591651205883638044542041784006874033/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (961870591651205883638044542041784006874033/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0350.rows ScalarLogs0350.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0175.bracket2807 BracketBatch0175.bracket2808 (961870591651205883638044542041784006874033/10000000000000000000000000000000000000000) (6052193710500304523783026368444008115217/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0175.bracket2807 BracketBatch0175.bracket2808
  (961870591651205883638044542041784006874033/10000000000000000000000000000000000000000) (6052193710500304523783026368444008115217/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2807
