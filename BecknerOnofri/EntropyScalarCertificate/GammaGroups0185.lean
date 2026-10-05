import BecknerOnofri.EntropyScalarCertificate.Bessel0231
import BecknerOnofri.EntropyScalarCertificate.Bessel0232
import BecknerOnofri.EntropyScalarCertificate.Bessel0604
import BecknerOnofri.EntropyScalarCertificate.Bessel0605
import BecknerOnofri.EntropyScalarCertificate.Brackets0092
import BecknerOnofri.EntropyScalarCertificate.Brackets0093
import BecknerOnofri.EntropyScalarCertificate.Logs0185
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1480
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (17413963640234878161054582708237489628257/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17413963640234878161054582708237489628257/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (17423435495592005097684164375444130588073/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17423435495592005097684164375444130588073/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (3483739913582688325873874708368162021633/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3483739913582688325873874708368162021633/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0092.bracket1480 BracketBatch0092.bracket1481 (3483739913582688325873874708368162021633/2000000000000000000000000000000000000000) (332353253616626563284500443410707961441/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0092.bracket1480 BracketBatch0092.bracket1481
  (3483739913582688325873874708368162021633/2000000000000000000000000000000000000000) (332353253616626563284500443410707961441/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1480
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1481
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (1742343549559200509768416437544413058807/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1742343549559200509768416437544413058807/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1743291913360768378187343043227469817851/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1743291913360768378187343043227469817851/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (1742817731459984443977879740385941438329/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1742817731459984443977879740385941438329/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0092.bracket1481 BracketBatch0092.bracket1482 (1742817731459984443977879740385941438329/1000000000000000000000000000000000000000) (33261163274751269126542908401644331163/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0092.bracket1481 BracketBatch0092.bracket1482
  (1742817731459984443977879740385941438329/1000000000000000000000000000000000000000) (33261163274751269126542908401644331163/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1481
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1482
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (17432919133607683781873430432274698178507/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17432919133607683781873430432274698178507/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (17442414577933852721981840551904786682479/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17442414577933852721981840551904786682479/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (17437666855770768251927635492089742430493/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17437666855770768251927635492089742430493/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0092.bracket1482 BracketBatch0092.bracket1483 (17437666855770768251927635492089742430493/10000000000000000000000000000000000000000) (83217569264654457684455747570655899793/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0092.bracket1482 BracketBatch0092.bracket1483
  (17437666855770768251927635492089742430493/10000000000000000000000000000000000000000) (83217569264654457684455747570655899793/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1482
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1483
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (4360603644483463180495460137976196670619/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4360603644483463180495460137976196670619/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (3490384370456662328486439178946472617951/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3490384370456662328486439178946472617951/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (34894336430217164364414036446637149772231/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34894336430217164364414036446637149772231/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0092.bracket1483 BracketBatch0092.bracket1484 (34894336430217164364414036446637149772231/20000000000000000000000000000000000000000) (133251674779397376778308413438247765537/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0092.bracket1483 BracketBatch0092.bracket1484
  (34894336430217164364414036446637149772231/20000000000000000000000000000000000000000) (133251674779397376778308413438247765537/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1483
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1484
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (2181490231535413955304024486841545386219/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2181490231535413955304024486841545386219/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (8730720490214954208263726332846033480863/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8730720490214954208263726332846033480863/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (17456681416356610029479824280212215025739/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17456681416356610029479824280212215025739/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0092.bracket1484 BracketBatch0092.bracket1485 (17456681416356610029479824280212215025739/10000000000000000000000000000000000000000) (666776725632874649171539550763664977341/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0092.bracket1484 BracketBatch0092.bracket1485
  (17456681416356610029479824280212215025739/10000000000000000000000000000000000000000) (666776725632874649171539550763664977341/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1484
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1485
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (17461440980429908416527452665692066961723/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17461440980429908416527452665692066961723/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (17470971986208726668225590461725458899449/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17470971986208726668225590461725458899449/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (8733103241659658771188260781854381465293/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8733103241659658771188260781854381465293/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0092.bracket1485 BracketBatch0092.bracket1486 (8733103241659658771188260781854381465293/5000000000000000000000000000000000000000) (667295610124990179065590321429276074721/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0092.bracket1485 BracketBatch0092.bracket1486
  (8733103241659658771188260781854381465293/5000000000000000000000000000000000000000) (667295610124990179065590321429276074721/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1485
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1486
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (8735485993104363334112795230862729449723/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8735485993104363334112795230862729449723/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (2185064361689534255710079327728834781829/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2185064361689534255710079327728834781829/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (17475743439862500356953112541778068577039/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17475743439862500356953112541778068577039/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0092.bracket1486 BracketBatch0092.bracket1487 (17475743439862500356953112541778068577039/10000000000000000000000000000000000000000) (333907514087461633515245070700686792079/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0092.bracket1486 BracketBatch0092.bracket1487
  (17475743439862500356953112541778068577039/10000000000000000000000000000000000000000) (333907514087461633515245070700686792079/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1486
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1487
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (17480514893516274045680634621830678254629/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17480514893516274045680634621830678254629/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (8745034863155335584686008903695530254191/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8745034863155335584686008903695530254191/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (34970584619826945215052652429221738763011/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34970584619826945215052652429221738763011/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0185.rows ScalarLogs0185.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0092.bracket1487 BracketBatch0093.bracket1488 (34970584619826945215052652429221738763011/20000000000000000000000000000000000000000) (334167490292882616747595973712820582107/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0092.bracket1487 BracketBatch0093.bracket1488
  (34970584619826945215052652429221738763011/20000000000000000000000000000000000000000) (334167490292882616747595973712820582107/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1487
