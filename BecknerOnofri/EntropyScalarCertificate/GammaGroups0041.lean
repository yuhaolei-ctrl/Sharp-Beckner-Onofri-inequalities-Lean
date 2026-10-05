import BecknerOnofri.EntropyScalarCertificate.Bessel0051
import BecknerOnofri.EntropyScalarCertificate.Bessel0052
import BecknerOnofri.EntropyScalarCertificate.Bessel0514
import BecknerOnofri.EntropyScalarCertificate.Bessel0515
import BecknerOnofri.EntropyScalarCertificate.Brackets0020
import BecknerOnofri.EntropyScalarCertificate.Brackets0021
import BecknerOnofri.EntropyScalarCertificate.Logs0041
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0328
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1230216285245582355783547590549037055197/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1230216285245582355783547590549037055197/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (616131015858028332086551541275736747743/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (616131015858028332086551541275736747743/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (2462478316961639019956650673100510550683/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2462478316961639019956650673100510550683/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0020.bracket0328 BracketBatch0020.bracket0329 (2462478316961639019956650673100510550683/20000000000000000000000000000000000000000) (173780639811757219525262021041719093/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0020.bracket0328 BracketBatch0020.bracket0329
  (2462478316961639019956650673100510550683/20000000000000000000000000000000000000000) (173780639811757219525262021041719093/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0328
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0329
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (1232262031716056664173103082551473495483/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1232262031716056664173103082551473495483/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (617153965615436946544774147182350859041/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (617153965615436946544774147182350859041/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (493313992589386111452530275383235042713/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (493313992589386111452530275383235042713/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0020.bracket0329 BracketBatch0020.bracket0330 (493313992589386111452530275383235042713/4000000000000000000000000000000000000000) (17492822873486650736639416262500623/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0020.bracket0329 BracketBatch0020.bracket0330
  (493313992589386111452530275383235042713/4000000000000000000000000000000000000000) (17492822873486650736639416262500623/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0329
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0330
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (1234307931230873893089548294364701718079/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1234307931230873893089548294364701718079/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (618176992030772869416624777016559351729/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (618176992030772869416624777016559351729/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (2470661915292419631922797848397820421537/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2470661915292419631922797848397820421537/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0020.bracket0330 BracketBatch0020.bracket0331 (2470661915292419631922797848397820421537/20000000000000000000000000000000000000000) (176081496178985140924651622875619961/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0020.bracket0330 BracketBatch0020.bracket0331
  (2470661915292419631922797848397820421537/20000000000000000000000000000000000000000) (176081496178985140924651622875619961/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0330
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0331
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (247270796812309147766649910806623740691/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (247270796812309147766649910806623740691/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (619200095239846114856308958911788188393/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (619200095239846114856308958911788188393/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (2474754174541237968545867471856695080241/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2474754174541237968545867471856695080241/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0020.bracket0331 BracketBatch0020.bracket0332 (2474754174541237968545867471856695080241/20000000000000000000000000000000000000000) (177240461016348494270994459048532343/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0020.bracket0331 BracketBatch0020.bracket0332
  (2474754174541237968545867471856695080241/20000000000000000000000000000000000000000) (177240461016348494270994459048532343/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0331
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0332
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (1238400190479692229712617917823576376783/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1238400190479692229712617917823576376783/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (620223275378520969311179236554444790053/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (620223275378520969311179236554444790053/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (2478846741236734168334976390932465956889/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2478846741236734168334976390932465956889/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0020.bracket0332 BracketBatch0020.bracket0333 (2478846741236734168334976390932465956889/20000000000000000000000000000000000000000) (178405142151917224913106009453216047/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0020.bracket0332 BracketBatch0020.bracket0333
  (2478846741236734168334976390932465956889/20000000000000000000000000000000000000000) (178405142151917224913106009453216047/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0332
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0333
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1240446550757041938622358473108889580103/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1240446550757041938622358473108889580103/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (621246532582716097904679412156982997629/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (621246532582716097904679412156982997629/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (2482939615922474134431717297422855575361/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2482939615922474134431717297422855575361/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0020.bracket0333 BracketBatch0020.bracket0334 (2482939615922474134431717297422855575361/20000000000000000000000000000000000000000) (179575558523386825446696601741238761/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0020.bracket0333 BracketBatch0020.bracket0334
  (2482939615922474134431717297422855575361/20000000000000000000000000000000000000000) (179575558523386825446696601741238761/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0333
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0334
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (248498613033086439161871764862793199051/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (248498613033086439161871764862793199051/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (1244539733976809301826632787488946825671/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1244539733976809301826632787488946825671/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (1243516399571120748817995805901456410463/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1243516399571120748817995805901456410463/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0020.bracket0334 BracketBatch0020.bracket0335 (1243516399571120748817995805901456410463/10000000000000000000000000000000000000000) (9037586455059859668545685677652813/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0020.bracket0334 BracketBatch0020.bracket0335
  (1243516399571120748817995805901456410463/10000000000000000000000000000000000000000) (9037586455059859668545685677652813/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0334
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0335
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (311134933494202325456658196872236706417/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (311134933494202325456658196872236706417/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (311646639365807185168933979834522378319/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (311646639365807185168933979834522378319/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (9730962075937648603524877761043110699/78125000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9730962075937648603524877761043110699/78125000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0041.rows ScalarLogs0041.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0020.bracket0335 BracketBatch0021.bracket0336 (9730962075937648603524877761043110699/78125000000000000000000000000000000000) (90966836444271109540711013501860813/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0020.bracket0335 BracketBatch0021.bracket0336
  (9730962075937648603524877761043110699/78125000000000000000000000000000000000) (90966836444271109540711013501860813/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0335
