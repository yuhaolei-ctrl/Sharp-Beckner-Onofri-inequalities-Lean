import BecknerOnofri.EntropyScalarCertificate.Bessel0391
import BecknerOnofri.EntropyScalarCertificate.Bessel0392
import BecknerOnofri.EntropyScalarCertificate.Bessel0684
import BecknerOnofri.EntropyScalarCertificate.Bessel0685
import BecknerOnofri.EntropyScalarCertificate.Brackets0156
import BecknerOnofri.EntropyScalarCertificate.Brackets0157
import BecknerOnofri.EntropyScalarCertificate.Logs0313
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2504
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (167744446868608515188538504494811136759679/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (167744446868608515188538504494811136759679/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (84096224819162950030631526147545383169901/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (84096224819162950030631526147545383169901/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (335936896506934415249801556789901903099481/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (335936896506934415249801556789901903099481/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0156.bracket2504 BracketBatch0156.bracket2505 (335936896506934415249801556789901903099481/10000000000000000000000000000000000000000) (278752791205596155870325112163278198879/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0156.bracket2504 BracketBatch0156.bracket2505
  (335936896506934415249801556789901903099481/10000000000000000000000000000000000000000) (278752791205596155870325112163278198879/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2504
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2505
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (336384899276651800122526104590181532679601/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (336384899276651800122526104590181532679601/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (337285722263726422262846291908789041932989/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (337285722263726422262846291908789041932989/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (67367062154037822238537239649897057461259/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (67367062154037822238537239649897057461259/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0156.bracket2505 BracketBatch0156.bracket2506 (67367062154037822238537239649897057461259/2000000000000000000000000000000000000000) (4463924483852451554231986193563539915349/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0156.bracket2505 BracketBatch0156.bracket2506
  (67367062154037822238537239649897057461259/2000000000000000000000000000000000000000) (4463924483852451554231986193563539915349/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2505
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2506
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (168642861131863211131423145954394520966493/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (168642861131863211131423145954394520966493/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (84547850413377275239218954729630896454759/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (84547850413377275239218954729630896454759/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (337738561958617761609861055413656313876011/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (337738561958617761609861055413656313876011/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0156.bracket2506 BracketBatch0156.bracket2507 (337738561958617761609861055413656313876011/10000000000000000000000000000000000000000) (1116953807841757131025493715705540468103/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0156.bracket2506 BracketBatch0156.bracket2507
  (337738561958617761609861055413656313876011/10000000000000000000000000000000000000000) (1116953807841757131025493715705540468103/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2506
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2507
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (338191401653509100956875818918523585819033/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (338191401653509100956875818918523585819033/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (16955098841110196187454118043308483273373/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16955098841110196187454118043308483273373/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (677293378475713024705958179784693251286493/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (677293378475713024705958179784693251286493/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0156.bracket2507 BracketBatch0156.bracket2508 (677293378475713024705958179784693251286493/20000000000000000000000000000000000000000) (17467644675620086405875635683087330561/39062500000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0156.bracket2507 BracketBatch0156.bracket2508
  (677293378475713024705958179784693251286493/20000000000000000000000000000000000000000) (17467644675620086405875635683087330561/39062500000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2507
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2508
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (339101976822203923749082360866169665467457/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (339101976822203923749082360866169665467457/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (68003497514571461969597846843531185622679/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (68003497514571461969597846843531185622679/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (169779866098765308399267898770956398395213/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (169779866098765308399267898770956398395213/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0156.bracket2508 BracketBatch0156.bracket2509 (169779866098765308399267898770956398395213/5000000000000000000000000000000000000000) (4475630004758935868997698368416260094073/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0156.bracket2508 BracketBatch0156.bracket2509
  (169779866098765308399267898770956398395213/5000000000000000000000000000000000000000) (4475630004758935868997698368416260094073/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2508
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2509
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (21251092973303581865499327138603495507087/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21251092973303581865499327138603495507087/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (340937974141157498322189509351361635673087/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (340937974141157498322189509351361635673087/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (680955461714014808170178743569017563786479/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (680955461714014808170178743569017563786479/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0156.bracket2509 BracketBatch0156.bracket2510 (680955461714014808170178743569017563786479/20000000000000000000000000000000000000000) (2239777096866576390701546281081980772733/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0156.bracket2509 BracketBatch0156.bracket2510
  (680955461714014808170178743569017563786479/20000000000000000000000000000000000000000) (2239777096866576390701546281081980772733/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2509
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2510
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (85234493535289374580547377337840408918271/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (85234493535289374580547377337840408918271/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (170931738600664425408640377820147796046597/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (170931738600664425408640377820147796046597/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (341400725671243174569735132495828613883139/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (341400725671243174569735132495828613883139/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0156.bracket2510 BracketBatch0156.bracket2511 (341400725671243174569735132495828613883139/10000000000000000000000000000000000000000) (1120872415825406238151273595969997314323/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0156.bracket2510 BracketBatch0156.bracket2511
  (341400725671243174569735132495828613883139/10000000000000000000000000000000000000000) (1120872415825406238151273595969997314323/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2510
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2511
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (341863477201328850817280755640295592093191/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (341863477201328850817280755640295592093191/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (171397018936061391093098518730486316267927/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (171397018936061391093098518730486316267927/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (136931503014690326600695558620253644925809/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (136931503014690326600695558620253644925809/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0313.rows ScalarLogs0313.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0156.bracket2511 BracketBatch0157.bracket2512 (136931503014690326600695558620253644925809/4000000000000000000000000000000000000000) (1121859118335951327649780939624500318509/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0156.bracket2511 BracketBatch0157.bracket2512
  (136931503014690326600695558620253644925809/4000000000000000000000000000000000000000) (1121859118335951327649780939624500318509/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2511
