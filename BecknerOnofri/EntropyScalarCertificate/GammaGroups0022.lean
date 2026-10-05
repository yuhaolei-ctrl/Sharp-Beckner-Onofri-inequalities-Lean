import BecknerOnofri.EntropyScalarCertificate.Bessel0027
import BecknerOnofri.EntropyScalarCertificate.Bessel0028
import BecknerOnofri.EntropyScalarCertificate.Bessel0502
import BecknerOnofri.EntropyScalarCertificate.Bessel0503
import BecknerOnofri.EntropyScalarCertificate.Brackets0011
import BecknerOnofri.EntropyScalarCertificate.Logs0022
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0176
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (460441355310113945711103196916700590143/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (460441355310113945711103196916700590143/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (461454145806958308487342329291815609583/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (461454145806958308487342329291815609583/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (460947750558536127099222763104258099863/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (460947750558536127099222763104258099863/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0011.bracket0176 BracketBatch0011.bracket0177 (460947750558536127099222763104258099863/5000000000000000000000000000000000000000) (54862421465803464641685946818630813/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0011.bracket0176 BracketBatch0011.bracket0177
  (460947750558536127099222763104258099863/5000000000000000000000000000000000000000) (54862421465803464641685946818630813/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0176
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0177
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (922908291613916616974684658583631219163/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (922908291613916616974684658583631219163/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (924933985519016792978281408607831011503/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (924933985519016792978281408607831011503/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (923921138566466704976483033595731115333/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (923921138566466704976483033595731115333/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0011.bracket0177 BracketBatch0011.bracket0178 (923921138566466704976483033595731115333/10000000000000000000000000000000000000000) (13836748973472365954772390644457871/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0011.bracket0177 BracketBatch0011.bracket0178
  (923921138566466704976483033595731115333/10000000000000000000000000000000000000000) (13836748973472365954772390644457871/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0177
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0178
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (1849867971038033585956562817215662023/20000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1849867971038033585956562817215662023/20000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (463479896296471362361194074342800205731/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (463479896296471362361194074342800205731/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (925946889055979758850334778646715711481/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (925946889055979758850334778646715711481/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0011.bracket0178 BracketBatch0011.bracket0179 (925946889055979758850334778646715711481/10000000000000000000000000000000000000000) (11166951100742253190712652780426637/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0011.bracket0178 BracketBatch0011.bracket0179
  (925946889055979758850334778646715711481/10000000000000000000000000000000000000000) (11166951100742253190712652780426637/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0178
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0179
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (926959792592942724722388148685600411459/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (926959792592942724722388148685600411459/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (464492856546593341997704360151769685551/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (464492856546593341997704360151769685551/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (1855945505686129408717796868989139782561/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1855945505686129408717796868989139782561/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0011.bracket0179 BracketBatch0011.bracket0180 (1855945505686129408717796868989139782561/20000000000000000000000000000000000000000) (3520357143361550317986439477943627/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0011.bracket0179 BracketBatch0011.bracket0180
  (1855945505686129408717796868989139782561/20000000000000000000000000000000000000000) (3520357143361550317986439477943627/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0179
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0180
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (928985713093186683995408720303539371099/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (928985713093186683995408720303539371099/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (58188234204832443603383048365262397457/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (58188234204832443603383048365262397457/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (1859997460370505781649537494147737730411/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1859997460370505781649537494147737730411/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0011.bracket0180 BracketBatch0011.bracket0181 (1859997460370505781649537494147737730411/20000000000000000000000000000000000000000) (5681988629410324818566571472479919/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0011.bracket0180 BracketBatch0011.bracket0181
  (1859997460370505781649537494147737730411/20000000000000000000000000000000000000000) (5681988629410324818566571472479919/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0180
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0181
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (931011747277319097654128773844198359309/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (931011747277319097654128773844198359309/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (466518947701494368161813959032175273093/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (466518947701494368161813959032175273093/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (372809928536061566795551338381709781099/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (372809928536061566795551338381709781099/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0011.bracket0181 BracketBatch0011.bracket0182 (372809928536061566795551338381709781099/4000000000000000000000000000000000000000) (28658642783071963259272768837998551/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0011.bracket0181 BracketBatch0011.bracket0182
  (372809928536061566795551338381709781099/4000000000000000000000000000000000000000) (28658642783071963259272768837998551/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0181
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0182
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (933037895402988736323627918064350546183/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (933037895402988736323627918064350546183/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (187012831545584580645615065906885097009/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (187012831545584580645615065906885097009/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (467025513282727909887925811899694007807/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (467025513282727909887925811899694007807/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0011.bracket0182 BracketBatch0011.bracket0183 (467025513282727909887925811899694007807/5000000000000000000000000000000000000000) (57817926202875283480497684674606421/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0011.bracket0182 BracketBatch0011.bracket0183
  (467025513282727909887925811899694007807/5000000000000000000000000000000000000000) (57817926202875283480497684674606421/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0182
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0183
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (467532078863961451614037664767212742521/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (467532078863961451614037664767212742521/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0028.rows BesselBatch0028.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (937090534509927623152750005271073832419/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (937090534509927623152750005271073832419/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0503.rows BesselBatch0503.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (1872154692237850526380825334805499317461/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1872154692237850526380825334805499317461/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0022.rows ScalarLogs0022.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0011.bracket0183 BracketBatch0011.bracket0184 (1872154692237850526380825334805499317461/20000000000000000000000000000000000000000) (2916091116438191942112087992164531/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0011.bracket0183 BracketBatch0011.bracket0184
  (1872154692237850526380825334805499317461/20000000000000000000000000000000000000000) (2916091116438191942112087992164531/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0183
