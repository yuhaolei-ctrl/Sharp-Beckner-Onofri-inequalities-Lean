import BecknerOnofri.EntropyScalarCertificate.Bessel0421
import BecknerOnofri.EntropyScalarCertificate.Bessel0422
import BecknerOnofri.EntropyScalarCertificate.Bessel0699
import BecknerOnofri.EntropyScalarCertificate.Bessel0700
import BecknerOnofri.EntropyScalarCertificate.Brackets0168
import BecknerOnofri.EntropyScalarCertificate.Brackets0169
import BecknerOnofri.EntropyScalarCertificate.Logs0337
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2696
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (688070074772511002640489098885548869323829/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (688070074772511002640489098885548869323829/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (691864584571280068589038266840281043959913/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (691864584571280068589038266840281043959913/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (689967329671895535614763682862914956641871/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (689967329671895535614763682862914956641871/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0168.bracket2696 BracketBatch0168.bracket2697 (689967329671895535614763682862914956641871/10000000000000000000000000000000000000000) (5513358058601653751070002810583887111877/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0168.bracket2696 BracketBatch0168.bracket2697
  (689967329671895535614763682862914956641871/10000000000000000000000000000000000000000) (5513358058601653751070002810583887111877/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2696
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2697
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (69186458457128006858903826684028104395991/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (69186458457128006858903826684028104395991/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (695701256018326993300165806083916319949587/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (695701256018326993300165806083916319949587/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (1387565840589607061889204072924197363909497/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1387565840589607061889204072924197363909497/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0168.bracket2697 BracketBatch0168.bracket2698 (1387565840589607061889204072924197363909497/20000000000000000000000000000000000000000) (5521347058761304084880945846901879130197/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0168.bracket2697 BracketBatch0168.bracket2698
  (1387565840589607061889204072924197363909497/20000000000000000000000000000000000000000) (5521347058761304084880945846901879130197/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2697
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2698
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (43481328501145437081260362880244769996849/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (43481328501145437081260362880244769996849/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (139916159146677790572492276497644955177447/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (139916159146677790572492276497644955177447/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (1395282051751715946162627188572141095836819/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1395282051751715946162627188572141095836819/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0168.bracket2698 BracketBatch0168.bracket2699 (1395282051751715946162627188572141095836819/20000000000000000000000000000000000000000) (1382344016126679670857718201901601339387/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0168.bracket2698 BracketBatch0168.bracket2699
  (1395282051751715946162627188572141095836819/20000000000000000000000000000000000000000) (1382344016126679670857718201901601339387/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2698
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2699
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (5465474966667101194237979550689256061619/78125000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5465474966667101194237979550689256061619/78125000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (2748062211778509223789001727872514246739/39062500000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2748062211778509223789001727872514246739/39062500000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (10961599390224119641815983006434284555097/156250000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10961599390224119641815983006434284555097/156250000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0168.bracket2699 BracketBatch0168.bracket2700 (10961599390224119641815983006434284555097/156250000000000000000000000000000000000) (692180673647231761902625922267692326063/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0168.bracket2699 BracketBatch0168.bracket2700
  (10961599390224119641815983006434284555097/156250000000000000000000000000000000000) (692180673647231761902625922267692326063/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2699
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2700
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (703503926215298361289984442335363647165181/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (703503926215298361289984442335363647165181/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (176867846572636220720605400391515811930563/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (176867846572636220720605400391515811930563/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (1410975312505843244172406043901426894887433/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1410975312505843244172406043901426894887433/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0168.bracket2700 BracketBatch0168.bracket2701 (1410975312505843244172406043901426894887433/20000000000000000000000000000000000000000) (554555534770878681930798834525822726661/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0168.bracket2700 BracketBatch0168.bracket2701
  (1410975312505843244172406043901426894887433/20000000000000000000000000000000000000000) (554555534770878681930798834525822726661/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2700
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2701
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (707471386290544882882421601566063247722249/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (707471386290544882882421601566063247722249/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (355741965788564665685128812488240967440381/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (355741965788564665685128812488240967440381/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (1418955317867674214252679226542545182603011/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1418955317867674214252679226542545182603011/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0168.bracket2701 BracketBatch0168.bracket2702 (1418955317867674214252679226542545182603011/20000000000000000000000000000000000000000) (5553706256541219550740309512926584792399/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0168.bracket2701 BracketBatch0168.bracket2702
  (1418955317867674214252679226542545182603011/20000000000000000000000000000000000000000) (5553706256541219550740309512926584792399/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2701
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2702
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (711483931577129331370257624976481934880759/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (711483931577129331370257624976481934880759/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (143108466992864226263272106027308339303273/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (143108466992864226263272106027308339303273/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (356756566635362615671654538778255907849281/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (356756566635362615671654538778255907849281/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0168.bracket2702 BracketBatch0168.bracket2703 (356756566635362615671654538778255907849281/5000000000000000000000000000000000000000) (5561898433530727499454694376592482768967/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0168.bracket2702 BracketBatch0168.bracket2703
  (356756566635362615671654538778255907849281/5000000000000000000000000000000000000000) (5561898433530727499454694376592482768967/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2702
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2703
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (357771167482160565658180265068270848258181/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (357771167482160565658180265068270848258181/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (89955923388619892531945085718389500437899/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (89955923388619892531945085718389500437899/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (717594861036640135785960607941828850009777/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (717594861036640135785960607941828850009777/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0337.rows ScalarLogs0337.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0168.bracket2703 BracketBatch0169.bracket2704 (717594861036640135785960607941828850009777/10000000000000000000000000000000000000000) (5570132197845278468743369767341910577901/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0168.bracket2703 BracketBatch0169.bracket2704
  (717594861036640135785960607941828850009777/10000000000000000000000000000000000000000) (5570132197845278468743369767341910577901/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2703
