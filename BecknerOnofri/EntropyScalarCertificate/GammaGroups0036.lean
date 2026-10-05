import BecknerOnofri.EntropyScalarCertificate.Bessel0045
import BecknerOnofri.EntropyScalarCertificate.Bessel0046
import BecknerOnofri.EntropyScalarCertificate.Bessel0511
import BecknerOnofri.EntropyScalarCertificate.Bessel0512
import BecknerOnofri.EntropyScalarCertificate.Brackets0018
import BecknerOnofri.EntropyScalarCertificate.Logs0036
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0288
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (229701763794685801696816238716073082697/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (229701763794685801696816238716073082697/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (575274332546079935366834667196467272457/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (575274332546079935366834667196467272457/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (2299057484065588879217750527973299958399/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2299057484065588879217750527973299958399/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0018.bracket0288 BracketBatch0018.bracket0289 (2299057484065588879217750527973299958399/20000000000000000000000000000000000000000) (16540105656780657255435320080596947/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0018.bracket0288 BracketBatch0018.bracket0289
  (2299057484065588879217750527973299958399/20000000000000000000000000000000000000000) (16540105656780657255435320080596947/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0288
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0289
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (1150548665092159870733669334392934544911/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1150548665092159870733669334392934544911/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (576294326740590179671805360859191467007/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (576294326740590179671805360859191467007/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (92125492742933609203091202244452699157/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (92125492742933609203091202244452699157/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0018.bracket0289 BracketBatch0018.bracket0290 (92125492742933609203091202244452699157/800000000000000000000000000000000000000) (33314098510721348476473259271640071/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0018.bracket0289 BracketBatch0018.bracket0290
  (92125492742933609203091202244452699157/800000000000000000000000000000000000000) (33314098510721348476473259271640071/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0289
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0290
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (1152588653481180359343610721718382934011/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1152588653481180359343610721718382934011/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (230925756881568220212221281524972376847/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (230925756881568220212221281524972376847/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (1153608718944510730202358564671622409123/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1153608718944510730202358564671622409123/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0018.bracket0290 BracketBatch0018.bracket0291 (1153608718944510730202358564671622409123/10000000000000000000000000000000000000000) (8387305824401657506344991465728849/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0018.bracket0290 BracketBatch0018.bracket0291
  (1153608718944510730202358564671622409123/10000000000000000000000000000000000000000) (8387305824401657506344991465728849/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0290
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0291
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (144328598050980137632638300953107735529/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (144328598050980137632638300953107735529/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (289167264534898175168010608548032000429/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (289167264534898175168010608548032000429/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (577824460636858450433287210454247471487/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (577824460636858450433287210454247471487/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0018.bracket0291 BracketBatch0018.bracket0292 (577824460636858450433287210454247471487/5000000000000000000000000000000000000000) (33785590066929536189648694005684681/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0018.bracket0291 BracketBatch0018.bracket0292
  (577824460636858450433287210454247471487/5000000000000000000000000000000000000000) (33785590066929536189648694005684681/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0291
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0292
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (1156669058139592700672042434192128001713/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1156669058139592700672042434192128001713/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (231741894988797189281621137146784697677/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (231741894988797189281621137146784697677/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (1157689266541789323540074059963025745049/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1157689266541789323540074059963025745049/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0018.bracket0292 BracketBatch0018.bracket0293 (1157689266541789323540074059963025745049/10000000000000000000000000000000000000000) (4252900402436491747791790572612619/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0018.bracket0292 BracketBatch0018.bracket0293
  (1157689266541789323540074059963025745049/10000000000000000000000000000000000000000) (4252900402436491747791790572612619/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0292
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0293
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (579354737471992973204052842866961744191/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (579354737471992973204052842866961744191/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (1160750035088672015525373073052289857149/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1160750035088672015525373073052289857149/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (2319459510032657961933478758786213345531/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2319459510032657961933478758786213345531/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0018.bracket0293 BracketBatch0018.bracket0294 (2319459510032657961933478758786213345531/20000000000000000000000000000000000000000) (68524134328374778728896456572274741/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0018.bracket0293 BracketBatch0018.bracket0294
  (2319459510032657961933478758786213345531/20000000000000000000000000000000000000000) (68524134328374778728896456572274741/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0293
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0294
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0045.rows BesselBatch0045.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (580375017544336007762686536526144928573/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (580375017544336007762686536526144928573/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (14534884235517533500684590930629784261/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14534884235517533500684590930629784261/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (1161770386965037347790070173751336299013/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1161770386965037347790070173751336299013/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0018.bracket0294 BracketBatch0018.bracket0295 (1161770386965037347790070173751336299013/10000000000000000000000000000000000000000) (69004372636006761246743622413421041/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0018.bracket0294 BracketBatch0018.bracket0295
  (1161770386965037347790070173751336299013/10000000000000000000000000000000000000000) (69004372636006761246743622413421041/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0294
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0295
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (1162790738841402680054767274450382740877/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1162790738841402680054767274450382740877/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (145603948308753814090596600029238890149/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (145603948308753814090596600029238890149/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0511.rows BesselBatch0511.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (2327622325311433192779540074684293862069/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2327622325311433192779540074684293862069/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0036.rows ScalarLogs0036.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0018.bracket0295 BracketBatch0018.bracket0296 (2327622325311433192779540074684293862069/20000000000000000000000000000000000000000) (17371782553011758082911097185201527/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0018.bracket0295 BracketBatch0018.bracket0296
  (2327622325311433192779540074684293862069/20000000000000000000000000000000000000000) (17371782553011758082911097185201527/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0295
