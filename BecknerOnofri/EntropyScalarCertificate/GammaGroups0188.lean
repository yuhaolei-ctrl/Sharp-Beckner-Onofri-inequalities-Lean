import BecknerOnofri.EntropyScalarCertificate.Bessel0235
import BecknerOnofri.EntropyScalarCertificate.Bessel0236
import BecknerOnofri.EntropyScalarCertificate.Bessel0606
import BecknerOnofri.EntropyScalarCertificate.Bessel0607
import BecknerOnofri.EntropyScalarCertificate.Brackets0094
import BecknerOnofri.EntropyScalarCertificate.Logs0188
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1504
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (1764458870883744366496922560470842058101/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1764458870883744366496922560470842058101/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (17654350001133106563945323385819907424043/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17654350001133106563945323385819907424043/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (35298938709970550228914548990528328005053/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35298938709970550228914548990528328005053/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0094.bracket1504 BracketBatch0094.bracket1505 (35298938709970550228914548990528328005053/20000000000000000000000000000000000000000) (338628357160053622210042077365568203211/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0094.bracket1504 BracketBatch0094.bracket1505
  (35298938709970550228914548990528328005053/20000000000000000000000000000000000000000) (338628357160053622210042077365568203211/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1504
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1505
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (441358750028327664098633084645497685601/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (441358750028327664098633084645497685601/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (1104007728807320168442044409089028766569/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1104007728807320168442044409089028766569/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (4414809207756278657377254241405545961143/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4414809207756278657377254241405545961143/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0094.bracket1505 BracketBatch0094.bracket1506 (4414809207756278657377254241405545961143/2500000000000000000000000000000000000000) (338893212142755218267100747809206251721/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0094.bracket1505 BracketBatch0094.bracket1506
  (4414809207756278657377254241405545961143/2500000000000000000000000000000000000000) (338893212142755218267100747809206251721/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1505
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1506
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (17664123660917122695072710545424460265101/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17664123660917122695072710545424460265101/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (2209238714169384703736506647805669511089/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2209238714169384703736506647805669511089/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (35338033374272200324964763727869816353813/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35338033374272200324964763727869816353813/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0094.bracket1506 BracketBatch0094.bracket1507 (35338033374272200324964763727869816353813/20000000000000000000000000000000000000000) (678316684159822107274762059257838893409/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0094.bracket1506 BracketBatch0094.bracket1507
  (35338033374272200324964763727869816353813/20000000000000000000000000000000000000000) (678316684159822107274762059257838893409/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1506
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1507
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (17673909713355077629892053182445356088709/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17673909713355077629892053182445356088709/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (17683708183678095012965166988295561220739/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17683708183678095012965166988295561220739/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (4419702237129146580357152521342614663681/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4419702237129146580357152521342614663681/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0094.bracket1507 BracketBatch0094.bracket1508 (4419702237129146580357152521342614663681/2500000000000000000000000000000000000000) (8485593684709924928637437963008620747/125000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0094.bracket1507 BracketBatch0094.bracket1508
  (4419702237129146580357152521342614663681/2500000000000000000000000000000000000000) (8485593684709924928637437963008620747/125000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1507
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1508
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (138153970184985117288790367096059072037/78125000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (138153970184985117288790367096059072037/78125000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (1769351909718304035415102989764911614937/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1769351909718304035415102989764911614937/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (17688613640430567683558098442972338685053/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17688613640430567683558098442972338685053/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0094.bracket1508 BracketBatch0094.bracket1509 (17688613640430567683558098442972338685053/10000000000000000000000000000000000000000) (679378856971742821995937683154224306707/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0094.bracket1508 BracketBatch0094.bracket1509
  (17688613640430567683558098442972338685053/10000000000000000000000000000000000000000) (679378856971742821995937683154224306707/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1508
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1509
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (17693519097183040354151029897649116149367/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17693519097183040354151029897649116149367/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (354066849584654511225976394603311403633/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (354066849584654511225976394603311403633/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (35396861576415765915449849627814686331017/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35396861576415765915449849627814686331017/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0094.bracket1509 BracketBatch0094.bracket1510 (35396861576415765915449849627814686331017/20000000000000000000000000000000000000000) (3399553857907766958610791743029477869/50000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0094.bracket1509 BracketBatch0094.bracket1510
  (35396861576415765915449849627814686331017/20000000000000000000000000000000000000000) (3399553857907766958610791743029477869/50000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1509
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1510
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (17703342479232725561298819730165570181647/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17703342479232725561298819730165570181647/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (17713178355256114216528609171906721491093/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17713178355256114216528609171906721491093/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (1770826041724441988891371445103614583637/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1770826041724441988891371445103614583637/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0094.bracket1510 BracketBatch0094.bracket1511 (1770826041724441988891371445103614583637/1000000000000000000000000000000000000000) (136088647888936335647626331297492083681/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0094.bracket1510 BracketBatch0094.bracket1511
  (1770826041724441988891371445103614583637/1000000000000000000000000000000000000000) (136088647888936335647626331297492083681/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1510
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1511
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (1771317835525611421652860917190672149109/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1771317835525611421652860917190672149109/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0236.rows BesselBatch0236.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (3544605350149705519857325354138624220637/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3544605350149705519857325354138624220637/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (1417448204240185672632609437703993703771/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1417448204240185672632609437703993703771/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0188.rows ScalarLogs0188.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0094.bracket1511 BracketBatch0094.bracket1512 (1417448204240185672632609437703993703771/800000000000000000000000000000000000000) (136195252280231586529285757245091579291/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0094.bracket1511 BracketBatch0094.bracket1512
  (1417448204240185672632609437703993703771/800000000000000000000000000000000000000) (136195252280231586529285757245091579291/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1511
