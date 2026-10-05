import BecknerOnofri.EntropyScalarCertificate.Bessel0315
import BecknerOnofri.EntropyScalarCertificate.Bessel0316
import BecknerOnofri.EntropyScalarCertificate.Bessel0646
import BecknerOnofri.EntropyScalarCertificate.Bessel0647
import BecknerOnofri.EntropyScalarCertificate.Brackets0126
import BecknerOnofri.EntropyScalarCertificate.Logs0252
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2016
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (55461457301047581861832573137835058156029/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (55461457301047581861832573137835058156029/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (27789295391454197000418232824463896555547/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (27789295391454197000418232824463896555547/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (111040048083955975862669038786762851267123/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (111040048083955975862669038786762851267123/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0126.bracket2016 BracketBatch0126.bracket2017 (111040048083955975862669038786762851267123/20000000000000000000000000000000000000000) (62504984530366596106217743870486355699/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0126.bracket2016 BracketBatch0126.bracket2017
  (111040048083955975862669038786762851267123/20000000000000000000000000000000000000000) (62504984530366596106217743870486355699/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2016
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2017
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (55578590782908394000836465648927793111091/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (55578590782908394000836465648927793111091/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (55696234802341408658156859334940695477041/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (55696234802341408658156859334940695477041/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (27818706396312450664748331245967122147033/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (27818706396312450664748331245967122147033/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0126.bracket2017 BracketBatch0126.bracket2018 (27818706396312450664748331245967122147033/5000000000000000000000000000000000000000) (2002830345991078853738900715803546460079/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0126.bracket2017 BracketBatch0126.bracket2018
  (27818706396312450664748331245967122147033/5000000000000000000000000000000000000000) (2002830345991078853738900715803546460079/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2017
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2018
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (27848117401170704329078429667470347738519/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (27848117401170704329078429667470347738519/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (55814392694562201238505727791028489136673/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (55814392694562201238505727791028489136673/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (111510627496903609896662587125969184613711/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (111510627496903609896662587125969184613711/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0126.bracket2018 BracketBatch0126.bracket2019 (111510627496903609896662587125969184613711/20000000000000000000000000000000000000000) (2005507678041553302316374580878292943151/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0126.bracket2018 BracketBatch0126.bracket2019
  (111510627496903609896662587125969184613711/20000000000000000000000000000000000000000) (2005507678041553302316374580878292943151/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2018
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2019
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (5581439269456220123850572779102848913667/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5581439269456220123850572779102848913667/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (27966533911960263440340559912861089563811/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (27966533911960263440340559912861089563811/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (27936865129620682029796711904187667066073/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (27936865129620682029796711904187667066073/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0126.bracket2019 BracketBatch0126.bracket2020 (27936865129620682029796711904187667066073/5000000000000000000000000000000000000000) (401638305975028570622786350268340559723/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0126.bracket2019 BracketBatch0126.bracket2020
  (27936865129620682029796711904187667066073/5000000000000000000000000000000000000000) (401638305975028570622786350268340559723/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2019
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2020
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (55933067823920526880681119825722179127619/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (55933067823920526880681119825722179127619/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (700653294802738020143882053077170731859/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (700653294802738020143882053077170731859/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (111985331408139568492191684071895837676339/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (111985331408139568492191684071895837676339/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0126.bracket2020 BracketBatch0126.bracket2021 (111985331408139568492191684071895837676339/20000000000000000000000000000000000000000) (1005440965219370573147311564188565983279/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0126.bracket2020 BracketBatch0126.bracket2021
  (111985331408139568492191684071895837676339/20000000000000000000000000000000000000000) (1005440965219370573147311564188565983279/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2020
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2021
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (56052263584219041611510564246173658548717/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (56052263584219041611510564246173658548717/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (11234396679807243455773625038922080522883/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11234396679807243455773625038922080522883/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (28056061745813814722594672360196015290783/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28056061745813814722594672360196015290783/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0126.bracket2021 BracketBatch0126.bracket2022 (28056061745813814722594672360196015290783/5000000000000000000000000000000000000000) (125848681804742577761888308448649138979/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0126.bracket2021 BracketBatch0126.bracket2022
  (28056061745813814722594672360196015290783/5000000000000000000000000000000000000000) (125848681804742577761888308448649138979/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2021
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2022
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (14042995849759054319717031298652600653603/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14042995849759054319717031298652600653603/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (450337845776428118304073632175277401599/80000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (450337845776428118304073632175277401599/80000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (112464214121089732066877329216520077814287/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (112464214121089732066877329216520077814287/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0126.bracket2022 BracketBatch0126.bracket2023 (112464214121089732066877329216520077814287/20000000000000000000000000000000000000000) (16130259956227911259166802358633515447/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0126.bracket2022 BracketBatch0126.bracket2023
  (112464214121089732066877329216520077814287/20000000000000000000000000000000000000000) (16130259956227911259166802358633515447/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2022
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2023
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (439783052516043084281321906421169337499/78125000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (439783052516043084281321906421169337499/78125000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (7051626129673360162796052392799704947923/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7051626129673360162796052392799704947923/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (14088154969930049511297202895538414347907/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14088154969930049511297202895538414347907/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0252.rows ScalarLogs0252.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0126.bracket2023 BracketBatch0126.bracket2024 (14088154969930049511297202895538414347907/2500000000000000000000000000000000000000) (1009496358469327591461538137097671001867/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0126.bracket2023 BracketBatch0126.bracket2024
  (14088154969930049511297202895538414347907/2500000000000000000000000000000000000000) (1009496358469327591461538137097671001867/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2023
