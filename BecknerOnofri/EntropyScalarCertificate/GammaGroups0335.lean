import BecknerOnofri.EntropyScalarCertificate.Bessel0418
import BecknerOnofri.EntropyScalarCertificate.Bessel0419
import BecknerOnofri.EntropyScalarCertificate.Bessel0420
import BecknerOnofri.EntropyScalarCertificate.Bessel0698
import BecknerOnofri.EntropyScalarCertificate.Brackets0167
import BecknerOnofri.EntropyScalarCertificate.Brackets0168
import BecknerOnofri.EntropyScalarCertificate.Logs0335
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2680
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (316285315459611698831370905112366753436101/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (316285315459611698831370905112366753436101/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (635775227846257690954219413747513038593181/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (635775227846257690954219413747513038593181/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (1268345858765481088616961223972246545465383/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1268345858765481088616961223972246545465383/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0167.bracket2680 BracketBatch0167.bracket2681 (1268345858765481088616961223972246545465383/20000000000000000000000000000000000000000) (673840790407084937747551359171816244183/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0167.bracket2680 BracketBatch0167.bracket2681
  (1268345858765481088616961223972246545465383/20000000000000000000000000000000000000000) (673840790407084937747551359171816244183/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2680
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2681
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (317887613923128845477109706873756519296589/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (317887613923128845477109706873756519296589/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (639012525136236409662593975863982779411601/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (639012525136236409662593975863982779411601/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (1274787752982494100616813389611495818004779/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1274787752982494100616813389611495818004779/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0167.bracket2681 BracketBatch0167.bracket2682 (1274787752982494100616813389611495818004779/20000000000000000000000000000000000000000) (674764537969046936589392796749343228379/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0167.bracket2681 BracketBatch0167.bracket2682
  (1274787752982494100616813389611495818004779/20000000000000000000000000000000000000000) (674764537969046936589392796749343228379/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2681
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2682
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (319506262568118204831296987931991389705799/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (319506262568118204831296987931991389705799/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (642283025871605172356862199109895754382651/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (642283025871605172356862199109895754382651/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (1281295551007841582019456174973878533794249/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1281295551007841582019456174973878533794249/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0167.bracket2682 BracketBatch0167.bracket2683 (1281295551007841582019456174973878533794249/20000000000000000000000000000000000000000) (2702770770762856474337936783846127137731/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0167.bracket2682 BracketBatch0167.bracket2683
  (1281295551007841582019456174973878533794249/20000000000000000000000000000000000000000) (2702770770762856474337936783846127137731/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2682
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2683
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (80285378233950646544607774888736969297831/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (80285378233950646544607774888736969297831/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (322793621753821773418797076595767677887233/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (322793621753821773418797076595767677887233/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (643935134689624359597228176150715555078557/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (643935134689624359597228176150715555078557/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0167.bracket2683 BracketBatch0167.bracket2684 (643935134689624359597228176150715555078557/10000000000000000000000000000000000000000) (5413002317138813631829522357838267892611/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0167.bracket2683 BracketBatch0167.bracket2684
  (643935134689624359597228176150715555078557/10000000000000000000000000000000000000000) (5413002317138813631829522357838267892611/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2683
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2684
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (645587243507643546837594153191535355774463/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (645587243507643546837594153191535355774463/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (648925702141191318241881482644808860361769/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (648925702141191318241881482644808860361769/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (161814118206104358134934454479543027017029/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (161814118206104358134934454479543027017029/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0167.bracket2684 BracketBatch0167.bracket2685 (161814118206104358134934454479543027017029/2500000000000000000000000000000000000000) (1084099782686797060610555507775820183213/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0167.bracket2684 BracketBatch0167.bracket2685
  (161814118206104358134934454479543027017029/2500000000000000000000000000000000000000) (1084099782686797060610555507775820183213/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2684
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2685
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (324462851070595659120940741322404430180883/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (324462851070595659120940741322404430180883/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (652298936787772453026572915276950250643981/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (652298936787772453026572915276950250643981/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (1301224638928963771268454397921759111005747/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1301224638928963771268454397921759111005747/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0167.bracket2685 BracketBatch0167.bracket2686 (1301224638928963771268454397921759111005747/20000000000000000000000000000000000000000) (1085606323103664802565868131852079367753/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0167.bracket2685 BracketBatch0167.bracket2686
  (1301224638928963771268454397921759111005747/20000000000000000000000000000000000000000) (1085606323103664802565868131852079367753/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2685
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2686
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (326149468393886226513286457638475125321989/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (326149468393886226513286457638475125321989/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (81963436708428065973585896702525045497967/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (81963436708428065973585896702525045497967/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (654003215227598490407630044448575307313857/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (654003215227598490407630044448575307313857/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0167.bracket2686 BracketBatch0167.bracket2687 (654003215227598490407630044448575307313857/10000000000000000000000000000000000000000) (679450088843208498875054141398809507869/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0167.bracket2686 BracketBatch0167.bracket2687
  (654003215227598490407630044448575307313857/10000000000000000000000000000000000000000) (679450088843208498875054141398809507869/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2686
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2687
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0419.rows BesselBatch0419.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (655707493667424527788687173620200363983733/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (655707493667424527788687173620200363983733/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (65915193049955435057489929067982815136443/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (65915193049955435057489929067982815136443/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (1314859424166978878363586464300028515348163/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1314859424166978878363586464300028515348163/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0335.rows ScalarLogs0335.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0167.bracket2687 BracketBatch0168.bracket2688 (1314859424166978878363586464300028515348163/20000000000000000000000000000000000000000) (85050101385870732807570931969589689929/156250000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0167.bracket2687 BracketBatch0168.bracket2688
  (1314859424166978878363586464300028515348163/20000000000000000000000000000000000000000) (85050101385870732807570931969589689929/156250000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2687
