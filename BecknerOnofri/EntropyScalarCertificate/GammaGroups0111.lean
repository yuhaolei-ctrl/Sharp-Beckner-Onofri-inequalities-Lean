import BecknerOnofri.EntropyScalarCertificate.Bessel0138
import BecknerOnofri.EntropyScalarCertificate.Bessel0139
import BecknerOnofri.EntropyScalarCertificate.Bessel0140
import BecknerOnofri.EntropyScalarCertificate.Bessel0558
import BecknerOnofri.EntropyScalarCertificate.Brackets0055
import BecknerOnofri.EntropyScalarCertificate.Brackets0056
import BecknerOnofri.EntropyScalarCertificate.Logs0111
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0888
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (15572333234152504294048161427389858677/39062500000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15572333234152504294048161427389858677/39062500000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (1999527968051735612082935998338872739419/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1999527968051735612082935998338872739419/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (159711464880930246468844026441790986003/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (159711464880930246468844026441790986003/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0055.bracket0888 BracketBatch0055.bracket0889 (159711464880930246468844026441790986003/400000000000000000000000000000000000000) (1931941824715528627977524234877652641/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0055.bracket0888 BracketBatch0055.bracket0889
  (159711464880930246468844026441790986003/400000000000000000000000000000000000000) (1931941824715528627977524234877652641/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0888
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0889
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0138.rows BesselBatch0138.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (799811187220694244833174399335549095767/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (799811187220694244833174399335549095767/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (802322294009166257990996841211382090421/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (802322294009166257990996841211382090421/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (400533370307465125706042810136732796547/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (400533370307465125706042810136732796547/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0055.bracket0889 BracketBatch0055.bracket0890 (400533370307465125706042810136732796547/1000000000000000000000000000000000000000) (7814377900446478312524464433669206239/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0055.bracket0889 BracketBatch0055.bracket0890
  (400533370307465125706042810136732796547/1000000000000000000000000000000000000000) (7814377900446478312524464433669206239/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0889
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0890
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (2005805735022915644977492103028455226051/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2005805735022915644977492103028455226051/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (2012091998658184407172960757851787375403/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2012091998658184407172960757851787375403/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (2008948866840550026075226430440121300727/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2008948866840550026075226430440121300727/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0055.bracket0890 BracketBatch0055.bracket0891 (2008948866840550026075226430440121300727/5000000000000000000000000000000000000000) (7901738419049864234413990727966260263/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0055.bracket0890 BracketBatch0055.bracket0891
  (2008948866840550026075226430440121300727/5000000000000000000000000000000000000000) (7901738419049864234413990727966260263/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0890
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0891
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (4024183997316368814345921515703574750803/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4024183997316368814345921515703574750803/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (2018386802974889213261664741392362994109/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2018386802974889213261664741392362994109/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (8060957603266147240869250998488300739021/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8060957603266147240869250998488300739021/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0055.bracket0891 BracketBatch0055.bracket0892 (8060957603266147240869250998488300739021/20000000000000000000000000000000000000000) (3994926806234469387736102682534203747/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0055.bracket0891 BracketBatch0055.bracket0892
  (8060957603266147240869250998488300739021/20000000000000000000000000000000000000000) (3994926806234469387736102682534203747/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0891
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0892
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (807354721189955685304665896556945197643/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (807354721189955685304665896556945197643/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (4049380384473211799085778190099066366251/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4049380384473211799085778190099066366251/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (4043076995211495112804553836441896177233/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4043076995211495112804553836441896177233/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0055.bracket0892 BracketBatch0055.bracket0893 (4043076995211495112804553836441896177233/10000000000000000000000000000000000000000) (8078728260666339263172938048145536817/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0055.bracket0892 BracketBatch0055.bracket0893
  (4043076995211495112804553836441896177233/10000000000000000000000000000000000000000) (8078728260666339263172938048145536817/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0892
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0893
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (506172548059151474885722273762383295781/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (506172548059151474885722273762383295781/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (4062004421910326097681999925730782845269/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4062004421910326097681999925730782845269/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (8111384806383537896767778115829849211517/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8111384806383537896767778115829849211517/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0055.bracket0893 BracketBatch0055.bracket0894 (8111384806383537896767778115829849211517/20000000000000000000000000000000000000000) (8168367165880537921329391571162535283/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0055.bracket0893 BracketBatch0055.bracket0894
  (8111384806383537896767778115829849211517/20000000000000000000000000000000000000000) (8168367165880537921329391571162535283/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0893
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0894
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (2031002210955163048840999962865391422633/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2031002210955163048840999962865391422633/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (2037322903892685697854197174584289905467/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2037322903892685697854197174584289905467/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (40683251148478487466951971374496813281/100000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (40683251148478487466951971374496813281/100000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0055.bracket0894 BracketBatch0055.bracket0895 (40683251148478487466951971374496813281/100000000000000000000000000000000000000) (3303510061094660670026742762543107139/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0055.bracket0894 BracketBatch0055.bracket0895
  (40683251148478487466951971374496813281/100000000000000000000000000000000000000) (3303510061094660670026742762543107139/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0894
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0895
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0139.rows BesselBatch0139.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (4074645807785371395708394349168579810931/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4074645807785371395708394349168579810931/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0140.rows BesselBatch0140.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (4087304632127317507365148655602672527491/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4087304632127317507365148655602672527491/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0558.rows BesselBatch0558.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (4080975219956344451536771502385626169211/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4080975219956344451536771502385626169211/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0111.rows ScalarLogs0111.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0055.bracket0895 BracketBatch0056.bracket0896 (4080975219956344451536771502385626169211/10000000000000000000000000000000000000000) (16699914136716415644408187829480147027/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0055.bracket0895 BracketBatch0056.bracket0896
  (4080975219956344451536771502385626169211/10000000000000000000000000000000000000000) (16699914136716415644408187829480147027/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0895
