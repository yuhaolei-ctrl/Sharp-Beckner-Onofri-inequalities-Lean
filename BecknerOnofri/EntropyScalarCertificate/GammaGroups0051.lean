import BecknerOnofri.EntropyScalarCertificate.Bessel0063
import BecknerOnofri.EntropyScalarCertificate.Bessel0064
import BecknerOnofri.EntropyScalarCertificate.Bessel0065
import BecknerOnofri.EntropyScalarCertificate.Bessel0520
import BecknerOnofri.EntropyScalarCertificate.Bessel0521
import BecknerOnofri.EntropyScalarCertificate.Brackets0025
import BecknerOnofri.EntropyScalarCertificate.Brackets0026
import BecknerOnofri.EntropyScalarCertificate.Logs0051
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0408
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (2788764213823941384533168123745861401/20000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2788764213823941384533168123745861401/20000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (1396440964148244056748069648790578509171/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1396440964148244056748069648790578509171/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (2790823071060214749014653710663509209671/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2790823071060214749014653710663509209671/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0025.bracket0408 BracketBatch0025.bracket0409 (2790823071060214749014653710663509209671/20000000000000000000000000000000000000000) (285134415686281291320057670130225319/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0025.bracket0408 BracketBatch0025.bracket0409
  (2790823071060214749014653710663509209671/20000000000000000000000000000000000000000) (285134415686281291320057670130225319/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0408
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0409
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (87277560259265253546754353049411156823/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (87277560259265253546754353049411156823/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (139849999650989757309957073871060367069/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (139849999650989757309957073871060367069/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (1397470480329070814923820193750591089929/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1397470480329070814923820193750591089929/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0025.bracket0409 BracketBatch0025.bracket0410 (1397470480329070814923820193750591089929/10000000000000000000000000000000000000000) (286798626810746215106775220815732123/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0025.bracket0409 BracketBatch0025.bracket0410
  (1397470480329070814923820193750591089929/10000000000000000000000000000000000000000) (286798626810746215106775220815732123/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0409
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0410
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (1398499996509897573099570738710603670687/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1398499996509897573099570738710603670687/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (700279602138898667421013039549882911699/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (700279602138898667421013039549882911699/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (559811840157538981588319363562073898817/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (559811840157538981588319363562073898817/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0025.bracket0410 BracketBatch0025.bracket0411 (559811840157538981588319363562073898817/4000000000000000000000000000000000000000) (288470130460772979300198690516433177/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0025.bracket0410 BracketBatch0025.bracket0411
  (559811840157538981588319363562073898817/4000000000000000000000000000000000000000) (288470130460772979300198690516433177/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0410
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0411
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (280111840855559466968405215819953164679/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (280111840855559466968405215819953164679/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (1402618587732935401871625523673911246707/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1402618587732935401871625523673911246707/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (1401588896005366368356825801386838535051/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1401588896005366368356825801386838535051/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0025.bracket0411 BracketBatch0025.bracket0412 (1401588896005366368356825801386838535051/10000000000000000000000000000000000000000) (72537237039579350713738918870071247/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0025.bracket0411 BracketBatch0025.bracket0412
  (1401588896005366368356825801386838535051/10000000000000000000000000000000000000000) (72537237039579350713738918870071247/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0411
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0412
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (87663661733308462616976595229619452919/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (87663661733308462616976595229619452919/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (28093562943128600588312561523729340331/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (28093562943128600588312561523729340331/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (1403648367444682715643626799930189131627/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1403648367444682715643626799930189131627/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0025.bracket0412 BracketBatch0025.bracket0413 (1403648367444682715643626799930189131627/10000000000000000000000000000000000000000) (291835101458883281927582466858059691/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0025.bracket0412 BracketBatch0025.bracket0413
  (1403648367444682715643626799930189131627/10000000000000000000000000000000000000000) (291835101458883281927582466858059691/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0412
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0413
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (1404678147156430029415628076186467016547/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1404678147156430029415628076186467016547/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (703368941414762948605563849115001646843/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (703368941414762948605563849115001646843/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (2811416029985955926626755774416470310233/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2811416029985955926626755774416470310233/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0025.bracket0413 BracketBatch0025.bracket0414 (2811416029985955926626755774416470310233/20000000000000000000000000000000000000000) (293528611951533440063778160284552233/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0025.bracket0413 BracketBatch0025.bracket0414
  (2811416029985955926626755774416470310233/20000000000000000000000000000000000000000) (293528611951533440063778160284552233/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0413
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0414
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (1406737882829525897211127698230003293683/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1406737882829525897211127698230003293683/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (704398897516797169453617993880856925797/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (704398897516797169453617993880856925797/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (2815535677863120236118363685991717145277/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2815535677863120236118363685991717145277/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0025.bracket0414 BracketBatch0025.bracket0415 (2815535677863120236118363685991717145277/20000000000000000000000000000000000000000) (295229501258900797733851060369379303/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0025.bracket0414 BracketBatch0025.bracket0415
  (2815535677863120236118363685991717145277/20000000000000000000000000000000000000000) (295229501258900797733851060369379303/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0414
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0415
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0064.rows BesselBatch0064.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (1408797795033594338907235987761713851591/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1408797795033594338907235987761713851591/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (17635723550626669646139394589213542627/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17635723550626669646139394589213542627/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (2819655679083727910598387554898797261751/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2819655679083727910598387554898797261751/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0051.rows ScalarLogs0051.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0025.bracket0415 BracketBatch0026.bracket0416 (2819655679083727910598387554898797261751/20000000000000000000000000000000000000000) (296937791037199461232481104468378251/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0025.bracket0415 BracketBatch0026.bracket0416
  (2819655679083727910598387554898797261751/20000000000000000000000000000000000000000) (296937791037199461232481104468378251/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0415
