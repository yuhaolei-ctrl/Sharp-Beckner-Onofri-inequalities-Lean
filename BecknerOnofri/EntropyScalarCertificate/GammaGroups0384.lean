import BecknerOnofri.EntropyScalarCertificate.Bessel0480
import BecknerOnofri.EntropyScalarCertificate.Bessel0481
import BecknerOnofri.EntropyScalarCertificate.Bessel0728
import BecknerOnofri.EntropyScalarCertificate.Bessel0729
import BecknerOnofri.EntropyScalarCertificate.Brackets0192
import BecknerOnofri.EntropyScalarCertificate.Logs0384
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3072
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (488594351929150981962368442877193439870643/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (488594351929150981962368442877193439870643/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (98101835600339156599893833996648055582509/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (98101835600339156599893833996648055582509/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (244775882482711691240459403215108429445797/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (244775882482711691240459403215108429445797/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0192.bracket3072 BracketBatch0192.bracket3073 (244775882482711691240459403215108429445797/1250000000000000000000000000000000000000) (1784625315509626843252191043901881068193/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0192.bracket3072 BracketBatch0192.bracket3073
  (244775882482711691240459403215108429445797/1250000000000000000000000000000000000000) (1784625315509626843252191043901881068193/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3072
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3073
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (1962036712006783131997876679932961111650177/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1962036712006783131997876679932961111650177/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (1969756325854093693998239540977600050217063/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1969756325854093693998239540977600050217063/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (98294825946521920649902905522764029046681/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (98294825946521920649902905522764029046681/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0192.bracket3073 BracketBatch0192.bracket3074 (98294825946521920649902905522764029046681/500000000000000000000000000000000000000) (7144355248291566314942948673131968399849/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0192.bracket3073 BracketBatch0192.bracket3074
  (98294825946521920649902905522764029046681/500000000000000000000000000000000000000) (7144355248291566314942948673131968399849/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3073
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3074
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (98487816292704684699911977048880002510853/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (98487816292704684699911977048880002510853/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (1977536964391621295651116267929303914258151/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1977536964391621295651116267929303914258151/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (3947293290245714989649355808906903964475211/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3947293290245714989649355808906903964475211/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0192.bracket3074 BracketBatch0192.bracket3075 (3947293290245714989649355808906903964475211/20000000000000000000000000000000000000000) (7150229103423479744994695759641360965243/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0192.bracket3074 BracketBatch0192.bracket3075
  (3947293290245714989649355808906903964475211/20000000000000000000000000000000000000000) (7150229103423479744994695759641360965243/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3074
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3075
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (494384241097905323912779066982325978564537/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (494384241097905323912779066982325978564537/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (992689677051885219658097517660251163910427/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (992689677051885219658097517660251163910427/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (1981458159247695867483655651624903121039501/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1981458159247695867483655651624903121039501/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0192.bracket3075 BracketBatch0192.bracket3076 (1981458159247695867483655651624903121039501/10000000000000000000000000000000000000000) (7156122928772201123039450726352523137859/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0192.bracket3075 BracketBatch0192.bracket3076
  (1981458159247695867483655651624903121039501/10000000000000000000000000000000000000000) (7156122928772201123039450726352523137859/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3075
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3076
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (1985379354103770439316195035320502327820851/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1985379354103770439316195035320502327820851/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (996642116526193168384015569495113174995909/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (996642116526193168384015569495113174995909/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (3978663587156156776084226174310728677812669/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3978663587156156776084226174310728677812669/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0192.bracket3076 BracketBatch0192.bracket3077 (3978663587156156776084226174310728677812669/20000000000000000000000000000000000000000) (447627301612064037276779530587238678731/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0192.bracket3076 BracketBatch0192.bracket3077
  (3978663587156156776084226174310728677812669/20000000000000000000000000000000000000000) (447627301612064037276779530587238678731/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3076
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3077
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (398656846610477267353606227798045269998363/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (398656846610477267353606227798045269998363/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (2001252351108303723384317449795058639131507/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2001252351108303723384317449795058639131507/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (1997268292080345030076174294392642494561661/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1997268292080345030076174294392642494561661/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0192.bracket3077 BracketBatch0192.bracket3078 (1997268292080345030076174294392642494561661/10000000000000000000000000000000000000000) (1791992724008691310534018546025783712991/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0192.bracket3077 BracketBatch0192.bracket3078
  (1997268292080345030076174294392642494561661/10000000000000000000000000000000000000000) (1791992724008691310534018546025783712991/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3077
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3078
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (125078271944268982711519840612191164945719/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (125078271944268982711519840612191164945719/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (31395069846694924403635428334388893022861/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (31395069846694924403635428334388893022861/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (250658551331048680326061553949746737037163/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (250658551331048680326061553949746737037163/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0192.bracket3078 BracketBatch0192.bracket3079 (250658551331048680326061553949746737037163/1250000000000000000000000000000000000000) (3586962620557375134013738986312203826441/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0192.bracket3078 BracketBatch0192.bracket3079
  (250658551331048680326061553949746737037163/1250000000000000000000000000000000000000) (3586962620557375134013738986312203826441/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3078
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3079
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (2009284470188475161832667413400889153463101/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2009284470188475161832667413400889153463101/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (2017381364498836320846594418019363815682063/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2017381364498836320846594418019363815682063/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (1006666458671827870669815457855063242286291/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1006666458671827870669815457855063242286291/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0384.rows ScalarLogs0384.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0192.bracket3079 BracketBatch0192.bracket3080 (1006666458671827870669815457855063242286291/5000000000000000000000000000000000000000) (7179899962692569766126597893650618974821/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0192.bracket3079 BracketBatch0192.bracket3080
  (1006666458671827870669815457855063242286291/5000000000000000000000000000000000000000) (7179899962692569766126597893650618974821/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3079
