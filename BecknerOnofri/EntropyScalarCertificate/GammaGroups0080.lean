import BecknerOnofri.EntropyScalarCertificate.Bessel0100
import BecknerOnofri.EntropyScalarCertificate.Bessel0101
import BecknerOnofri.EntropyScalarCertificate.Bessel0538
import BecknerOnofri.EntropyScalarCertificate.Bessel0539
import BecknerOnofri.EntropyScalarCertificate.Brackets0040
import BecknerOnofri.EntropyScalarCertificate.Logs0080
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0640
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (187732273702243259536922702302213367003/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (187732273702243259536922702302213367003/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (75177201457561007814147363633402928871/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (75177201457561007814147363633402928871/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (751350554692291558144582222771441378361/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (751350554692291558144582222771441378361/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0040.bracket0640 BracketBatch0040.bracket0641 (751350554692291558144582222771441378361/4000000000000000000000000000000000000000) (914853201072179219871024553560302343/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0040.bracket0640 BracketBatch0040.bracket0641
  (751350554692291558144582222771441378361/4000000000000000000000000000000000000000) (914853201072179219871024553560302343/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0640
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0641
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (469857509109756298838421022708768305443/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (469857509109756298838421022708768305443/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (37630751600331651660962652477939687411/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (37630751600331651660962652477939687411/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (1880483808227803889200908357366028796161/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1880483808227803889200908357366028796161/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0040.bracket0641 BracketBatch0040.bracket0642 (1880483808227803889200908357366028796161/10000000000000000000000000000000000000000) (459428100588404013981395774456630919/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0040.bracket0641 BracketBatch0040.bracket0642
  (1880483808227803889200908357366028796161/10000000000000000000000000000000000000000) (459428100588404013981395774456630919/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0641
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0642
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (1881537580016582583048132623896984370547/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1881537580016582583048132623896984370547/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (1883645368071847655961275854012353177151/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1883645368071847655961275854012353177151/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (1882591474044215119504704238954668773849/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1882591474044215119504704238954668773849/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0040.bracket0642 BracketBatch0040.bracket0643 (1882591474044215119504704238954668773849/10000000000000000000000000000000000000000) (461436205175665171024786723089163581/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0040.bracket0642 BracketBatch0040.bracket0643
  (1882591474044215119504704238954668773849/10000000000000000000000000000000000000000) (461436205175665171024786723089163581/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0642
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0643
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (470911342017961913990318963503088294287/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (470911342017961913990318963503088294287/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (942876700460874715060384863648540792117/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (942876700460874715060384863648540792117/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (1884699384496798543041022790654717380691/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1884699384496798543041022790654717380691/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0040.bracket0643 BracketBatch0040.bracket0644 (1884699384496798543041022790654717380691/10000000000000000000000000000000000000000) (926901858236801922651001547015982909/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0040.bracket0643 BracketBatch0040.bracket0644
  (1884699384496798543041022790654717380691/10000000000000000000000000000000000000000) (926901858236801922651001547015982909/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0643
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0644
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (1885753400921749430120769727297081584231/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1885753400921749430120769727297081584231/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (377572335776680667012184314489349431207/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (377572335776680667012184314489349431207/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (1886807539902576382590845649871914370133/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1886807539902576382590845649871914370133/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0040.bracket0644 BracketBatch0040.bracket0645 (1886807539902576382590845649871914370133/10000000000000000000000000000000000000000) (930944574510941877890410403082270957/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0040.bracket0644 BracketBatch0040.bracket0645
  (1886807539902576382590845649871914370133/10000000000000000000000000000000000000000) (930944574510941877890410403082270957/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0644
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0645
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (29497838732553177110326899569480424313/156250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (29497838732553177110326899569480424313/156250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (236246275284263938645748262920530277567/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (236246275284263938645748262920530277567/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (472228985144689355528363459476373672071/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (472228985144689355528363459476373672071/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0040.bracket0645 BracketBatch0040.bracket0646 (472228985144689355528363459476373672071/2500000000000000000000000000000000000000) (935000588888148705604306106963649731/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0040.bracket0645 BracketBatch0040.bracket0646
  (472228985144689355528363459476373672071/2500000000000000000000000000000000000000) (935000588888148705604306106963649731/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0645
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0646
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (1889970202274111509165986103364242220533/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1889970202274111509165986103364242220533/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (946039485705681547684877553471136417059/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (946039485705681547684877553471136417059/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (3782049173685474604535741210306515054651/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3782049173685474604535741210306515054651/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0040.bracket0646 BracketBatch0040.bracket0647 (3782049173685474604535741210306515054651/20000000000000000000000000000000000000000) (46953496555975817978511492265293907/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0040.bracket0646 BracketBatch0040.bracket0647
  (3782049173685474604535741210306515054651/20000000000000000000000000000000000000000) (46953496555975817978511492265293907/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0646
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0647
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (378415794282272619073951021388454566823/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (378415794282272619073951021388454566823/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0101.rows BesselBatch0101.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (947093993306417268606069222199530382021/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (947093993306417268606069222199530382021/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0539.rows BesselBatch0539.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (3786266958024197632581893551341333598157/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3786266958024197632581893551341333598157/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0080.rows ScalarLogs0080.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0040.bracket0647 BracketBatch0040.bracket0648 (3786266958024197632581893551341333598157/20000000000000000000000000000000000000000) (235788157748212584969699130566236087/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0040.bracket0647 BracketBatch0040.bracket0648
  (3786266958024197632581893551341333598157/20000000000000000000000000000000000000000) (235788157748212584969699130566236087/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0647
