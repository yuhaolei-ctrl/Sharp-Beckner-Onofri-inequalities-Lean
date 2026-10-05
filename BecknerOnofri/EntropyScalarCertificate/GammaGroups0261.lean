import BecknerOnofri.EntropyScalarCertificate.Bessel0326
import BecknerOnofri.EntropyScalarCertificate.Bessel0327
import BecknerOnofri.EntropyScalarCertificate.Bessel0652
import BecknerOnofri.EntropyScalarCertificate.Brackets0130
import BecknerOnofri.EntropyScalarCertificate.Brackets0131
import BecknerOnofri.EntropyScalarCertificate.Logs0261
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2088
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (65434112763674129230460106036059697538181/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (65434112763674129230460106036059697538181/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (65598665975348356090367248822274168143129/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (65598665975348356090367248822274168143129/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (13103277873902248532082735485833386568131/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13103277873902248532082735485833386568131/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0130.bracket2088 BracketBatch0130.bracket2089 (13103277873902248532082735485833386568131/2000000000000000000000000000000000000000) (2210921056715975848866540664166736511713/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0130.bracket2088 BracketBatch0130.bracket2089
  (13103277873902248532082735485833386568131/2000000000000000000000000000000000000000) (2210921056715975848866540664166736511713/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2088
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2089
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (32799332987674178045183624411137084071563/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (32799332987674178045183624411137084071563/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (8220508596381175186487887924350878384873/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8220508596381175186487887924350878384873/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (13136273474639775758227035221708119522211/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13136273474639775758227035221708119522211/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0130.bracket2089 BracketBatch0130.bracket2090 (13136273474639775758227035221708119522211/2000000000000000000000000000000000000000) (2214144262552342628977757727956983597939/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0130.bracket2089 BracketBatch0130.bracket2090
  (13136273474639775758227035221708119522211/2000000000000000000000000000000000000000) (2214144262552342628977757727956983597939/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2089
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2090
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (65764068771049401491903103394807027078981/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (65764068771049401491903103394807027078981/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (65930327735155765124595275188061909222991/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (65930327735155765124595275188061909222991/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (32923599126551291654124594645717234075493/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (32923599126551291654124594645717234075493/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0130.bracket2090 BracketBatch0130.bracket2091 (32923599126551291654124594645717234075493/5000000000000000000000000000000000000000) (443475325875041299100316010079716872037/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0130.bracket2090 BracketBatch0130.bracket2091
  (32923599126551291654124594645717234075493/5000000000000000000000000000000000000000) (443475325875041299100316010079716872037/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2090
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2091
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (16482581933788941281148818797015477305747/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16482581933788941281148818797015477305747/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (258193162188602172660760927495428358537/39062500000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (258193162188602172660760927495428358537/39062500000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (6601388862771896066287503631344578450423/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6601388862771896066287503631344578450423/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0130.bracket2091 BracketBatch0130.bracket2092 (6601388862771896066287503631344578450423/1000000000000000000000000000000000000000) (2220618208182448830358463621367400808009/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0130.bracket2091 BracketBatch0130.bracket2092
  (6601388862771896066287503631344578450423/1000000000000000000000000000000000000000) (2220618208182448830358463621367400808009/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2091
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2092
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0326.rows BesselBatch0326.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (66097449520282156201154797438829659785469/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (66097449520282156201154797438829659785469/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (66265440848165652529892588791506862023307/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (66265440848165652529892588791506862023307/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (16545361296055976091380923278792065226097/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16545361296055976091380923278792065226097/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0130.bracket2092 BracketBatch0130.bracket2093 (16545361296055976091380923278792065226097/2500000000000000000000000000000000000000) (277983631065165496002490387823618098963/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0130.bracket2092 BracketBatch0130.bracket2093
  (16545361296055976091380923278792065226097/2500000000000000000000000000000000000000) (277983631065165496002490387823618098963/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2092
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2093
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (8283180106020706566236573598938357752913/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8283180106020706566236573598938357752913/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (6643430851056570604892429146171049165893/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6643430851056570604892429146171049165893/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (66349874679365679289408440126608676841117/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (66349874679365679289408440126608676841117/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0130.bracket2093 BracketBatch0130.bracket2094 (66349874679365679289408440126608676841117/10000000000000000000000000000000000000000) (1113564599785041257787835119443864518457/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0130.bracket2093 BracketBatch0130.bracket2094
  (66349874679365679289408440126608676841117/10000000000000000000000000000000000000000) (1113564599785041257787835119443864518457/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2093
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2094
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (66434308510565706048924291461710491658927/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (66434308510565706048924291461710491658927/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (66604059370178247889568094442021843463971/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (66604059370178247889568094442021843463971/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (66519183940371976969246192951866167561449/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (66519183940371976969246192951866167561449/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0130.bracket2094 BracketBatch0130.bracket2095 (66519183940371976969246192951866167561449/10000000000000000000000000000000000000000) (1115199355449692672008017598626306736491/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0130.bracket2094 BracketBatch0130.bracket2095
  (66519183940371976969246192951866167561449/10000000000000000000000000000000000000000) (1115199355449692672008017598626306736491/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2094
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2095
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (2081376855318070246549002951313182608249/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2081376855318070246549002951313182608249/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (66774700361564151336134364552088022586541/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (66774700361564151336134364552088022586541/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (133378759731742399225702458994109866050509/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (133378759731742399225702458994109866050509/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0261.rows ScalarLogs0261.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0130.bracket2095 BracketBatch0131.bracket2096 (133378759731742399225702458994109866050509/20000000000000000000000000000000000000000) (1116838816238198566120781060667477497831/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0130.bracket2095 BracketBatch0131.bracket2096
  (133378759731742399225702458994109866050509/20000000000000000000000000000000000000000) (1116838816238198566120781060667477497831/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2095
