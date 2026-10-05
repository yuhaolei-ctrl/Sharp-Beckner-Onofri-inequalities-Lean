import BecknerOnofri.EntropyScalarCertificate.Bessel0440
import BecknerOnofri.EntropyScalarCertificate.Bessel0441
import BecknerOnofri.EntropyScalarCertificate.Bessel0708
import BecknerOnofri.EntropyScalarCertificate.Bessel0709
import BecknerOnofri.EntropyScalarCertificate.Brackets0176
import BecknerOnofri.EntropyScalarCertificate.Logs0352
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2816
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (7822538648117700052336287148574954637361/80000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7822538648117700052336287148574954637361/80000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (122466050341425763878429047722576928770779/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (122466050341425763878429047722576928770779/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (1957545733746118617569468275352484759836357/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1957545733746118617569468275352484759836357/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0176.bracket2816 BracketBatch0176.bracket2817 (1957545733746118617569468275352484759836357/20000000000000000000000000000000000000000) (6078968375711863094048471642998496377677/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0176.bracket2816 BracketBatch0176.bracket2817
  (1957545733746118617569468275352484759836357/20000000000000000000000000000000000000000) (6078968375711863094048471642998496377677/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2816
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2817
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (979728402731406111027432381780615430166229/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (979728402731406111027432381780615430166229/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (981646968884471526146532143440096510317011/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (981646968884471526146532143440096510317011/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0708.rows BesselBatch0708.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (49034384290396940929349113130517798512081/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (49034384290396940929349113130517798512081/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0176.bracket2817 BracketBatch0176.bracket2818 (49034384290396940929349113130517798512081/500000000000000000000000000000000000000) (6081972783005594354479678620031640875881/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0176.bracket2817 BracketBatch0176.bracket2818
  (49034384290396940929349113130517798512081/500000000000000000000000000000000000000) (6081972783005594354479678620031640875881/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2817
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2818
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (61352935555279470384158258965006031894813/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (61352935555279470384158258965006031894813/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (491786536822718997641226212014878059333139/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (491786536822718997641226212014878059333139/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (982610021264954760714492283734926314491643/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (982610021264954760714492283734926314491643/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0176.bracket2818 BracketBatch0176.bracket2819 (982610021264954760714492283734926314491643/10000000000000000000000000000000000000000) (760622895095191670021557347657837831063/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0176.bracket2818 BracketBatch0176.bracket2819
  (982610021264954760714492283734926314491643/10000000000000000000000000000000000000000) (760622895095191670021557347657837831063/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2818
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2819
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (39342922945817519811298096961190244746651/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (39342922945817519811298096961190244746651/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (985506761533642078804521900926285089296241/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (985506761533642078804521900926285089296241/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (492269958794770018521743581239010301990629/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (492269958794770018521743581239010301990629/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0176.bracket2819 BracketBatch0176.bracket2820 (492269958794770018521743581239010301990629/5000000000000000000000000000000000000000) (760999941448688684418474869857306158203/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0176.bracket2819 BracketBatch0176.bracket2820
  (492269958794770018521743581239010301990629/5000000000000000000000000000000000000000) (760999941448688684418474869857306158203/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2819
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2820
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (492753380766821039402260950463142544648119/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (492753380766821039402260950463142544648119/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (987448077419657706504028222406580565321629/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (987448077419657706504028222406580565321629/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (1972954838953299785308550123332865654617867/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1972954838953299785308550123332865654617867/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0176.bracket2820 BracketBatch0176.bracket2821 (1972954838953299785308550123332865654617867/20000000000000000000000000000000000000000) (1522755479555999601687226634217827167717/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0176.bracket2820 BracketBatch0176.bracket2821
  (1972954838953299785308550123332865654617867/20000000000000000000000000000000000000000) (1522755479555999601687226634217827167717/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2820
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2821
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (493724038709828853252014111203290282660813/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (493724038709828853252014111203290282660813/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (197879413305753380517698439991105937104951/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (197879413305753380517698439991105937104951/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (1976845143948424609092520422362110250846381/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1976845143948424609092520422362110250846381/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0176.bracket2821 BracketBatch0176.bracket2822 (1976845143948424609092520422362110250846381/20000000000000000000000000000000000000000) (3047025171762500728547405794371939977329/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0176.bracket2821 BracketBatch0176.bracket2822
  (1976845143948424609092520422362110250846381/20000000000000000000000000000000000000000) (3047025171762500728547405794371939977329/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2821
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2822
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0440.rows BesselBatch0440.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (61837316658047931411780762497220605345297/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (61837316658047931411780762497220605345297/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (247838443611117936753126909297764765333599/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (247838443611117936753126909297764765333599/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (495187710243309662400249959286647186714787/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (495187710243309662400249959286647186714787/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0176.bracket2822 BracketBatch0176.bracket2823 (495187710243309662400249959286647186714787/5000000000000000000000000000000000000000) (6097084830478932048097520609289918121907/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0176.bracket2822 BracketBatch0176.bracket2823
  (495187710243309662400249959286647186714787/5000000000000000000000000000000000000000) (6097084830478932048097520609289918121907/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2822
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2823
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (991353774444471747012507637191059061334393/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (991353774444471747012507637191059061334393/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (496659123556024072936021770179385714724357/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (496659123556024072936021770179385714724357/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (1984672021556519892884551177549830490783107/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1984672021556519892884551177549830490783107/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0352.rows ScalarLogs0352.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0176.bracket2823 BracketBatch0176.bracket2824 (1984672021556519892884551177549830490783107/20000000000000000000000000000000000000000) (762515675274938697157763033435533342569/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0176.bracket2823 BracketBatch0176.bracket2824
  (1984672021556519892884551177549830490783107/20000000000000000000000000000000000000000) (762515675274938697157763033435533342569/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2823
