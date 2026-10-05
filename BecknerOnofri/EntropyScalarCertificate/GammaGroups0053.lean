import BecknerOnofri.EntropyScalarCertificate.Bessel0066
import BecknerOnofri.EntropyScalarCertificate.Bessel0067
import BecknerOnofri.EntropyScalarCertificate.Bessel0522
import BecknerOnofri.EntropyScalarCertificate.Brackets0026
import BecknerOnofri.EntropyScalarCertificate.Brackets0027
import BecknerOnofri.EntropyScalarCertificate.Logs0053
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0424
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (356836248813308948202464585736855075317/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (356836248813308948202464585736855075317/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (1429406688270481657054538647604796689807/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1429406688270481657054538647604796689807/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (114270067340948697994575879622088679643/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (114270067340948697994575879622088679643/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0026.bracket0424 BracketBatch0026.bracket0425 (114270067340948697994575879622088679643/800000000000000000000000000000000000000) (62529802029228077184177516650994391/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0026.bracket0424 BracketBatch0026.bracket0425
  (114270067340948697994575879622088679643/800000000000000000000000000000000000000) (62529802029228077184177516650994391/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0424
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0425
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (357351672067620414263634661901199172451/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (357351672067620414263634661901199172451/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (44733392528819054925386353102207740383/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (44733392528819054925386353102207740383/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (143043762459634570733345097343772219103/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (143043762459634570733345097343772219103/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0026.bracket0425 BracketBatch0026.bracket0426 (143043762459634570733345097343772219103/1000000000000000000000000000000000000000) (314432503121356247054025339185036579/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0026.bracket0425 BracketBatch0026.bracket0426
  (143043762459634570733345097343772219103/1000000000000000000000000000000000000000) (314432503121356247054025339185036579/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0425
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0426
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (1431468560922209757612363299270647692253/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1431468560922209757612363299270647692253/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (179191326686416156301773519232118755239/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (179191326686416156301773519232118755239/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (572999834882707801605310290625519546833/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (572999834882707801605310290625519546833/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0026.bracket0426 BracketBatch0026.bracket0427 (572999834882707801605310290625519546833/4000000000000000000000000000000000000000) (316223637005407705370706778069073497/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0026.bracket0426 BracketBatch0026.bracket0427
  (572999834882707801605310290625519546833/4000000000000000000000000000000000000000) (316223637005407705370706778069073497/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0426
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0427
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1433530613491329250414188153856950041909/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1433530613491329250414188153856950041909/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (1435592846260878948076980546675064826029/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1435592846260878948076980546675064826029/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (1434561729876104099245584350266007433969/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1434561729876104099245584350266007433969/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0026.bracket0427 BracketBatch0026.bracket0428 (1434561729876104099245584350266007433969/10000000000000000000000000000000000000000) (159011216929177551004266571068920859/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0026.bracket0427 BracketBatch0026.bracket0428
  (1434561729876104099245584350266007433969/10000000000000000000000000000000000000000) (159011216929177551004266571068920859/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0427
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0428
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (717796423130439474038490273337532413013/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (717796423130439474038490273337532413013/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (1437655259514027552483507605553561394859/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1437655259514027552483507605553561394859/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (574649621154981300112097630445725244177/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (574649621154981300112097630445725244177/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0026.bracket0428 BracketBatch0026.bracket0429 (574649621154981300112097630445725244177/4000000000000000000000000000000000000000) (31982891577398588917763030810739221/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0026.bracket0428 BracketBatch0026.bracket0429
  (574649621154981300112097630445725244177/4000000000000000000000000000000000000000) (31982891577398588917763030810739221/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0428
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0429
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (179706907439253444060438450694195174357/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (179706907439253444060438450694195174357/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (1439717853534073887592566894839547142103/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1439717853534073887592566894839547142103/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (2877373113048101440076074500393108536959/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2877373113048101440076074500393108536959/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0026.bracket0429 BracketBatch0026.bracket0430 (2877373113048101440076074500393108536959/20000000000000000000000000000000000000000) (80410776219956497968248094641243861/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0026.bracket0429 BracketBatch0026.bracket0430
  (2877373113048101440076074500393108536959/20000000000000000000000000000000000000000) (80410776219956497968248094641243861/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0429
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0430
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (14397178535340738875925668948395471421/100000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14397178535340738875925668948395471421/100000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (1441780628604447132480240427409388968797/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1441780628604447132480240427409388968797/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (2881498482138521020072807322248936110897/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2881498482138521020072807322248936110897/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0026.bracket0430 BracketBatch0026.bracket0431 (2881498482138521020072807322248936110897/20000000000000000000000000000000000000000) (323465023337151189197114262405175559/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0026.bracket0430 BracketBatch0026.bracket0431
  (2881498482138521020072807322248936110897/20000000000000000000000000000000000000000) (323465023337151189197114262405175559/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0430
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0431
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (720890314302223566240120213704694484397/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (720890314302223566240120213704694484397/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (288768717001741410922530768606330530411/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (288768717001741410922530768606330530411/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (2885624213613154187092894270441041620849/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2885624213613154187092894270441041620849/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0053.rows ScalarLogs0053.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0026.bracket0431 BracketBatch0027.bracket0432 (2885624213613154187092894270441041620849/20000000000000000000000000000000000000000) (13011787733639940612383546860728959/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0026.bracket0431 BracketBatch0027.bracket0432
  (2885624213613154187092894270441041620849/20000000000000000000000000000000000000000) (13011787733639940612383546860728959/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0431
