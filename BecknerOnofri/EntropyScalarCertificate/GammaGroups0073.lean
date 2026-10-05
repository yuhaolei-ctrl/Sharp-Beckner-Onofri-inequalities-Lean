import BecknerOnofri.EntropyScalarCertificate.Bessel0091
import BecknerOnofri.EntropyScalarCertificate.Bessel0092
import BecknerOnofri.EntropyScalarCertificate.Bessel0534
import BecknerOnofri.EntropyScalarCertificate.Bessel0535
import BecknerOnofri.EntropyScalarCertificate.Brackets0036
import BecknerOnofri.EntropyScalarCertificate.Brackets0037
import BecknerOnofri.EntropyScalarCertificate.Logs0073
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0584
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1759693960289907930465678516683835393253/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1759693960289907930465678516683835393253/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (880894043301808171225303572807288460063/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (880894043301808171225303572807288460063/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (3521482046893524272916285662298412313379/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3521482046893524272916285662298412313379/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0036.bracket0584 BracketBatch0036.bracket0585 (3521482046893524272916285662298412313379/20000000000000000000000000000000000000000) (142173773300344541387342589204917421/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0036.bracket0584 BracketBatch0036.bracket0585
  (3521482046893524272916285662298412313379/20000000000000000000000000000000000000000) (142173773300344541387342589204917421/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0584
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0585
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (1761788086603616342450607145614576920123/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1761788086603616342450607145614576920123/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (881941219814394202703467900687201680617/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (881941219814394202703467900687201680617/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (3525670526232404747857542946988980281357/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3525670526232404747857542946988980281357/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0036.bracket0585 BracketBatch0036.bracket0586 (3525670526232404747857542946988980281357/20000000000000000000000000000000000000000) (714178341703920200669841944233374667/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0036.bracket0585 BracketBatch0036.bracket0586
  (3525670526232404747857542946988980281357/20000000000000000000000000000000000000000) (714178341703920200669841944233374667/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0585
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0586
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (1763882439628788405406935801374403361231/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1763882439628788405406935801374403361231/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (882988509836102258976693904598090989061/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (882988509836102258976693904598090989061/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (3529859459300992923360323610570585339353/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3529859459300992923360323610570585339353/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0036.bracket0586 BracketBatch0036.bracket0587 (3529859459300992923360323610570585339353/20000000000000000000000000000000000000000) (717499424107434958297880877639368167/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0036.bracket0586 BracketBatch0036.bracket0587
  (3529859459300992923360323610570585339353/20000000000000000000000000000000000000000) (717499424107434958297880877639368167/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0586
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0587
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1765977019672204517953387809196181978119/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1765977019672204517953387809196181978119/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (884035913520407612264229312149893127633/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (884035913520407612264229312149893127633/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (706809769342603948496369286699193646677/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (706809769342603948496369286699193646677/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0036.bracket0587 BracketBatch0036.bracket0588 (706809769342603948496369286699193646677/4000000000000000000000000000000000000000) (720832141325045743426161381932300247/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0036.bracket0587 BracketBatch0036.bracket0588
  (706809769342603948496369286699193646677/4000000000000000000000000000000000000000) (720832141325045743426161381932300247/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0587
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0588
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0091.rows BesselBatch0091.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (1768071827040815224528458624299786255263/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1768071827040815224528458624299786255263/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (1770166862041741491537967946846323834547/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1770166862041741491537967946846323834547/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (353823868908255671606642657114611008981/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (353823868908255671606642657114611008981/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0036.bracket0588 BracketBatch0036.bracket0589 (353823868908255671606642657114611008981/2000000000000000000000000000000000000000) (362088260502667014679416641321944063/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0036.bracket0588 BracketBatch0036.bracket0589
  (353823868908255671606642657114611008981/2000000000000000000000000000000000000000) (362088260502667014679416641321944063/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0588
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0589
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (110635428877608843221122996677895239659/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (110635428877608843221122996677895239659/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (1772262124982274983821161649694630746271/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1772262124982274983821161649694630746271/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0534.rows BesselBatch0534.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (708485797404803295071825919308190916163/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (708485797404803295071825919308190916163/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0036.bracket0589 BracketBatch0036.bracket0590 (708485797404803295071825919308190916163/4000000000000000000000000000000000000000) (363766295416349365094867320998771749/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0036.bracket0589 BracketBatch0036.bracket0590
  (708485797404803295071825919308190916163/4000000000000000000000000000000000000000) (363766295416349365094867320998771749/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0589
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0590
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (443065531245568745955290412423657686567/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (443065531245568745955290412423657686567/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (1774357616169878341435992976532800770733/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1774357616169878341435992976532800770733/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (3546619741152153325257154626227431517001/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3546619741152153325257154626227431517001/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0036.bracket0590 BracketBatch0036.bracket0591 (3546619741152153325257154626227431517001/20000000000000000000000000000000000000000) (730900378527370954646612551831066561/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0036.bracket0590 BracketBatch0036.bracket0591
  (3546619741152153325257154626227431517001/20000000000000000000000000000000000000000) (730900378527370954646612551831066561/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0590
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0591
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (177435761616987834143599297653280077073/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (177435761616987834143599297653280077073/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (44411333397804636419105339645611409141/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (44411333397804636419105339645611409141/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (355081095208206379820020656235725713637/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (355081095208206379820020656235725713637/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0073.rows ScalarLogs0073.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0036.bracket0591 BracketBatch0037.bracket0592 (355081095208206379820020656235725713637/2000000000000000000000000000000000000000) (734279911845428782711762000095830781/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0036.bracket0591 BracketBatch0037.bracket0592
  (355081095208206379820020656235725713637/2000000000000000000000000000000000000000) (734279911845428782711762000095830781/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0591
