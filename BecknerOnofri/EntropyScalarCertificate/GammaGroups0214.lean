import BecknerOnofri.EntropyScalarCertificate.Bessel0267
import BecknerOnofri.EntropyScalarCertificate.Bessel0268
import BecknerOnofri.EntropyScalarCertificate.Bessel0622
import BecknerOnofri.EntropyScalarCertificate.Bessel0623
import BecknerOnofri.EntropyScalarCertificate.Brackets0107
import BecknerOnofri.EntropyScalarCertificate.Logs0214
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1712
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (19984069536703032118120673080413474959061/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19984069536703032118120673080413474959061/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (19997060031028974832625975807117880998359/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19997060031028974832625975807117880998359/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (1999056478386600347537332444376567797871/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1999056478386600347537332444376567797871/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0107.bracket1712 BracketBatch0107.bracket1713 (1999056478386600347537332444376567797871/1000000000000000000000000000000000000000) (800636183936915866622416628730163933027/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0107.bracket1712 BracketBatch0107.bracket1713
  (1999056478386600347537332444376567797871/1000000000000000000000000000000000000000) (800636183936915866622416628730163933027/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1712
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1713
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (4999265007757243708156493951779470249589/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4999265007757243708156493951779470249589/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (2001006990740508320147686238937070067799/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2001006990740508320147686238937070067799/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (20003564969217029017051419098244290838173/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20003564969217029017051419098244290838173/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0107.bracket1713 BracketBatch0107.bracket1714 (20003564969217029017051419098244290838173/10000000000000000000000000000000000000000) (32052031755224017668396831077638629947/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0107.bracket1713 BracketBatch0107.bracket1714
  (20003564969217029017051419098244290838173/10000000000000000000000000000000000000000) (32052031755224017668396831077638629947/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1713
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1714
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (20010069907405083201476862389370700677987/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20010069907405083201476862389370700677987/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (20023099210414076351773118598223645227169/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20023099210414076351773118598223645227169/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (10008292279454789888312495246898586476289/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10008292279454789888312495246898586476289/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0107.bracket1714 BracketBatch0107.bracket1715 (10008292279454789888312495246898586476289/5000000000000000000000000000000000000000) (801966165982083616627837869133739563239/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0107.bracket1714 BracketBatch0107.bracket1715
  (10008292279454789888312495246898586476289/5000000000000000000000000000000000000000) (801966165982083616627837869133739563239/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1714
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1715
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (10011549605207038175886559299111822613583/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10011549605207038175886559299111822613583/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (1252259249048053624903413186650985480347/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1252259249048053624903413186650985480347/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (20029623597591467175113864792319706456359/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20029623597591467175113864792319706456359/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0107.bracket1715 BracketBatch0107.bracket1716 (20029623597591467175113864792319706456359/10000000000000000000000000000000000000000) (5016451884242891467226911073415382197/62500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0107.bracket1715 BracketBatch0107.bracket1716
  (20029623597591467175113864792319706456359/10000000000000000000000000000000000000000) (5016451884242891467226911073415382197/62500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1715
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1716
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (20036147984768857998454610986415767685549/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20036147984768857998454610986415767685549/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (4009843255062595378030661095774227442273/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4009843255062595378030661095774227442273/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (20042682130040917444303958232643452448457/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20042682130040917444303958232643452448457/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0107.bracket1716 BracketBatch0107.bracket1717 (20042682130040917444303958232643452448457/10000000000000000000000000000000000000000) (160659840322165806634743919426962407301/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0107.bracket1716 BracketBatch0107.bracket1717
  (20042682130040917444303958232643452448457/10000000000000000000000000000000000000000) (160659840322165806634743919426962407301/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1716
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1717
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (10024608137656488445076652739435568605681/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10024608137656488445076652739435568605681/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (10031152063510544612597179516437407496293/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10031152063510544612597179516437407496293/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (10027880100583516528836916127936488050987/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10027880100583516528836916127936488050987/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0107.bracket1717 BracketBatch0107.bracket1718 (10027880100583516528836916127936488050987/5000000000000000000000000000000000000000) (803966867620273908018572711286298443593/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0107.bracket1717 BracketBatch0107.bracket1718
  (10027880100583516528836916127936488050987/5000000000000000000000000000000000000000) (803966867620273908018572711286298443593/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1717
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1718
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (20062304127021089225194359032874814992583/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20062304127021089225194359032874814992583/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (10037705792499711524000999407752679511373/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10037705792499711524000999407752679511373/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (40137715712020512273196357848380174015329/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (40137715712020512273196357848380174015329/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0107.bracket1718 BracketBatch0107.bracket1719 (40137715712020512273196357848380174015329/20000000000000000000000000000000000000000) (160927060150378639485549691971266822939/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0107.bracket1718 BracketBatch0107.bracket1719
  (40137715712020512273196357848380174015329/20000000000000000000000000000000000000000) (160927060150378639485549691971266822939/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1718
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1719
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (20075411584999423048001998815505359022743/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20075411584999423048001998815505359022743/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0268.rows BesselBatch0268.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (10044269347243122318114652399864899079829/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10044269347243122318114652399864899079829/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (40163950279485667684231303615235157182401/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (40163950279485667684231303615235157182401/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0214.rows ScalarLogs0214.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0107.bracket1719 BracketBatch0107.bracket1720 (40163950279485667684231303615235157182401/20000000000000000000000000000000000000000) (805304502252792982161337869690761545471/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0107.bracket1719 BracketBatch0107.bracket1720
  (40163950279485667684231303615235157182401/20000000000000000000000000000000000000000) (805304502252792982161337869690761545471/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1719
