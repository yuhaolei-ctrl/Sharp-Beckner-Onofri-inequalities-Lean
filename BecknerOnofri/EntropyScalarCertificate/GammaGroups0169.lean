module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0211
public import BecknerOnofri.EntropyScalarCertificate.Bessel0212
public import BecknerOnofri.EntropyScalarCertificate.Bessel0594
public import BecknerOnofri.EntropyScalarCertificate.Bessel0595
public import BecknerOnofri.EntropyScalarCertificate.Brackets0084
public import BecknerOnofri.EntropyScalarCertificate.Brackets0085
public import BecknerOnofri.EntropyScalarCertificate.Logs0169
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1352
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (774583636992607666432292748121735750093/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (774583636992607666432292748121735750093/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (15528094194079194611202390360124867890623/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15528094194079194611202390360124867890623/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (31019766933931347939848245322559582892483/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (31019766933931347939848245322559582892483/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0084.bracket1352 BracketBatch0084.bracket1353 (31019766933931347939848245322559582892483/20000000000000000000000000000000000000000) (278224344912986440693152982819944220829/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0084.bracket1352 BracketBatch0084.bracket1353
  (31019766933931347939848245322559582892483/20000000000000000000000000000000000000000) (278224344912986440693152982819944220829/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1352
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1353
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (776404709703959730560119518006243394531/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (776404709703959730560119518006243394531/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (7782353692779182537041850561958568288299/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7782353692779182537041850561958568288299/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (15546400789818779842643045742021002233609/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15546400789818779842643045742021002233609/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0084.bracket1353 BracketBatch0084.bracket1354 (15546400789818779842643045742021002233609/10000000000000000000000000000000000000000) (558506186546552949285431886295922437209/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0084.bracket1353 BracketBatch0084.bracket1354
  (15546400789818779842643045742021002233609/10000000000000000000000000000000000000000) (558506186546552949285431886295922437209/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1353
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1354
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (3112941477111673014816740224783427315319/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3112941477111673014816740224783427315319/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (7800757009838646572368701538135493262791/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7800757009838646572368701538135493262791/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (31166221405235658218821104200188123102177/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (31166221405235658218821104200188123102177/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0084.bracket1354 BracketBatch0084.bracket1355 (31166221405235658218821104200188123102177/20000000000000000000000000000000000000000) (140143294688049883991826069491450600529/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0084.bracket1354 BracketBatch0084.bracket1355
  (31166221405235658218821104200188123102177/20000000000000000000000000000000000000000) (140143294688049883991826069491450600529/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1354
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1355
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (15601514019677293144737403076270986525579/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15601514019677293144737403076270986525579/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (3127703164328042646722340671717983104499/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3127703164328042646722340671717983104499/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (15620014920658753189174553217430451024037/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15620014920658753189174553217430451024037/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0084.bracket1355 BracketBatch0084.bracket1356 (15620014920658753189174553217430451024037/10000000000000000000000000000000000000000) (562649731674584363390161305626396665967/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0084.bracket1355 BracketBatch0084.bracket1356
  (15620014920658753189174553217430451024037/10000000000000000000000000000000000000000) (562649731674584363390161305626396665967/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1355
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1356
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0211.rows BesselBatch0211.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (3909628955410053308402925839647478880623/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3909628955410053308402925839647478880623/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (15675714536744705979888977680152001831803/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15675714536744705979888977680152001831803/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (6262846071676983842700136207748383470859/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6262846071676983842700136207748383470859/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0084.bracket1356 BracketBatch0084.bracket1357 (6262846071676983842700136207748383470859/4000000000000000000000000000000000000000) (112947182228381982972980308807041254653/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0084.bracket1356 BracketBatch0084.bracket1357
  (6262846071676983842700136207748383470859/4000000000000000000000000000000000000000) (112947182228381982972980308807041254653/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1356
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1357
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (78378572683723529899444888400760009159/50000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (78378572683723529899444888400760009159/50000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (3928277982665723401325636373389132807481/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3928277982665723401325636373389132807481/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0594.rows BesselBatch0594.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (7847206616851899896297880793427133265431/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7847206616851899896297880793427133265431/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0084.bracket1357 BracketBatch0084.bracket1358 (7847206616851899896297880793427133265431/5000000000000000000000000000000000000000) (566831783584914442872869973004881947237/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0084.bracket1357 BracketBatch0084.bracket1358
  (7847206616851899896297880793427133265431/5000000000000000000000000000000000000000) (566831783584914442872869973004881947237/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1357
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1358
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (15713111930662893605302545493556531229921/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15713111930662893605302545493556531229921/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (15750709789727171902094281015212261156013/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15750709789727171902094281015212261156013/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (15731910860195032753698413254384396192967/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15731910860195032753698413254384396192967/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0084.bracket1358 BracketBatch0084.bracket1359 (15731910860195032753698413254384396192967/10000000000000000000000000000000000000000) (568937416042934729209866375257791430547/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0084.bracket1358 BracketBatch0084.bracket1359
  (15731910860195032753698413254384396192967/10000000000000000000000000000000000000000) (568937416042934729209866375257791430547/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1358
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1359
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1575070978972717190209428101521226115601/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1575070978972717190209428101521226115601/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (3947127480305140523431483137679247498087/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3947127480305140523431483137679247498087/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (15769609855473866997910106782964625574179/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15769609855473866997910106782964625574179/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0169.rows ScalarLogs0169.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0084.bracket1359 BracketBatch0085.bracket1360 (15769609855473866997910106782964625574179/10000000000000000000000000000000000000000) (571052876170027050275080537026348550447/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0084.bracket1359 BracketBatch0085.bracket1360
  (15769609855473866997910106782964625574179/10000000000000000000000000000000000000000) (571052876170027050275080537026348550447/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1359
