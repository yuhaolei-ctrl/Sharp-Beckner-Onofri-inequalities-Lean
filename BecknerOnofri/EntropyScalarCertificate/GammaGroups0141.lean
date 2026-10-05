module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0176
public import BecknerOnofri.EntropyScalarCertificate.Bessel0177
public import BecknerOnofri.EntropyScalarCertificate.Bessel0577
public import BecknerOnofri.EntropyScalarCertificate.Brackets0070
public import BecknerOnofri.EntropyScalarCertificate.Brackets0071
public import BecknerOnofri.EntropyScalarCertificate.Logs0141
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1128
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1557376642414287152614152405201586111019/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1557376642414287152614152405201586111019/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (7808086125386704960606877824348531186497/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7808086125386704960606877824348531186497/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (1949371167182267590459704981294557717699/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1949371167182267590459704981294557717699/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0070.bracket1128 BracketBatch0070.bracket1129 (1949371167182267590459704981294557717699/2500000000000000000000000000000000000000) (129740205101956212496733951326465392197/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0070.bracket1128 BracketBatch0070.bracket1129
  (1949371167182267590459704981294557717699/2500000000000000000000000000000000000000) (129740205101956212496733951326465392197/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1128
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1129
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (3904043062693352480303438912174265593247/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3904043062693352480303438912174265593247/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (313174441636021754194360716824622268261/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (313174441636021754194360716824622268261/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (15637447166287248815465895744964087893019/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15637447166287248815465895744964087893019/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0070.bracket1129 BracketBatch0070.bracket1130 (15637447166287248815465895744964087893019/20000000000000000000000000000000000000000) (130695970619567615753817825053086515049/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0070.bracket1129 BracketBatch0070.bracket1130
  (15637447166287248815465895744964087893019/20000000000000000000000000000000000000000) (130695970619567615753817825053086515049/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1129
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1130
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (3914680520450271927429508960307778353261/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3914680520450271927429508960307778353261/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (1962677128172840125038743333681921821899/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1962677128172840125038743333681921821899/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (7840034776795952177506995627671621997059/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7840034776795952177506995627671621997059/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0070.bracket1130 BracketBatch0070.bracket1131 (7840034776795952177506995627671621997059/10000000000000000000000000000000000000000) (131657771765758152265312486376948134533/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0070.bracket1130 BracketBatch0070.bracket1131
  (7840034776795952177506995627671621997059/10000000000000000000000000000000000000000) (131657771765758152265312486376948134533/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1130
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1131
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (7850708512691360500154973334727687287593/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7850708512691360500154973334727687287593/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (984016137585911223061528776375422360051/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (984016137585911223061528776375422360051/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (15722837613378650284647203545731066168001/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15722837613378650284647203545731066168001/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0070.bracket1131 BracketBatch0070.bracket1132 (15722837613378650284647203545731066168001/20000000000000000000000000000000000000000) (16578205663225783214182899169387254821/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0070.bracket1131 BracketBatch0070.bracket1132
  (15722837613378650284647203545731066168001/20000000000000000000000000000000000000000) (16578205663225783214182899169387254821/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1131
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1132
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (1574425820137457956898446042200675776081/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1574425820137457956898446042200675776081/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (7893623370746133114699799852465098304443/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7893623370746133114699799852465098304443/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (985359529464588931199501878966779824053/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (985359529464588931199501878966779824053/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0070.bracket1132 BracketBatch0070.bracket1133 (985359529464588931199501878966779824053/1250000000000000000000000000000000000000) (33399907073294909534535011927916302953/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0070.bracket1132 BracketBatch0070.bracket1133
  (985359529464588931199501878966779824053/1250000000000000000000000000000000000000) (33399907073294909534535011927916302953/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1132
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1133
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (197340584268653327867494996311627457611/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (197340584268653327867494996311627457611/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (7915191894736621006757149042552392691613/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7915191894736621006757149042552392691613/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (15808815265482754121456948895017490996053/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15808815265482754121456948895017490996053/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0070.bracket1133 BracketBatch0070.bracket1134 (15808815265482754121456948895017490996053/20000000000000000000000000000000000000000) (1076638064583680916301883022640341247/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0070.bracket1133 BracketBatch0070.bracket1134
  (15808815265482754121456948895017490996053/20000000000000000000000000000000000000000) (1076638064583680916301883022640341247/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1133
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1134
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (791519189473662100675714904255239269161/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (791519189473662100675714904255239269161/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (496052203163814011309844539767277632671/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (496052203163814011309844539767277632671/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (7926013572678822593857330839414417407173/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7926013572678822593857330839414417407173/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0070.bracket1134 BracketBatch0070.bracket1135 (7926013572678822593857330839414417407173/10000000000000000000000000000000000000000) (135566072285321938452901014114350882677/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0070.bracket1134 BracketBatch0070.bracket1135
  (7926013572678822593857330839414417407173/10000000000000000000000000000000000000000) (135566072285321938452901014114350882677/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1134
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1135
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (7936835250621024180957512636276442122733/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7936835250621024180957512636276442122733/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (1989638505634784831487252829494320528969/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1989638505634784831487252829494320528969/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (15895389273160163506906523954253724238609/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15895389273160163506906523954253724238609/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0141.rows ScalarLogs0141.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0070.bracket1135 BracketBatch0071.bracket1136 (15895389273160163506906523954253724238609/20000000000000000000000000000000000000000) (13655860886906426587196352818622785243/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0070.bracket1135 BracketBatch0071.bracket1136
  (15895389273160163506906523954253724238609/20000000000000000000000000000000000000000) (13655860886906426587196352818622785243/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1135
