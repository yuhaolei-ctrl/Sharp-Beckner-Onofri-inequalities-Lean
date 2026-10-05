module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0193
public import BecknerOnofri.EntropyScalarCertificate.Bessel0194
public import BecknerOnofri.EntropyScalarCertificate.Bessel0195
public import BecknerOnofri.EntropyScalarCertificate.Bessel0585
public import BecknerOnofri.EntropyScalarCertificate.Bessel0586
public import BecknerOnofri.EntropyScalarCertificate.Brackets0077
public import BecknerOnofri.EntropyScalarCertificate.Brackets0078
public import BecknerOnofri.EntropyScalarCertificate.Logs0155
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1240
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (10786982914945248451398220259520759903083/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10786982914945248451398220259520759903083/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (5410896360864729557271553192028369656487/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5410896360864729557271553192028369656487/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (21608775636674707565941326643577499216057/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (21608775636674707565941326643577499216057/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0077.bracket1240 BracketBatch0077.bracket1241 (21608775636674707565941326643577499216057/20000000000000000000000000000000000000000) (71304962666482826145407771756320737101/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0077.bracket1240 BracketBatch0077.bracket1241
  (21608775636674707565941326643577499216057/20000000000000000000000000000000000000000) (71304962666482826145407771756320737101/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1240
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1241
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0193.rows BesselBatch0193.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (10821792721729459114543106384056739312971/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10821792721729459114543106384056739312971/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (10856804943238970994419780324414023956113/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10856804943238970994419780324414023956113/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (5419649416242107527240721677117690817271/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5419649416242107527240721677117690817271/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0077.bracket1241 BracketBatch0077.bracket1242 (5419649416242107527240721677117690817271/5000000000000000000000000000000000000000) (287182069774651858852286071707036756489/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0077.bracket1241 BracketBatch0077.bracket1242
  (5419649416242107527240721677117690817271/5000000000000000000000000000000000000000) (287182069774651858852286071707036756489/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1241
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1242
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (1085680494323897099441978032441402395611/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1085680494323897099441978032441402395611/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (2178404375404199489985613638130205192849/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2178404375404199489985613638130205192849/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (4349765364051993688869569703013009984071/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4349765364051993688869569703013009984071/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0077.bracket1242 BracketBatch0077.bracket1243 (4349765364051993688869569703013009984071/4000000000000000000000000000000000000000) (9036177144697357454474450342430253711/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0077.bracket1242 BracketBatch0077.bracket1243
  (4349765364051993688869569703013009984071/4000000000000000000000000000000000000000) (9036177144697357454474450342430253711/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1242
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1243
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (5446010938510498724964034095325512982121/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5446010938510498724964034095325512982121/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (2731861464107679275977714724511647297783/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2731861464107679275977714724511647297783/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (10909733866725857276919463544348807577687/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10909733866725857276919463544348807577687/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0077.bracket1243 BracketBatch0077.bracket1244 (10909733866725857276919463544348807577687/10000000000000000000000000000000000000000) (291146763102522131615581647064837584097/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0077.bracket1243 BracketBatch0077.bracket1244
  (10909733866725857276919463544348807577687/10000000000000000000000000000000000000000) (291146763102522131615581647064837584097/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1243
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1244
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (10927445856430717103910858898046589191129/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10927445856430717103910858898046589191129/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (2740769812833258330130966779586755416627/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2740769812833258330130966779586755416627/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (21890525107763750424434726016393610857637/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (21890525107763750424434726016393610857637/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0077.bracket1244 BracketBatch0077.bracket1245 (21890525107763750424434726016393610857637/20000000000000000000000000000000000000000) (293149470583139262089923997604239676199/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0077.bracket1244 BracketBatch0077.bracket1245
  (21890525107763750424434726016393610857637/20000000000000000000000000000000000000000) (293149470583139262089923997604239676199/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1244
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1245
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (2192615850266606664104773423669404333301/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2192615850266606664104773423669404333301/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (10998924468820669301225988506770067653007/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10998924468820669301225988506770067653007/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (2745250465019212827718731953139636164939/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2745250465019212827718731953139636164939/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0077.bracket1245 BracketBatch0077.bracket1246 (2745250465019212827718731953139636164939/2500000000000000000000000000000000000000) (295165910013255519221705583227762468761/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0077.bracket1245 BracketBatch0077.bracket1246
  (2745250465019212827718731953139636164939/2500000000000000000000000000000000000000) (295165910013255519221705583227762468761/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1245
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1246
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (2749731117205167325306497126692516913251/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2749731117205167325306497126692516913251/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (551749197697451729682873557713387280971/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (551749197697451729682873557713387280971/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (2754238552846212986860432457629726659053/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2754238552846212986860432457629726659053/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0077.bracket1246 BracketBatch0077.bracket1247 (2754238552846212986860432457629726659053/2500000000000000000000000000000000000000) (74299050477672587500450383207922517851/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0077.bracket1246 BracketBatch0077.bracket1247
  (2754238552846212986860432457629726659053/2500000000000000000000000000000000000000) (74299050477672587500450383207922517851/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1246
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1247
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0194.rows BesselBatch0194.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (11034983953949034593657471154267745619417/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11034983953949034593657471154267745619417/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0195.rows BesselBatch0195.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (11071260190488311797120699415814978732231/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11071260190488311797120699415814978732231/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0586.rows BesselBatch0586.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (690820129513667074711817830315085135989/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (690820129513667074711817830315085135989/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0155.rows ScalarLogs0155.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0077.bracket1247 BracketBatch0078.bracket1248 (690820129513667074711817830315085135989/625000000000000000000000000000000000000) (149620234199035488747461925501563513483/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0077.bracket1247 BracketBatch0078.bracket1248
  (690820129513667074711817830315085135989/625000000000000000000000000000000000000) (149620234199035488747461925501563513483/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1247
