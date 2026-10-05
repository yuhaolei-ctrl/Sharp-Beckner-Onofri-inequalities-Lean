module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0388
public import BecknerOnofri.EntropyScalarCertificate.Bessel0389
public import BecknerOnofri.EntropyScalarCertificate.Bessel0390
public import BecknerOnofri.EntropyScalarCertificate.Bessel0683
public import BecknerOnofri.EntropyScalarCertificate.Brackets0155
public import BecknerOnofri.EntropyScalarCertificate.Brackets0156
public import BecknerOnofri.EntropyScalarCertificate.Logs0311
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2488
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (160888869631727273312011981830131043878903/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (160888869631727273312011981830131043878903/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (322601640648868081697021656754309414790597/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (322601640648868081697021656754309414790597/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (644379379912322628321045620414571502548403/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (644379379912322628321045620414571502548403/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0155.bracket2488 BracketBatch0155.bracket2489 (644379379912322628321045620414571502548403/20000000000000000000000000000000000000000) (1099851813363170196020899865792709210081/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0155.bracket2488 BracketBatch0155.bracket2489
  (644379379912322628321045620414571502548403/20000000000000000000000000000000000000000) (1099851813363170196020899865792709210081/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2488
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2489
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (161300820324434040848510828377154707395297/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (161300820324434040848510828377154707395297/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (64685957830782295696885846042074937776717/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (64685957830782295696885846042074937776717/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (646031429802779560181450886964684103674179/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (646031429802779560181450886964684103674179/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0155.bracket2489 BracketBatch0155.bracket2490 (646031429802779560181450886964684103674179/20000000000000000000000000000000000000000) (4403119854417852732193879627689737636873/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0155.bracket2489 BracketBatch0155.bracket2490
  (646031429802779560181450886964684103674179/20000000000000000000000000000000000000000) (4403119854417852732193879627689737636873/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2489
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2490
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (161714894576955739242214615105187344441791/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (161714894576955739242214615105187344441791/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (162131108850979976884560014173986679515441/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (162131108850979976884560014173986679515441/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (20240375214245982257923414329948376497327/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20240375214245982257923414329948376497327/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0155.bracket2490 BracketBatch0155.bracket2491 (20240375214245982257923414329948376497327/625000000000000000000000000000000000000) (4406842508292222133398212245642689452821/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0155.bracket2490 BracketBatch0155.bracket2491
  (20240375214245982257923414329948376497327/625000000000000000000000000000000000000) (4406842508292222133398212245642689452821/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2490
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2491
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (324262217701959953769120028347973359030879/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (324262217701959953769120028347973359030879/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (325098959557563607594190354891500139071191/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (325098959557563607594190354891500139071191/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (64936117725952356136331038323947349810207/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (64936117725952356136331038323947349810207/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0155.bracket2491 BracketBatch0155.bracket2492 (64936117725952356136331038323947349810207/2000000000000000000000000000000000000000) (4410575266380687326404383699112399916389/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0155.bracket2491 BracketBatch0155.bracket2492
  (64936117725952356136331038323947349810207/2000000000000000000000000000000000000000) (4410575266380687326404383699112399916389/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2491
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2492
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (81274739889390901898547588722875034767797/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (81274739889390901898547588722875034767797/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (65188009666175653179388428952237152263563/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (65188009666175653179388428952237152263563/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (651039007888441873491132499652685900389003/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (651039007888441873491132499652685900389003/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0155.bracket2492 BracketBatch0155.bracket2493 (651039007888441873491132499652685900389003/20000000000000000000000000000000000000000) (882863636073909437625292402546880909683/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0155.bracket2492 BracketBatch0155.bracket2493
  (651039007888441873491132499652685900389003/20000000000000000000000000000000000000000) (882863636073909437625292402546880909683/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2492
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2493
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (81485012082719566474235536190296440329453/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (81485012082719566474235536190296440329453/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (163392758991082777529513180736475839369681/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (163392758991082777529513180736475839369681/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (326362783156521910477984253117068720028587/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (326362783156521910477984253117068720028587/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0155.bracket2493 BracketBatch0155.bracket2494 (326362783156521910477984253117068720028587/10000000000000000000000000000000000000000) (441807130233017569569391609425565583867/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0155.bracket2493 BracketBatch0155.bracket2494
  (326362783156521910477984253117068720028587/10000000000000000000000000000000000000000) (441807130233017569569391609425565583867/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2493
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2494
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (326785517982165555059026361472951678739359/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (326785517982165555059026361472951678739359/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (10238606338323858553375919549613900753273/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10238606338323858553375919549613900753273/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (130884184161705805753411157412119300568819/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (130884184161705805753411157412119300568819/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0155.bracket2494 BracketBatch0155.bracket2495 (130884184161705805753411157412119300568819/4000000000000000000000000000000000000000) (2210917342361369557958727899902630184481/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0155.bracket2494 BracketBatch0155.bracket2495
  (130884184161705805753411157412119300568819/4000000000000000000000000000000000000000) (2210917342361369557958727899902630184481/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2494
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2495
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0389.rows BesselBatch0389.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (327635402826363473708029425587644824104733/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (327635402826363473708029425587644824104733/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (41061217192216094200619149434909280792481/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (41061217192216094200619149434909280792481/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (656125140364092227312982621066919070444581/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (656125140364092227312982621066919070444581/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0311.rows ScalarLogs0311.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0155.bracket2495 BracketBatch0156.bracket2496 (656125140364092227312982621066919070444581/20000000000000000000000000000000000000000) (4425608380399956382873371442431635886781/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0155.bracket2495 BracketBatch0156.bracket2496
  (656125140364092227312982621066919070444581/20000000000000000000000000000000000000000) (4425608380399956382873371442431635886781/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2495
