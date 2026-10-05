module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0143
public import BecknerOnofri.EntropyScalarCertificate.Bessel0144
public import BecknerOnofri.EntropyScalarCertificate.Bessel0145
public import BecknerOnofri.EntropyScalarCertificate.Bessel0560
public import BecknerOnofri.EntropyScalarCertificate.Bessel0561
public import BecknerOnofri.EntropyScalarCertificate.Brackets0057
public import BecknerOnofri.EntropyScalarCertificate.Brackets0058
public import BecknerOnofri.EntropyScalarCertificate.Logs0115
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0920
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (219829565741959972423613954391174367301/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (219829565741959972423613954391174367301/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (440971692603789616192484327550408500163/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (440971692603789616192484327550408500163/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (176126164817541912207942447266551446953/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (176126164817541912207942447266551446953/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0057.bracket0920 BracketBatch0057.bracket0921 (176126164817541912207942447266551446953/400000000000000000000000000000000000000) (21791368334689874258949200172660337743/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0057.bracket0920 BracketBatch0057.bracket0921
  (176126164817541912207942447266551446953/400000000000000000000000000000000000000) (21791368334689874258949200172660337743/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0920
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0921
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0143.rows BesselBatch0143.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (4409716926037896161924843275504085001627/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4409716926037896161924843275504085001627/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (1105715627034589570382275864445639586217/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1105715627034589570382275864445639586217/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (1766515886835250888690789346657328669299/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1766515886835250888690789346657328669299/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0057.bracket0921 BracketBatch0057.bracket0922 (1766515886835250888690789346657328669299/4000000000000000000000000000000000000000) (22017532149428166622151413413787354279/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0057.bracket0921 BracketBatch0057.bracket0922
  (1766515886835250888690789346657328669299/4000000000000000000000000000000000000000) (22017532149428166622151413413787354279/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0921
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0922
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (884572501627671656305820691556511668973/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (884572501627671656305820691556511668973/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (554503520814310597411314092901153616023/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (554503520814310597411314092901153616023/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (8858890674652843060819616200991787273049/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8858890674652843060819616200991787273049/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0057.bracket0922 BracketBatch0057.bracket0923 (8858890674652843060819616200991787273049/20000000000000000000000000000000000000000) (1112276172402035281536616794191274811/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0057.bracket0922 BracketBatch0057.bracket0923
  (8858890674652843060819616200991787273049/20000000000000000000000000000000000000000) (1112276172402035281536616794191274811/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0922
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0923
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (4436028166514484779290512743209228928181/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4436028166514484779290512743209228928181/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (4449214007178496365949196844700730858657/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4449214007178496365949196844700730858657/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (4442621086846490572619854793954979893419/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4442621086846490572619854793954979893419/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0057.bracket0923 BracketBatch0057.bracket0924 (4442621086846490572619854793954979893419/10000000000000000000000000000000000000000) (5618838320974093076377877657022757343/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0057.bracket0923 BracketBatch0057.bracket0924
  (4442621086846490572619854793954979893419/10000000000000000000000000000000000000000) (5618838320974093076377877657022757343/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0923
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0924
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (2224607003589248182974598422350365429327/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2224607003589248182974598422350365429327/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (4462420136786432896491124645528333706981/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4462420136786432896491124645528333706981/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (1782326828792985852488064298045812913127/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1782326828792985852488064298045812913127/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0057.bracket0924 BracketBatch0057.bracket0925 (1782326828792985852488064298045812913127/4000000000000000000000000000000000000000) (22707032762776495199257592779087860451/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0057.bracket0924 BracketBatch0057.bracket0925
  (1782326828792985852488064298045812913127/4000000000000000000000000000000000000000) (22707032762776495199257592779087860451/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0924
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0925
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (2231210068393216448245562322764166853489/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2231210068393216448245562322764166853489/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (4475646662643707060026172058369609862509/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4475646662643707060026172058369609862509/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (8938066799430139956517296703897943569487/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8938066799430139956517296703897943569487/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0057.bracket0925 BracketBatch0057.bracket0926 (8938066799430139956517296703897943569487/20000000000000000000000000000000000000000) (22940573043166648757133030071430683343/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0057.bracket0925 BracketBatch0057.bracket0926
  (8938066799430139956517296703897943569487/20000000000000000000000000000000000000000) (22940573043166648757133030071430683343/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0925
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0926
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (2237823331321853530013086029184804931253/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2237823331321853530013086029184804931253/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (561111711588839380564846318005333409581/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (561111711588839380564846318005333409581/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (4482270177677211052272471301206138569577/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4482270177677211052272471301206138569577/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0057.bracket0926 BracketBatch0057.bracket0927 (4482270177677211052272471301206138569577/10000000000000000000000000000000000000000) (23175985336551147709979995190789092527/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0057.bracket0926 BracketBatch0057.bracket0927
  (4482270177677211052272471301206138569577/10000000000000000000000000000000000000000) (23175985336551147709979995190789092527/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0926
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0927
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0144.rows BesselBatch0144.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (897778738542143008903754108808533455329/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (897778738542143008903754108808533455329/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0145.rows BesselBatch0145.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (2251080667804252438285787492821449322807/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2251080667804252438285787492821449322807/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0561.rows BesselBatch0561.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (8991055028319219921090345529685565922259/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8991055028319219921090345529685565922259/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0115.rows ScalarLogs0115.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0057.bracket0927 BracketBatch0058.bracket0928 (8991055028319219921090345529685565922259/20000000000000000000000000000000000000000) (4682656181542053754261696273490060843/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0057.bracket0927 BracketBatch0058.bracket0928
  (8991055028319219921090345529685565922259/20000000000000000000000000000000000000000) (4682656181542053754261696273490060843/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0927
