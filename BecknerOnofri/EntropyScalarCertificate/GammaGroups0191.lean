module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0238
public import BecknerOnofri.EntropyScalarCertificate.Bessel0239
public import BecknerOnofri.EntropyScalarCertificate.Bessel0240
public import BecknerOnofri.EntropyScalarCertificate.Bessel0608
public import BecknerOnofri.EntropyScalarCertificate.Brackets0095
public import BecknerOnofri.EntropyScalarCertificate.Brackets0096
public import BecknerOnofri.EntropyScalarCertificate.Logs0191
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1528
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (17882324791034359575288506834935682902357/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17882324791034359575288506834935682902357/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (8946194991799288728886290440215674122787/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8946194991799288728886290440215674122787/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (35774714774632937033061087715367031147931/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35774714774632937033061087715367031147931/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0095.bracket1528 BracketBatch0095.bracket1529 (35774714774632937033061087715367031147931/20000000000000000000000000000000000000000) (43132702038987365836548788341222732607/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0095.bracket1528 BracketBatch0095.bracket1529
  (35774714774632937033061087715367031147931/20000000000000000000000000000000000000000) (43132702038987365836548788341222732607/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1528
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1529
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (17892389983598577457772580880431348245571/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17892389983598577457772580880431348245571/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (17902468166134190671359468198551547787667/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17902468166134190671359468198551547787667/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (17897429074866384064566024539491448016619/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17897429074866384064566024539491448016619/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0095.bracket1529 BracketBatch0095.bracket1530 (17897429074866384064566024539491448016619/10000000000000000000000000000000000000000) (690666373719126587250727723219047979349/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0095.bracket1529 BracketBatch0095.bracket1530
  (17897429074866384064566024539491448016619/10000000000000000000000000000000000000000) (690666373719126587250727723219047979349/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1529
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1530
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (1118904260383386916959966762409471736729/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1118904260383386916959966762409471736729/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (8956279682718739104448378254188503985589/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8956279682718739104448378254188503985589/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (17907513765785834440128112353464277879421/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17907513765785834440128112353464277879421/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0095.bracket1530 BracketBatch0095.bracket1531 (17907513765785834440128112353464277879421/10000000000000000000000000000000000000000) (345605042585832417739690572930819386183/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0095.bracket1530 BracketBatch0095.bracket1531
  (17907513765785834440128112353464277879421/10000000000000000000000000000000000000000) (345605042585832417739690572930819386183/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1530
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1531
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (716502374617499128355870260335080318847/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (716502374617499128355870260335080318847/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (4480665902093839775151333840717815242239/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4480665902093839775151333840717815242239/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (35835222973812837309502091871248268940131/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35835222973812837309502091871248268940131/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0095.bracket1531 BracketBatch0095.bracket1532 (35835222973812837309502091871248268940131/20000000000000000000000000000000000000000) (86469295981698750871069931721384160053/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0095.bracket1531 BracketBatch0095.bracket1532
  (35835222973812837309502091871248268940131/20000000000000000000000000000000000000000) (86469295981698750871069931721384160053/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1531
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1532
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (17922663608375359100605335362871260968953/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17922663608375359100605335362871260968953/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (2241597615235701860685922040007592410809/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2241597615235701860685922040007592410809/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (1434217781210438959443708467317280010217/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1434217781210438959443708467317280010217/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0095.bracket1532 BracketBatch0095.bracket1533 (1434217781210438959443708467317280010217/800000000000000000000000000000000000000) (346149611319360230639914663030962174383/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0095.bracket1532 BracketBatch0095.bracket1533
  (1434217781210438959443708467317280010217/800000000000000000000000000000000000000) (346149611319360230639914663030962174383/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1532
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1533
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (17932780921885614885487376320060739286469/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17932780921885614885487376320060739286469/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (17942911332977112903947383013300221127897/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17942911332977112903947383013300221127897/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (17937846127431363894717379666680480207183/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17937846127431363894717379666680480207183/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0095.bracket1533 BracketBatch0095.bracket1534 (17937846127431363894717379666680480207183/10000000000000000000000000000000000000000) (346422325201259378817769582128434452861/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0095.bracket1533 BracketBatch0095.bracket1534
  (17937846127431363894717379666680480207183/10000000000000000000000000000000000000000) (346422325201259378817769582128434452861/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1533
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1534
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (8971455666488556451973691506650110563947/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8971455666488556451973691506650110563947/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (3590610973746006083043288486390854824617/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3590610973746006083043288486390854824617/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (35895966201707143319163825445254495250979/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35895966201707143319163825445254495250979/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0095.bracket1534 BracketBatch0095.bracket1535 (35895966201707143319163825445254495250979/20000000000000000000000000000000000000000) (138678130404418982166466298019302313893/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0095.bracket1534 BracketBatch0095.bracket1535
  (35895966201707143319163825445254495250979/20000000000000000000000000000000000000000) (138678130404418982166466298019302313893/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1534
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1535
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0239.rows BesselBatch0239.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (8976527434365015207608221215977137061541/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8976527434365015207608221215977137061541/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (4490802889074019885797167486258138788139/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4490802889074019885797167486258138788139/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (17958133212513054979202556188493414637819/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17958133212513054979202556188493414637819/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0191.rows ScalarLogs0191.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0095.bracket1535 BracketBatch0096.bracket1536 (17958133212513054979202556188493414637819/10000000000000000000000000000000000000000) (693937228376209654096625765657932340223/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0095.bracket1535 BracketBatch0096.bracket1536
  (17958133212513054979202556188493414637819/10000000000000000000000000000000000000000) (693937228376209654096625765657932340223/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1535
