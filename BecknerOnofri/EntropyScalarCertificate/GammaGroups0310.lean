module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0387
public import BecknerOnofri.EntropyScalarCertificate.Bessel0388
public import BecknerOnofri.EntropyScalarCertificate.Bessel0682
public import BecknerOnofri.EntropyScalarCertificate.Bessel0683
public import BecknerOnofri.EntropyScalarCertificate.Brackets0155
public import BecknerOnofri.EntropyScalarCertificate.Logs0310
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2480
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (315335582874902388001991781726727005120001/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (315335582874902388001991781726727005120001/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (316126653013229452604470662991256334389279/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (316126653013229452604470662991256334389279/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (3946638974300824003790390279487395871933/125000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3946638974300824003790390279487395871933/125000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0155.bracket2480 BracketBatch0155.bracket2481 (3946638974300824003790390279487395871933/125000000000000000000000000000000000000) (437006231689781091570359764452517986889/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0155.bracket2480 BracketBatch0155.bracket2481
  (3946638974300824003790390279487395871933/125000000000000000000000000000000000000) (437006231689781091570359764452517986889/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2480
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2481
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (79031663253307363151117665747814083597319/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (79031663253307363151117665747814083597319/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (316921718656667137812206878857188864448393/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (316921718656667137812206878857188864448393/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (633048371669896590416677541848445198837669/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (633048371669896590416677541848445198837669/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0155.bracket2481 BracketBatch0155.bracket2482 (633048371669896590416677541848445198837669/20000000000000000000000000000000000000000) (1093424074244364836157239933124326637559/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0155.bracket2481 BracketBatch0155.bracket2482
  (633048371669896590416677541848445198837669/20000000000000000000000000000000000000000) (1093424074244364836157239933124326637559/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2481
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2482
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (31692171865666713781220687885718886444839/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (31692171865666713781220687885718886444839/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (317720810150791693045626421391163443836469/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (317720810150791693045626421391163443836469/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (634642528807458830857833300248352308284859/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (634642528807458830857833300248352308284859/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0155.bracket2482 BracketBatch0155.bracket2483 (634642528807458830857833300248352308284859/20000000000000000000000000000000000000000) (547167491603778313126567581409891367083/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0155.bracket2482 BracketBatch0155.bracket2483
  (634642528807458830857833300248352308284859/20000000000000000000000000000000000000000) (547167491603778313126567581409891367083/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2482
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2483
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (158860405075395846522813210695581721918233/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (158860405075395846522813210695581721918233/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (318523958149256294341410177132667221551187/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (318523958149256294341410177132667221551187/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (636244768300047987387036598523830665387653/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (636244768300047987387036598523830665387653/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0155.bracket2483 BracketBatch0155.bracket2484 (636244768300047987387036598523830665387653/20000000000000000000000000000000000000000) (4380993272837154381555817836812224525053/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0155.bracket2483 BracketBatch0155.bracket2484
  (636244768300047987387036598523830665387653/20000000000000000000000000000000000000000) (4380993272837154381555817836812224525053/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2483
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2484
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (19907747384328518396338136070791701346949/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19907747384328518396338136070791701346949/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (9979099800553456191267409749616180325971/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9979099800553456191267409749616180325971/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (39865946985435430778872955570024061998891/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (39865946985435430778872955570024061998891/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0155.bracket2484 BracketBatch0155.bracket2485 (39865946985435430778872955570024061998891/1250000000000000000000000000000000000000) (4384656365732758804408412844912593482969/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0155.bracket2484 BracketBatch0155.bracket2485
  (39865946985435430778872955570024061998891/1250000000000000000000000000000000000000) (4384656365732758804408412844912593482969/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2484
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2485
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (319331193617710598120557111987717770431069/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (319331193617710598120557111987717770431069/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (32014254783778028812637148314582987069053/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (32014254783778028812637148314582987069053/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (639473741455490886246928595133547641121599/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (639473741455490886246928595133547641121599/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0155.bracket2485 BracketBatch0155.bracket2486 (639473741455490886246928595133547641121599/20000000000000000000000000000000000000000) (1097082315152095568102931583830376929577/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0155.bracket2485 BracketBatch0155.bracket2486
  (639473741455490886246928595133547641121599/20000000000000000000000000000000000000000) (1097082315152095568102931583830376929577/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2485
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2486
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (320142547837780288126371483145829870690527/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (320142547837780288126371483145829870690527/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (32095805241110768957889445159498834529079/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (32095805241110768957889445159498834529079/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (641100600248887977705265934740818215981317/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (641100600248887977705265934740818215981317/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0155.bracket2486 BracketBatch0155.bracket2487 (641100600248887977705265934740818215981317/20000000000000000000000000000000000000000) (2196006003457792593676496504153458683579/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0155.bracket2486 BracketBatch0155.bracket2487
  (641100600248887977705265934740818215981317/20000000000000000000000000000000000000000) (2196006003457792593676496504153458683579/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2486
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2487
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (320958052411107689578894451594988345290787/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (320958052411107689578894451594988345290787/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0388.rows BesselBatch0388.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (321777739263454546624023963660262087757809/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (321777739263454546624023963660262087757809/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (160683947918640559050729603813812608262149/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (160683947918640559050729603813812608262149/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0310.rows ScalarLogs0310.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0155.bracket2487 BracketBatch0155.bracket2488 (160683947918640559050729603813812608262149/5000000000000000000000000000000000000000) (4395704654469576001047008288122442967503/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0155.bracket2487 BracketBatch0155.bracket2488
  (160683947918640559050729603813812608262149/5000000000000000000000000000000000000000) (4395704654469576001047008288122442967503/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2487
