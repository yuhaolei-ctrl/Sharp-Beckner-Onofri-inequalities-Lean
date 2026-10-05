module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0120
public import BecknerOnofri.EntropyScalarCertificate.Bessel0121
public import BecknerOnofri.EntropyScalarCertificate.Bessel0548
public import BecknerOnofri.EntropyScalarCertificate.Bessel0549
public import BecknerOnofri.EntropyScalarCertificate.Brackets0048
public import BecknerOnofri.EntropyScalarCertificate.Logs0096
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0768
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (1291225902652590866633498762775916081529/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1291225902652590866633498762775916081529/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (2593482542429991453585205435076438770333/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2593482542429991453585205435076438770333/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (5175934347735173186852202960628270933391/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5175934347735173186852202960628270933391/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0048.bracket0768 BracketBatch0048.bracket0769 (5175934347735173186852202960628270933391/20000000000000000000000000000000000000000) (3108822506770615754488023308281907797/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0048.bracket0768 BracketBatch0048.bracket0769
  (5175934347735173186852202960628270933391/20000000000000000000000000000000000000000) (3108822506770615754488023308281907797/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0768
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0769
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (259348254242999145358520543507643877033/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (259348254242999145358520543507643877033/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (260452231288286825959257143225092400597/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (260452231288286825959257143225092400597/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (51980048553128597131777768673273627763/200000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (51980048553128597131777768673273627763/200000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0048.bracket0769 BracketBatch0048.bracket0770 (51980048553128597131777768673273627763/200000000000000000000000000000000000000) (3159707248478135477975508853416623199/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0048.bracket0769 BracketBatch0048.bracket0770
  (51980048553128597131777768673273627763/200000000000000000000000000000000000000) (3159707248478135477975508853416623199/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0769
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0770
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (2604522312882868259592571432250924005967/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2604522312882868259592571432250924005967/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (2615571166382591216218849722753514730643/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2615571166382591216218849722753514730643/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (522009347926545947581142115500443873661/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (522009347926545947581142115500443873661/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0048.bracket0770 BracketBatch0048.bracket0771 (522009347926545947581142115500443873661/2000000000000000000000000000000000000000) (3211220448621600916579575837793630223/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0048.bracket0770 BracketBatch0048.bracket0771
  (522009347926545947581142115500443873661/2000000000000000000000000000000000000000) (3211220448621600916579575837793630223/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0770
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0771
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (32694639579782390202735621534418934133/125000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (32694639579782390202735621534418934133/125000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (525325830568359174163252998593540578191/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (525325830568359174163252998593540578191/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (1048440063844877417407022943144243524319/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1048440063844877417407022943144243524319/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0048.bracket0771 BracketBatch0048.bracket0772 (1048440063844877417407022943144243524319/4000000000000000000000000000000000000000) (3263367469370239055361842224619821127/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0048.bracket0771 BracketBatch0048.bracket0772
  (1048440063844877417407022943144243524319/4000000000000000000000000000000000000000) (3263367469370239055361842224619821127/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0771
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0772
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (328328644105224483852033124120962861369/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (328328644105224483852033124120962861369/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (659424080592106529135882117798598868819/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (659424080592106529135882117798598868819/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (1316081368802555496839948366040524591557/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1316081368802555496839948366040524591557/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0048.bracket0772 BracketBatch0048.bracket0773 (1316081368802555496839948366040524591557/5000000000000000000000000000000000000000) (331615370011658018787201421286556937/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0048.bracket0772 BracketBatch0048.bracket0773
  (1316081368802555496839948366040524591557/5000000000000000000000000000000000000000) (331615370011658018787201421286556937/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0772
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0773
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (2637696322368426116543528471194395475273/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2637696322368426116543528471194395475273/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (33109659065839960488877392762544845029/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (33109659065839960488877392762544845029/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (5286469047635622955653719892197983077593/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5286469047635622955653719892197983077593/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0048.bracket0773 BracketBatch0048.bracket0774 (5286469047635622955653719892197983077593/20000000000000000000000000000000000000000) (3369584557557670457089732698337651291/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0048.bracket0773 BracketBatch0048.bracket0774
  (5286469047635622955653719892197983077593/20000000000000000000000000000000000000000) (3369584557557670457089732698337651291/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0773
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0774
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0120.rows BesselBatch0120.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (2648772725267196839110191421003587602317/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2648772725267196839110191421003587602317/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (2659858412041067454206344435709966534199/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2659858412041067454206344435709966534199/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (1327157784327066073329133964178388534129/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1327157784327066073329133964178388534129/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0048.bracket0774 BracketBatch0048.bracket0775 (1327157784327066073329133964178388534129/5000000000000000000000000000000000000000) (3423665485776854884385347971913722861/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0048.bracket0774 BracketBatch0048.bracket0775
  (1327157784327066073329133964178388534129/5000000000000000000000000000000000000000) (3423665485776854884385347971913722861/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0774
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0775
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (664964603010266863551586108927491633549/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (664964603010266863551586108927491633549/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (1335476716696363222047777116472869750817/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1335476716696363222047777116472869750817/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (533081184543379389830189866865570603583/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (533081184543379389830189866865570603583/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0096.rows ScalarLogs0096.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0048.bracket0775 BracketBatch0048.bracket0776 (533081184543379389830189866865570603583/2000000000000000000000000000000000000000) (3478401956326134847666192180018035031/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0048.bracket0775 BracketBatch0048.bracket0776
  (533081184543379389830189866865570603583/2000000000000000000000000000000000000000) (3478401956326134847666192180018035031/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0775
