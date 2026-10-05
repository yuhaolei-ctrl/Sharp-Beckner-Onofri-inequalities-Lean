module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0061
public import BecknerOnofri.EntropyScalarCertificate.Bessel0062
public import BecknerOnofri.EntropyScalarCertificate.Bessel0519
public import BecknerOnofri.EntropyScalarCertificate.Bessel0520
public import BecknerOnofri.EntropyScalarCertificate.Brackets0024
public import BecknerOnofri.EntropyScalarCertificate.Brackets0025
public import BecknerOnofri.EntropyScalarCertificate.Logs0049
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0392
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (340365994870318289914997159515265687941/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (340365994870318289914997159515265687941/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (42610002275229632886382098825719698169/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (42610002275229632886382098825719698169/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (681246013072155353006053950121023273293/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (681246013072155353006053950121023273293/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0024.bracket0392 BracketBatch0024.bracket0393 (681246013072155353006053950121023273293/5000000000000000000000000000000000000000) (16217586819811827976748011250857377/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0024.bracket0392 BracketBatch0024.bracket0393
  (681246013072155353006053950121023273293/5000000000000000000000000000000000000000) (16217586819811827976748011250857377/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0392
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0393
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (272704014561469650472845432484606068281/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (272704014561469650472845432484606068281/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1365576336781891456602012277539243998081/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1365576336781891456602012277539243998081/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (1364548204794619854483119719981137169743/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1364548204794619854483119719981137169743/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0024.bracket0393 BracketBatch0024.bracket0394 (1364548204794619854483119719981137169743/10000000000000000000000000000000000000000) (261031819485838126552699556146503159/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0024.bracket0393 BracketBatch0024.bracket0394
  (1364548204794619854483119719981137169743/10000000000000000000000000000000000000000) (261031819485838126552699556146503159/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0393
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0394
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (682788168390945728301006138769621999039/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (682788168390945728301006138769621999039/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (68381638584189218088157384812333684689/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (68381638584189218088157384812333684689/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (1366604554232837909182579986892958845929/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1366604554232837909182579986892958845929/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0024.bracket0394 BracketBatch0024.bracket0395 (1366604554232837909182579986892958845929/10000000000000000000000000000000000000000) (131294601291269217361062936745086007/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0024.bracket0394 BracketBatch0024.bracket0395
  (1366604554232837909182579986892958845929/10000000000000000000000000000000000000000) (131294601291269217361062936745086007/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0394
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0395
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1367632771683784361763147696246673693777/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1367632771683784361763147696246673693777/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (171211172224003861282564288045703412537/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (171211172224003861282564288045703412537/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (2737322149475815252023662000612300994073/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2737322149475815252023662000612300994073/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0024.bracket0395 BracketBatch0024.bracket0396 (2737322149475815252023662000612300994073/20000000000000000000000000000000000000000) (132076779696882727585984370328040507/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0024.bracket0395 BracketBatch0024.bracket0396
  (2737322149475815252023662000612300994073/20000000000000000000000000000000000000000) (132076779696882727585984370328040507/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0395
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0396
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0061.rows BesselBatch0061.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (1369689377792030890260514304365627300293/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1369689377792030890260514304365627300293/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (171468269423219690372741501055103161993/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (171468269423219690372741501055103161993/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (2741435533177788413242446312806452596237/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2741435533177788413242446312806452596237/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0024.bracket0396 BracketBatch0024.bracket0397 (2741435533177788413242446312806452596237/20000000000000000000000000000000000000000) (132862455469784131736130624232933143/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0024.bracket0396 BracketBatch0024.bracket0397
  (2741435533177788413242446312806452596237/20000000000000000000000000000000000000000) (132862455469784131736130624232933143/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0396
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0397
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1371746155385757522981932008440825295941/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1371746155385757522981932008440825295941/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (686901552372106762478780877221241810777/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (686901552372106762478780877221241810777/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0519.rows BesselBatch0519.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (549109852025994209587898752576661783499/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (549109852025994209587898752576661783499/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0024.bracket0397 BracketBatch0024.bracket0398 (549109852025994209587898752576661783499/4000000000000000000000000000000000000000) (33412909784172558813593849360083723/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0024.bracket0397 BracketBatch0024.bracket0398
  (549109852025994209587898752576661783499/4000000000000000000000000000000000000000) (33412909784172558813593849360083723/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0397
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0398
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (1373803104744213524957561754442483621551/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1373803104744213524957561754442483621551/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (171982528268346396405413168949996347639/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (171982528268346396405413168949996347639/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (2749663330890984696200867106042454402663/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2749663330890984696200867106042454402663/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0024.bracket0398 BracketBatch0024.bracket0399 (2749663330890984696200867106042454402663/20000000000000000000000000000000000000000) (134444341241015492179552504973318579/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0024.bracket0398 BracketBatch0024.bracket0399
  (2749663330890984696200867106042454402663/20000000000000000000000000000000000000000) (134444341241015492179552504973318579/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0398
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0399
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1375860226146771171243305351599970781109/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1375860226146771171243305351599970781109/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (172239689984115746627582679931760162509/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (172239689984115746627582679931760162509/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (2753777746019697144263966791054052081181/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2753777746019697144263966791054052081181/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0049.rows ScalarLogs0049.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0024.bracket0399 BracketBatch0025.bracket0400 (2753777746019697144263966791054052081181/20000000000000000000000000000000000000000) (270481144685754791279506835427790679/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0024.bracket0399 BracketBatch0025.bracket0400
  (2753777746019697144263966791054052081181/20000000000000000000000000000000000000000) (270481144685754791279506835427790679/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0399
