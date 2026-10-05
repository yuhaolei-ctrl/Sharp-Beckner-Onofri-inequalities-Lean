import BecknerOnofri.EntropyScalarCertificate.Bessel0185
import BecknerOnofri.EntropyScalarCertificate.Bessel0186
import BecknerOnofri.EntropyScalarCertificate.Bessel0581
import BecknerOnofri.EntropyScalarCertificate.Bessel0582
import BecknerOnofri.EntropyScalarCertificate.Brackets0074
import BecknerOnofri.EntropyScalarCertificate.Logs0148
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1184
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (455149625501555885342931607435941470027/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (455149625501555885342931607435941470027/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (9129278381073316476938676982789072438669/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9129278381073316476938676982789072438669/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (18232270891104434183797309131507901839209/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18232270891104434183797309131507901839209/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0074.bracket1184 BracketBatch0074.bracket1185 (18232270891104434183797309131507901839209/20000000000000000000000000000000000000000) (96848996932314056650106919384892473107/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0074.bracket1184 BracketBatch0074.bracket1185
  (18232270891104434183797309131507901839209/20000000000000000000000000000000000000000) (96848996932314056650106919384892473107/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1184
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1185
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (4564639190536658238469338491394536219333/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4564639190536658238469338491394536219333/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (2288919778267817357174488324698226985643/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2288919778267817357174488324698226985643/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (9142478747072292952818315140790990190619/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9142478747072292952818315140790990190619/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0074.bracket1185 BracketBatch0074.bracket1186 (9142478747072292952818315140790990190619/10000000000000000000000000000000000000000) (24382232490555821853874682171287563649/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0074.bracket1185 BracketBatch0074.bracket1186
  (9142478747072292952818315140790990190619/10000000000000000000000000000000000000000) (24382232490555821853874682171287563649/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1185
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1186
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (9155679113071269428697953298792907942569/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9155679113071269428697953298792907942569/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (1147774469947785147778948860206248595699/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1147774469947785147778948860206248595699/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (18337874872653550610929544180442896708161/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18337874872653550610929544180442896708161/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0074.bracket1186 BracketBatch0074.bracket1187 (18337874872653550610929544180442896708161/20000000000000000000000000000000000000000) (19642638324363574737536721608938607553/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0074.bracket1186 BracketBatch0074.bracket1187
  (18337874872653550610929544180442896708161/20000000000000000000000000000000000000000) (19642638324363574737536721608938607553/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1186
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1187
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (9182195759582281182231590881649988765589/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9182195759582281182231590881649988765589/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (2302207346878183840092131203215090569527/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2302207346878183840092131203215090569527/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (18391025147095016542600115694510351043697/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18391025147095016542600115694510351043697/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0074.bracket1187 BracketBatch0074.bracket1188 (18391025147095016542600115694510351043697/20000000000000000000000000000000000000000) (24725452990583112242435521586773933273/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0074.bracket1187 BracketBatch0074.bracket1188
  (18391025147095016542600115694510351043697/20000000000000000000000000000000000000000) (24725452990583112242435521586773933273/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1187
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1188
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (1841765877502547072073704962572072455621/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1841765877502547072073704962572072455621/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (1847116215466839298985808134344816713453/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1847116215466839298985808134344816713453/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (1844441046484693185529756548458444584537/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1844441046484693185529756548458444584537/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0074.bracket1188 BracketBatch0074.bracket1189 (1844441046484693185529756548458444584537/2000000000000000000000000000000000000000) (49797410667022233448536390889755064009/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0074.bracket1188 BracketBatch0074.bracket1189
  (1844441046484693185529756548458444584537/2000000000000000000000000000000000000000) (49797410667022233448536390889755064009/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1188
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1189
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (4617790538667098247464520335862041783631/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4617790538667098247464520335862041783631/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (9262451923303719038759975042623428006677/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9262451923303719038759975042623428006677/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (18498033000637915533689015714347511573939/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18498033000637915533689015714347511573939/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0074.bracket1189 BracketBatch0074.bracket1190 (18498033000637915533689015714347511573939/20000000000000000000000000000000000000000) (100292250390596609030712574640784567709/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0074.bracket1189 BracketBatch0074.bracket1190
  (18498033000637915533689015714347511573939/20000000000000000000000000000000000000000) (100292250390596609030712574640784567709/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1189
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1190
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0185.rows BesselBatch0185.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (4631225961651859519379987521311714003337/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4631225961651859519379987521311714003337/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (9289443033688458513126041368421591494637/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9289443033688458513126041368421591494637/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (18551894956992177551886016411045019501311/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18551894956992177551886016411045019501311/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0074.bracket1190 BracketBatch0074.bracket1191 (18551894956992177551886016411045019501311/20000000000000000000000000000000000000000) (201988260186792478811030722305843978263/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0074.bracket1190 BracketBatch0074.bracket1191
  (18551894956992177551886016411045019501311/20000000000000000000000000000000000000000) (201988260186792478811030722305843978263/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1190
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1191
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (4644721516844229256563020684210795747317/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4644721516844229256563020684210795747317/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (1863311106198936449412257456158072978351/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1863311106198936449412257456158072978351/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0581.rows BesselBatch0581.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (18605998564683140760187328649211956386389/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18605998564683140760187328649211956386389/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0148.rows ScalarLogs0148.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0074.bracket1191 BracketBatch0074.bracket1192 (18605998564683140760187328649211956386389/20000000000000000000000000000000000000000) (20340098343218691182548082229565646709/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0074.bracket1191 BracketBatch0074.bracket1192
  (18605998564683140760187328649211956386389/20000000000000000000000000000000000000000) (20340098343218691182548082229565646709/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1191
